package com.jml.inferrer.validation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Stream;

/**
 * Top-level orchestrator for OpenJML validation.
 *
 * Pipeline:
 * 1. Find all .java files with JML annotations
 * 2. For each file: convert annotations to JML comments -> write temp file -> invoke OpenJML -> parse results
 * 3. Aggregate into ValidationReport
 * 4. Generate console + JSON reports
 * 5. Clean up temp files
 */
public class OpenJMLValidator {

    private static final Logger logger = LoggerFactory.getLogger(OpenJMLValidator.class);

    private static final int DEFAULT_TIMEOUT_SECONDS = 30;

    private final AnnotationToJMLConverter converter;
    private final OpenJMLOutputParser parser;
    private final ValidationReportGenerator reportGenerator;
    private final int timeoutSeconds;

    public OpenJMLValidator() {
        this(DEFAULT_TIMEOUT_SECONDS);
    }

    public OpenJMLValidator(int timeoutSeconds) {
        this.converter = new AnnotationToJMLConverter();
        this.parser = new OpenJMLOutputParser();
        this.reportGenerator = new ValidationReportGenerator();
        this.timeoutSeconds = timeoutSeconds;
    }

    /**
     * Validates all annotated Java files in the given codebase path.
     *
     * @param codebasePath the path to the annotated codebase
     * @param reportPath   the path for the JSON report output
     * @return the validation report
     */
    public ValidationReport validate(Path codebasePath, Path reportPath) throws IOException {
        long startTime = System.currentTimeMillis();

        logger.info("Starting OpenJML validation on: {}", codebasePath);

        // Find OpenJML
        OpenJMLInstaller installer = new OpenJMLInstaller(
                codebasePath.toAbsolutePath().getParent());
        Optional<Path> openjmlPath = installer.findOrInstall(true);

        if (openjmlPath.isEmpty()) {
            logger.error("OpenJML not available. Validation skipped.");
            logger.info("To install OpenJML: set OPENJML_HOME or place it in tools/openjml/");
            return createSkippedReport(codebasePath);
        }

        OpenJMLInvoker invoker = new OpenJMLInvoker(openjmlPath.get(), timeoutSeconds);
        ValidationReport report = new ValidationReport();

        // Find annotated files
        List<Path> annotatedFiles = findAnnotatedFiles(codebasePath);
        logger.info("Found {} files with JML annotations", annotatedFiles.size());

        // Create temp directory for converted files
        Path tempDir = Files.createTempDirectory("jml-validation-");

        try {
            for (Path sourceFile : annotatedFiles) {
                logger.info("Validating: {}", codebasePath.relativize(sourceFile));

                ValidationReport.FileValidationResult fileResult =
                        validateFile(sourceFile, codebasePath, tempDir, invoker);
                report.addFileResult(fileResult);
            }
        } finally {
            // Clean up temp directory
            cleanupTempDir(tempDir);
        }

        long totalTime = System.currentTimeMillis() - startTime;
        report.setTotalVerificationTimeMs(totalTime);

        // Generate reports
        reportGenerator.printReport(report);

        if (reportPath != null) {
            reportGenerator.exportJSON(report, reportPath);
        }

        logger.info("Validation complete. {} methods verified out of {} checked.",
                report.getVerifiedCount(), report.getTotalMethods());

        return report;
    }

    /**
     * Validates a single source file.
     */
    private ValidationReport.FileValidationResult validateFile(
            Path sourceFile, Path codebasePath, Path tempDir, OpenJMLInvoker invoker) {

        String relativePath = codebasePath.relativize(sourceFile).toString();
        ValidationReport.FileValidationResult fileResult =
                new ValidationReport.FileValidationResult(relativePath);

        try {
            // Convert annotations to JML comments
            String convertedSource = converter.convert(sourceFile);

            if (convertedSource == null) {
                logger.debug("No JML annotations to convert in: {}", relativePath);
                return fileResult;
            }

            // Write converted file to temp directory (preserving relative path)
            Path tempFile = tempDir.resolve(sourceFile.getFileName());
            Files.writeString(tempFile, convertedSource);

            // Extract method info for matching results
            List<OpenJMLOutputParser.MethodInfo> methods = extractMethodInfo(sourceFile);

            if (methods.isEmpty()) {
                logger.debug("No methods with specs found in: {}", relativePath);
                return fileResult;
            }

            // Invoke OpenJML
            OpenJMLInvoker.InvocationResult invocationResult =
                    invoker.verify(tempFile, tempDir);

            // Parse results
            List<MethodVerificationResult> methodResults;

            if (invocationResult.timedOut()) {
                // Mark all methods as timed out
                methodResults = new ArrayList<>();
                for (OpenJMLOutputParser.MethodInfo m : methods) {
                    MethodVerificationResult result = new MethodVerificationResult(
                            m.className(), m.methodName(), m.lineNumber());
                    result.setStatus(MethodVerificationResult.Status.TIMEOUT);
                    result.setVerificationTimeMs(invocationResult.durationMs());
                    methodResults.add(result);
                }
            } else {
                methodResults = parser.parse(
                        invocationResult.output(),
                        sourceFile.getFileName().toString(),
                        methods);

                // Set timing on all results
                long perMethodTime = methods.isEmpty() ? 0
                        : invocationResult.durationMs() / methods.size();
                for (MethodVerificationResult result : methodResults) {
                    result.setVerificationTimeMs(perMethodTime);
                }
            }

            methodResults.forEach(fileResult::addMethodResult);

        } catch (Exception e) {
            logger.error("Error validating {}: {}", relativePath, e.getMessage());
            // Add an error result for the file
            MethodVerificationResult errorResult = new MethodVerificationResult(
                    relativePath, "<file>", 0);
            errorResult.setStatus(MethodVerificationResult.Status.ERROR);
            errorResult.addErrorMessage(e.getMessage());
            fileResult.addMethodResult(errorResult);
        }

        return fileResult;
    }

    /**
     * Finds all .java files that contain JML annotations.
     */
    private List<Path> findAnnotatedFiles(Path codebasePath) throws IOException {
        List<Path> result = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(codebasePath)) {
            walk.filter(p -> p.toString().endsWith(".java"))
                    .filter(p -> !p.toString().contains("test"))
                    .forEach(p -> {
                        try {
                            if (converter.hasJMLAnnotations(p)) {
                                result.add(p);
                            }
                        } catch (IOException e) {
                            logger.warn("Could not read {}: {}", p, e.getMessage());
                        }
                    });
        }
        return result;
    }

    /**
     * Extracts method information from a source file for result matching.
     */
    private List<OpenJMLOutputParser.MethodInfo> extractMethodInfo(Path sourceFile) throws IOException {
        List<OpenJMLOutputParser.MethodInfo> methods = new ArrayList<>();

        String source = Files.readString(sourceFile);
        JavaParser javaParser = new JavaParser(
                new ParserConfiguration()
                        .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21));

        var parseResult = javaParser.parse(source);
        if (!parseResult.isSuccessful() || parseResult.getResult().isEmpty()) {
            return methods;
        }

        CompilationUnit cu = parseResult.getResult().get();

        for (MethodDeclaration method : cu.findAll(MethodDeclaration.class)) {
            List<String> specs = new ArrayList<>();
            boolean hasSpecs = false;

            for (AnnotationExpr ann : method.getAnnotations()) {
                String name = getSimpleName(ann.getNameAsString());
                if (Set.of("Requires", "Ensures", "LoopInvariant", "Signals", "Assignable")
                        .contains(name)) {
                    hasSpecs = true;
                    String value = extractAnnotationValue(ann);
                    if (value != null) {
                        String jmlType = switch (name) {
                            case "Requires" -> "requires " + value;
                            case "Ensures" -> "ensures " + value;
                            case "LoopInvariant" -> "loop_invariant " + value;
                            case "Signals" -> "signals " + value;
                            case "Assignable" -> "assignable " + value;
                            default -> value;
                        };
                        specs.add(jmlType);
                    }
                }
            }

            if (hasSpecs) {
                // Find enclosing class name
                String className = method.findAncestor(ClassOrInterfaceDeclaration.class)
                        .map(ClassOrInterfaceDeclaration::getNameAsString)
                        .orElse("Unknown");

                int lineNumber = method.getBegin()
                        .map(pos -> pos.line)
                        .orElse(0);

                methods.add(new OpenJMLOutputParser.MethodInfo(
                        className, method.getNameAsString(), lineNumber, specs));
            }
        }

        return methods;
    }

    private String getSimpleName(String name) {
        int lastDot = name.lastIndexOf('.');
        return lastDot >= 0 ? name.substring(lastDot + 1) : name;
    }

    private String extractAnnotationValue(AnnotationExpr ann) {
        if (ann.isSingleMemberAnnotationExpr()) {
            String value = ann.asSingleMemberAnnotationExpr().getMemberValue().toString();
            if (value.startsWith("\"") && value.endsWith("\"")) {
                value = value.substring(1, value.length() - 1);
            }
            return value;
        }
        return null;
    }

    /**
     * Creates a report where all methods are marked as SKIPPED
     * (used when OpenJML is not available).
     */
    private ValidationReport createSkippedReport(Path codebasePath) throws IOException {
        ValidationReport report = new ValidationReport();
        List<Path> files = findAnnotatedFiles(codebasePath);

        for (Path file : files) {
            String relativePath = codebasePath.relativize(file).toString();
            ValidationReport.FileValidationResult fileResult =
                    new ValidationReport.FileValidationResult(relativePath);

            List<OpenJMLOutputParser.MethodInfo> methods = extractMethodInfo(file);
            for (OpenJMLOutputParser.MethodInfo m : methods) {
                MethodVerificationResult result = new MethodVerificationResult(
                        m.className(), m.methodName(), m.lineNumber());
                result.setStatus(MethodVerificationResult.Status.SKIPPED);
                result.addErrorMessage("OpenJML not available");
                fileResult.addMethodResult(result);
            }
            report.addFileResult(fileResult);
        }

        reportGenerator.printReport(report);
        return report;
    }

    /**
     * Cleans up the temporary directory.
     */
    private void cleanupTempDir(Path tempDir) {
        try (Stream<Path> walk = Files.walk(tempDir)) {
            walk.sorted(Comparator.reverseOrder())
                    .forEach(p -> {
                        try {
                            Files.delete(p);
                        } catch (IOException e) {
                            logger.debug("Could not delete temp file: {}", p);
                        }
                    });
        } catch (IOException e) {
            logger.debug("Could not clean up temp directory: {}", tempDir);
        }
    }
}
