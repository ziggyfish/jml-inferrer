package com.jml.inferrer.processor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.analysis.ClassFileSpecificationReader;
import com.jml.inferrer.evaluation.MetricsCollector;
import com.jml.inferrer.visitor.JMLInferenceVisitor;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Processes an entire Java codebase to infer and add JML specifications.
 */
public class CodebaseProcessor {

    private static final Logger logger = LoggerFactory.getLogger(CodebaseProcessor.class);
    private final JavaParser javaParser;
    private final MetricsCollector metricsCollector;
    private final boolean collectMetrics;

    public CodebaseProcessor() {
        this(true); // Enable metrics by default
    }

    public CodebaseProcessor(boolean collectMetrics) {
        ParserConfiguration parserConfig = new ParserConfiguration();
        parserConfig.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        this.javaParser = new JavaParser(parserConfig);
        this.collectMetrics = collectMetrics;
        this.metricsCollector = collectMetrics ? new MetricsCollector() : null;
    }

    /**
     * Processes all Java files in the given codebase path.
     * Uses two-pass analysis for interprocedural specification inference.
     * Also loads specifications from compiled class files if available.
     *
     * @param codebasePath Path to the root directory of the Java codebase
     * @return Number of files processed
     * @throws IOException If file reading fails
     */
    public int processCodebase(Path codebasePath) throws IOException {
        if (!Files.exists(codebasePath)) {
            throw new IOException("Path does not exist: " + codebasePath);
        }

        // Start metrics collection
        if (collectMetrics) {
            metricsCollector.startAnalysis();
        }

        // Collect all Java files first
        java.util.List<Path> javaFiles = new java.util.ArrayList<>();
        try (Stream<Path> paths = Files.walk(codebasePath)) {
            paths.filter(Files::isRegularFile)
                 .filter(path -> path.toString().endsWith(".java"))
                 .forEach(javaFiles::add);
        }

        logger.info("Found {} Java files. Starting two-pass analysis...", javaFiles.size());

        // Pre-pass: Load specifications from compiled class files if available
        JMLInferenceVisitor visitor = new JMLInferenceVisitor();
        loadExistingSpecificationsFromClassFiles(codebasePath, visitor);

        // First pass: Infer specifications and populate cache
        logger.info("Pass 1: Building specification cache...");
        java.util.Map<Path, CompilationUnit> compilationUnits = new java.util.HashMap<>();

        for (Path javaFile : javaFiles) {
            try {
                CompilationUnit cu = javaParser.parse(javaFile).getResult()
                    .orElseThrow(() -> new IOException("Failed to parse file: " + javaFile));
                compilationUnits.put(javaFile, cu);
                visitor.visit(cu, null);

                // Collect metrics after first pass
                if (collectMetrics) {
                    metricsCollector.recordFile();
                    collectMetricsFromCompilationUnit(cu);
                }
            } catch (Exception e) {
                logger.error("Error in first pass for file: {}", javaFile, e);
            }
        }

        // Second pass: Re-infer with interprocedural analysis
        logger.info("Pass 2: Applying interprocedural analysis...");
        visitor.enableSecondPass();

        AtomicInteger processedCount = new AtomicInteger(0);
        for (java.util.Map.Entry<Path, CompilationUnit> entry : compilationUnits.entrySet()) {
            try {
                Path javaFile = entry.getKey();
                CompilationUnit cu = entry.getValue();

                // Re-visit with cached specifications
                visitor.visit(cu, null);

                if (visitor.hasModifications()) {
                    Files.writeString(javaFile, cu.toString());
                    logger.info("Updated file with JML specifications: {}", javaFile);
                }

                processedCount.incrementAndGet();
            } catch (Exception e) {
                logger.error("Error in second pass for file: {}", entry.getKey(), e);
            }
        }

        // End metrics collection and generate report
        if (collectMetrics) {
            metricsCollector.endAnalysis();
            metricsCollector.printReport();

            // Export to JSON
            try {
                Path metricsPath = codebasePath.resolve("jml-inference-metrics.json");
                metricsCollector.exportJSON(metricsPath);
            } catch (IOException e) {
                logger.error("Failed to export metrics to JSON", e);
            }
        }

        return processedCount.get();
    }

    /**
     * Collect metrics from a compilation unit.
     */
    private void collectMetricsFromCompilationUnit(CompilationUnit cu) {
        // Count lines of code (approximate)
        int loc = cu.toString().split("\n").length;

        // Collect metrics for each class
        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(classDecl -> {
            metricsCollector.recordClass(classDecl, loc / cu.getTypes().size());

            // Collect metrics for each method
            classDecl.getMethods().forEach(method -> {
                metricsCollector.recordMethod(method);
            });
        });
    }

    /**
     * Get the metrics collector for external access.
     */
    public MetricsCollector getMetricsCollector() {
        return metricsCollector;
    }

    /**
     * Loads existing specifications from compiled class files.
     * Looks for target/classes, build/classes, or bin directories.
     *
     * @param codebasePath The codebase root path
     * @param visitor The visitor containing the specification cache
     */
    private void loadExistingSpecificationsFromClassFiles(Path codebasePath, JMLInferenceVisitor visitor) {
        ClassFileSpecificationReader reader = new ClassFileSpecificationReader();

        // Look for common build output directories
        java.util.List<String> possibleDirs = java.util.Arrays.asList(
            "target/classes",
            "build/classes/java/main",
            "build/classes",
            "bin",
            "out/production"
        );

        for (String dir : possibleDirs) {
            Path classesDir = codebasePath.resolve(dir);
            if (Files.exists(classesDir) && Files.isDirectory(classesDir)) {
                logger.info("Loading existing specifications from: {}", classesDir);
                reader.loadSpecificationsFromDirectory(classesDir, visitor.getCache());
            }
        }
    }
}
