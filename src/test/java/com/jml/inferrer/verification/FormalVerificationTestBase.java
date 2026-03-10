package com.jml.inferrer.verification;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.analysis.MethodSpecificationInferrer;
import com.jml.inferrer.model.MethodSpecification;
import com.jml.inferrer.validation.*;
import com.jml.inferrer.visitor.JMLInferenceVisitor;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Base class for formal verification tests that invoke OpenJML theorem prover.
 *
 * Provides helpers for:
 * - Tier 1: Write JML comment syntax directly into source, invoke OpenJML
 * - Tier 2: Full pipeline (infer -> annotate -> convert -> verify)
 *
 * All tests skip gracefully when OpenJML is not installed.
 */
abstract class FormalVerificationTestBase {

    private static final Logger logger = LoggerFactory.getLogger(FormalVerificationTestBase.class);

    static boolean openjmlAvailable;
    static OpenJMLInvoker invoker;
    static Path tempDir;

    private static final int TIMEOUT_SECONDS = 30;

    @BeforeAll
    static void initOpenJML() throws IOException {
        tempDir = Files.createTempDirectory("jml-verification-tests");

        OpenJMLInstaller installer = new OpenJMLInstaller(Path.of(System.getProperty("user.dir")));
        Optional<Path> openjmlPath = installer.findOrInstall(false);

        openjmlAvailable = openjmlPath.isPresent();
        if (openjmlAvailable) {
            invoker = new OpenJMLInvoker(openjmlPath.get(), TIMEOUT_SECONDS);
            logger.info("OpenJML found at: {}", openjmlPath.get());
        } else {
            logger.warn("OpenJML not found -- formal verification tests will be skipped");
        }
    }

    @AfterAll
    static void cleanupTempDir() {
        if (tempDir != null) {
            try {
                Files.walk(tempDir)
                        .sorted(java.util.Comparator.reverseOrder())
                        .forEach(p -> {
                            try { Files.deleteIfExists(p); } catch (IOException ignored) {}
                        });
            } catch (IOException ignored) {}
        }
    }

    @BeforeEach
    void skipIfNoOpenJML() {
        assumeTrue(openjmlAvailable, "OpenJML not available -- skipping formal verification test");
    }

    // -------------------------------------------------------------------------
    // Tier 1: Direct JML comment syntax verification
    // -------------------------------------------------------------------------

    /**
     * Writes a complete Java source string (with embedded JML comments) to a temp file,
     * invokes OpenJML ESC, and returns the verification result for the named method.
     *
     * @param jmlSource   complete Java source with //@ JML comments already embedded
     * @param className   the class name (used for file naming and result matching)
     * @param methodName  the method to check in results
     * @return verification result for the specified method
     */
    protected MethodVerificationResult verifyMethod(String jmlSource, String className, String methodName) throws IOException {
        Path sourceFile = tempDir.resolve(className + ".java");
        Files.writeString(sourceFile, jmlSource);

        OpenJMLInvoker.InvocationResult invocation = invoker.verify(sourceFile, null);

        assertFalse(invocation.timedOut(), "OpenJML timed out verifying " + className + "." + methodName);

        // Parse the output
        OpenJMLOutputParser parser = new OpenJMLOutputParser();
        List<OpenJMLOutputParser.MethodInfo> methods = List.of(
                new OpenJMLOutputParser.MethodInfo(className, methodName, findMethodLine(jmlSource, methodName), List.of())
        );
        List<MethodVerificationResult> results = parser.parse(invocation.output(), className + ".java", methods);

        // If exit code 0 and no parsed results, treat as verified
        if (results.isEmpty()) {
            MethodVerificationResult result = new MethodVerificationResult(className, methodName, 0);
            if (invocation.isSuccess()) {
                result.setStatus(MethodVerificationResult.Status.VERIFIED);
            } else {
                result.setStatus(MethodVerificationResult.Status.FAILED);
                result.addErrorMessage("OpenJML exit code: " + invocation.exitCode() + "\n" + invocation.output());
            }
            return result;
        }

        return results.get(0);
    }

    /**
     * Overload for single-method classes where className matches the default "T".
     */
    protected MethodVerificationResult verifyMethod(String jmlSource, String methodName) throws IOException {
        return verifyMethod(jmlSource, extractClassName(jmlSource), methodName);
    }

    // -------------------------------------------------------------------------
    // Tier 2: Full pipeline verification
    // -------------------------------------------------------------------------

    /**
     * Exercises the full pipeline: parse raw source -> infer specs -> inject annotations ->
     * convert annotations to JML comments -> invoke OpenJML -> return result.
     *
     * @param rawSource   Java source WITHOUT any JML annotations or comments
     * @param className   the class name
     * @param methodName  the method to verify
     * @return verification result
     */
    protected MethodVerificationResult inferAndVerify(String rawSource, String className, String methodName) throws IOException {
        // Step 1: Parse and infer specifications
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        JavaParser javaParser = new JavaParser(config);

        var parseResult = javaParser.parse(rawSource);
        assertTrue(parseResult.isSuccessful(), "Failed to parse source: " + parseResult.getProblems());
        CompilationUnit cu = parseResult.getResult().orElseThrow();

        // Step 2: Run the inference visitor to add annotations
        JMLInferenceVisitor visitor = new JMLInferenceVisitor();
        visitor.visit(cu, null);

        // Step 3: Write the annotated source to a temp file
        String annotatedSource = cu.toString();
        Path annotatedFile = tempDir.resolve(className + "_annotated.java");
        Files.writeString(annotatedFile, annotatedSource);

        // Step 4: Convert annotations to JML comments
        AnnotationToJMLConverter converter = new AnnotationToJMLConverter();
        String jmlSource = converter.convert(annotatedFile);

        if (jmlSource == null) {
            // No annotations were inferred -- this is a test issue
            fail("No JML annotations were inferred for " + className + "." + methodName +
                    "\nAnnotated source:\n" + annotatedSource);
        }

        // Step 5: Write JML-commented source and verify
        Path jmlFile = tempDir.resolve(className + "_jml.java");
        Files.writeString(jmlFile, jmlSource);

        OpenJMLInvoker.InvocationResult invocation = invoker.verify(jmlFile, null);
        assertFalse(invocation.timedOut(), "OpenJML timed out on full pipeline for " + className + "." + methodName);

        OpenJMLOutputParser parser = new OpenJMLOutputParser();
        List<OpenJMLOutputParser.MethodInfo> methods = List.of(
                new OpenJMLOutputParser.MethodInfo(className, methodName, findMethodLine(jmlSource, methodName), List.of())
        );
        List<MethodVerificationResult> results = parser.parse(invocation.output(), className + "_jml.java", methods);

        if (results.isEmpty()) {
            MethodVerificationResult result = new MethodVerificationResult(className, methodName, 0);
            if (invocation.isSuccess()) {
                result.setStatus(MethodVerificationResult.Status.VERIFIED);
            } else {
                result.setStatus(MethodVerificationResult.Status.FAILED);
                result.addErrorMessage("OpenJML exit code: " + invocation.exitCode() + "\n" + invocation.output());
            }
            return result;
        }

        return results.get(0);
    }

    // -------------------------------------------------------------------------
    // Assertion helpers
    // -------------------------------------------------------------------------

    protected void assertVerified(MethodVerificationResult result) {
        assertEquals(MethodVerificationResult.Status.VERIFIED, result.getStatus(),
                () -> "Expected VERIFIED but got " + result.getStatus()
                        + " for " + result.getFullMethodName()
                        + ". Failed specs: " + result.getFailedSpecs()
                        + ". Errors: " + result.getErrorMessages());
    }

    protected void assertFailed(MethodVerificationResult result) {
        assertNotEquals(MethodVerificationResult.Status.VERIFIED, result.getStatus(),
                () -> "Expected verification to FAIL but got VERIFIED for " + result.getFullMethodName());
    }

    // -------------------------------------------------------------------------
    // Utility methods
    // -------------------------------------------------------------------------

    /**
     * Finds the approximate line number of a method declaration in source text.
     */
    private int findMethodLine(String source, String methodName) {
        String[] lines = source.split("\n");
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(methodName) && lines[i].contains("(")) {
                return i + 1;
            }
        }
        return 1;
    }

    /**
     * Extracts the class name from source by finding the first "class X" declaration.
     */
    private String extractClassName(String source) {
        java.util.regex.Matcher m = java.util.regex.Pattern.compile("class\\s+(\\w+)").matcher(source);
        if (m.find()) {
            return m.group(1);
        }
        return "T";
    }
}
