package com.jml.inferrer.verification;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
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
import java.util.*;
import java.util.stream.Collectors;

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

    /** Set via -Djml.showInferred=true to print inferred JML for every test. */
    private static final boolean SHOW_INFERRED = Boolean.getBoolean("jml.showInferred");

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

        if (results.isEmpty()) {
            MethodVerificationResult result = buildFallbackResult(
                    invocation, parser, className, methodName);
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
        // Step 0: Strip any existing JML comments (//@ ... and /*@ ... @*/) so the
        // inference engine works with truly raw source and doesn't produce duplicate specs.
        String cleanSource = rawSource.replaceAll("(?m)^\\s*//@ [^\n]*\n?", "")
                                      .replaceAll("(?m)^\\s*/\\*@.*?@\\*/\\s*\n?", "");

        // Step 1: Parse and infer specifications
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        JavaParser javaParser = new JavaParser(config);

        var parseResult = javaParser.parse(cleanSource);
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

        // Step 4b: Run specification quality checks
        Optional<MethodDeclaration> method = cu.findAll(MethodDeclaration.class).stream()
                .filter(m -> m.getNameAsString().equals(methodName))
                .findFirst();
        if (method.isPresent()) {
            runSpecQualityChecks(method.get(), jmlSource, className, methodName);
        }

        // Log the inferred JML source for review (opt-in via -Djml.showInferred=true)
        if (SHOW_INFERRED) {
            System.out.println("=== Inferred JML: " + className + "." + methodName + " ===");
            System.out.println(jmlSource);
            System.out.println("=== End JML ===");
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
            MethodVerificationResult result = buildFallbackResult(
                    invocation, parser, className, methodName);
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
    // Fallback result builder
    // -------------------------------------------------------------------------

    /**
     * Builds a result when the parser returned no structured results.
     * Unlike the old logic that treated exit-code-0 as VERIFIED, this checks
     * the raw output for any failure indicators before declaring success.
     */
    private MethodVerificationResult buildFallbackResult(
            OpenJMLInvoker.InvocationResult invocation,
            OpenJMLOutputParser parser,
            String className, String methodName) {

        MethodVerificationResult result = new MethodVerificationResult(className, methodName, 0);
        String output = invocation.output();

        // Non-zero exit code is always a failure
        if (!invocation.isSuccess()) {
            result.setStatus(MethodVerificationResult.Status.FAILED);
            result.addErrorMessage("OpenJML exit code: " + invocation.exitCode() + "\n" + output);
            return result;
        }

        // Exit code 0 but output contains failure indicators — don't trust exit code
        if (parser.hasAnyFailureIndicator(output)) {
            result.setStatus(MethodVerificationResult.Status.FAILED);
            result.addErrorMessage("OpenJML exit code was 0 but output contains failure indicators:\n" + output);
            return result;
        }

        // Exit code 0, no failure indicators, output is non-empty — log for awareness
        if (output != null && !output.isBlank()) {
            logger.info("OpenJML produced output but parser found no results for {}.{}: {}",
                    className, methodName, output);
        }

        // Genuinely clean — verified
        result.setStatus(MethodVerificationResult.Status.VERIFIED);
        return result;
    }

    // -------------------------------------------------------------------------
    // Specification quality checks
    // -------------------------------------------------------------------------

    /**
     * Runs all spec quality checks on the inferred JML for the given method.
     * Each check collects failures; all are reported together at the end.
     */
    private void runSpecQualityChecks(MethodDeclaration method, String jmlSource,
                                       String className, String methodName) {
        List<String> failures = new ArrayList<>();

        checkEnsuresForNonVoid(method, jmlSource, failures);
        checkRequiresForDereferencedParams(method, jmlSource, failures);
        checkAssignableOrPure(method, jmlSource, failures);
        checkLoopInvariantsForLoops(method, jmlSource, failures);
        checkAssignableCoversFieldWrites(method, jmlSource, failures);
        checkRequiresForArrayIndexing(method, jmlSource, failures);
        checkContradictoryEnsures(jmlSource, failures);
        checkDuplicateSpecs(jmlSource, failures);
        checkPureMethodDoesNotWriteFields(method, jmlSource, failures);

        if (!failures.isEmpty()) {
            fail("Specification quality check(s) failed for " + className + "." + methodName + ":\n" +
                    failures.stream().collect(Collectors.joining("\n  - ", "  - ", "")) +
                    "\n\nInferred JML:\n" + jmlSource);
        }
    }

    /**
     * Non-void methods must have at least one ensures clause.
     */
    private void checkEnsuresForNonVoid(MethodDeclaration method, String jmlSource,
                                         List<String> failures) {
        if (method.getType().isVoidType()) return;

        boolean hasEnsures = jmlSource.lines().anyMatch(line ->
                line.stripLeading().startsWith("//@ ensures"));
        if (!hasEnsures) {
            failures.add("Non-void method (returns " + method.getType() +
                    ") has no ensures clause");
        }
    }

    /**
     * Parameters that are dereferenced (method calls, field access, array indexing)
     * must have a requires param != null precondition.
     */
    private void checkRequiresForDereferencedParams(MethodDeclaration method, String jmlSource,
                                                      List<String> failures) {
        if (method.getBody().isEmpty()) return;

        Set<String> refParams = new HashSet<>();
        for (Parameter param : method.getParameters()) {
            if (param.getType().isReferenceType()) {
                refParams.add(param.getNameAsString());
            }
        }
        if (refParams.isEmpty()) return;

        // Find which ref params are actually dereferenced in the method body
        Set<String> dereferencedParams = new HashSet<>();

        // Method calls on params: param.method()
        for (MethodCallExpr call : method.findAll(MethodCallExpr.class)) {
            call.getScope().ifPresent(scope -> {
                String scopeStr = scope.toString();
                if (refParams.contains(scopeStr)) {
                    dereferencedParams.add(scopeStr);
                }
            });
        }

        // Field access on params: param.field
        for (FieldAccessExpr fa : method.findAll(FieldAccessExpr.class)) {
            String scopeStr = fa.getScope().toString();
            if (refParams.contains(scopeStr)) {
                dereferencedParams.add(scopeStr);
            }
        }

        // Array indexing: param[i]
        for (ArrayAccessExpr aa : method.findAll(ArrayAccessExpr.class)) {
            String nameStr = aa.getName().toString();
            if (refParams.contains(nameStr)) {
                dereferencedParams.add(nameStr);
            }
        }

        // For-each over a param: for (X x : param)
        for (ForEachStmt forEach : method.findAll(ForEachStmt.class)) {
            String iterStr = forEach.getIterable().toString();
            if (refParams.contains(iterStr)) {
                dereferencedParams.add(iterStr);
            }
        }

        // Check each dereferenced param has a requires != null (or a guard clause that throws)
        for (String param : dereferencedParams) {
            boolean hasNullRequires = jmlSource.lines().anyMatch(line -> {
                String stripped = line.stripLeading();
                return stripped.startsWith("//@ requires") &&
                        stripped.contains(param) &&
                        stripped.contains("!= null");
            });

            // Also accept if there's a guard clause that throws on null
            // (the method will have a requires from the guard)
            if (!hasNullRequires) {
                // Check if the param is guarded by an if-throw null check in the source
                boolean hasGuardThrow = hasNullGuardThrow(method, param);
                if (hasGuardThrow) {
                    // Guard clause exists but no requires generated — still a problem
                    // unless the requires is implicit from the guard
                    hasNullRequires = jmlSource.lines().anyMatch(line -> {
                        String stripped = line.stripLeading();
                        return stripped.startsWith("//@ requires") &&
                                stripped.contains(param);
                    });
                }
            }

            if (!hasNullRequires) {
                failures.add("Parameter '" + param + "' (type " +
                        getParamType(method, param) + ") is dereferenced but has no " +
                        "requires " + param + " != null");
            }
        }
    }

    /**
     * Every method must have either a pure annotation or an assignable clause.
     */
    private void checkAssignableOrPure(MethodDeclaration method, String jmlSource,
                                        List<String> failures) {
        boolean hasPure = jmlSource.lines().anyMatch(line ->
                line.stripLeading().startsWith("/*@ pure"));
        boolean hasAssignable = jmlSource.lines().anyMatch(line ->
                line.stripLeading().startsWith("//@ assignable"));

        if (!hasPure && !hasAssignable) {
            failures.add("Method has neither @pure nor assignable clause (frame condition missing)");
        }
    }

    /**
     * Methods containing for/while/for-each loops must have at least one loop_invariant.
     */
    private void checkLoopInvariantsForLoops(MethodDeclaration method, String jmlSource,
                                               List<String> failures) {
        if (method.getBody().isEmpty()) return;

        boolean hasLoop = !method.findAll(ForStmt.class).isEmpty() ||
                !method.findAll(WhileStmt.class).isEmpty() ||
                !method.findAll(ForEachStmt.class).isEmpty();

        if (hasLoop) {
            boolean hasLoopInvariant = jmlSource.lines().anyMatch(line ->
                    line.stripLeading().startsWith("//@ loop_invariant"));
            if (!hasLoopInvariant) {
                failures.add("Method contains loop(s) but has no loop_invariant");
            }
        }
    }

    /**
     * If a method writes to instance fields, the assignable clause must mention those fields.
     */
    private void checkAssignableCoversFieldWrites(MethodDeclaration method, String jmlSource,
                                                    List<String> failures) {
        if (method.getBody().isEmpty()) return;

        // Collect fields written via this.field = ..., field = ..., this.field++, field++, etc.
        Set<String> writtenFields = new HashSet<>();

        for (AssignExpr assign : method.findAll(AssignExpr.class)) {
            Expression target = assign.getTarget();
            extractFieldName(target, method).ifPresent(writtenFields::add);
        }

        for (UnaryExpr unary : method.findAll(UnaryExpr.class)) {
            if (unary.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT) {
                extractFieldName(unary.getExpression(), method).ifPresent(writtenFields::add);
            }
        }

        if (writtenFields.isEmpty()) return;

        // Check pure — pure methods shouldn't write fields, but that's a different issue
        boolean hasPure = jmlSource.lines().anyMatch(line ->
                line.stripLeading().startsWith("/*@ pure"));
        if (hasPure) return;

        // Check assignable clause covers the written fields
        String assignableLine = jmlSource.lines()
                .filter(line -> line.stripLeading().startsWith("//@ assignable"))
                .findFirst().orElse("");

        if (assignableLine.isEmpty()) {
            // No assignable at all — already caught by checkAssignableOrPure
            return;
        }

        // Don't check if assignable is \everything
        if (assignableLine.contains("\\everything")) return;

        for (String field : writtenFields) {
            // Accept this.field or just field in the assignable clause
            if (!assignableLine.contains("this." + field) && !assignableLine.contains(field)) {
                failures.add("Field 'this." + field + "' is written but not in assignable clause: " +
                        assignableLine.strip());
            }
        }
    }

    /**
     * If a method accesses array elements by index, there should be a requires
     * for the index bounds or the array length.
     */
    private void checkRequiresForArrayIndexing(MethodDeclaration method, String jmlSource,
                                                 List<String> failures) {
        if (method.getBody().isEmpty()) return;

        // Find array access with parameter as index: arr[param]
        Set<String> paramNames = method.getParameters().stream()
                .map(Parameter::getNameAsString)
                .collect(Collectors.toSet());

        for (ArrayAccessExpr aa : method.findAll(ArrayAccessExpr.class)) {
            String indexStr = aa.getIndex().toString();
            // Only check direct parameter indexing like arr[index], not arr[i] in loops
            if (paramNames.contains(indexStr)) {
                boolean hasBoundsRequires = jmlSource.lines().anyMatch(line -> {
                    String stripped = line.stripLeading();
                    return stripped.startsWith("//@ requires") &&
                            stripped.contains(indexStr) &&
                            (stripped.contains(">=") || stripped.contains("<") ||
                                    stripped.contains("length"));
                });

                if (!hasBoundsRequires) {
                    failures.add("Array indexed by parameter '" + indexStr +
                            "' but no bounds precondition found");
                }
            }
        }
    }

    // -------------------------------------------------------------------------
    // Quality check helpers
    // -------------------------------------------------------------------------

    /**
     * Checks if the method has a guard clause that throws on null for the given param.
     * Pattern: if (param == null) throw ...;
     */
    private boolean hasNullGuardThrow(MethodDeclaration method, String paramName) {
        for (IfStmt ifStmt : method.findAll(IfStmt.class)) {
            Expression condition = ifStmt.getCondition();
            if (condition instanceof BinaryExpr bin) {
                if (bin.getOperator() == BinaryExpr.Operator.EQUALS) {
                    String left = bin.getLeft().toString();
                    String right = bin.getRight().toString();
                    if ((left.equals(paramName) && right.equals("null")) ||
                            (right.equals(paramName) && left.equals("null"))) {
                        // Check if the then branch throws
                        Statement thenStmt = ifStmt.getThenStmt();
                        if (containsThrow(thenStmt)) return true;
                    }
                }
            }
        }
        return false;
    }

    private boolean containsThrow(Statement stmt) {
        if (stmt instanceof ThrowStmt) return true;
        if (stmt instanceof BlockStmt block) {
            return block.getStatements().stream().anyMatch(s -> s instanceof ThrowStmt);
        }
        return false;
    }

    /**
     * Extracts a field name from an assignment target expression.
     * Returns empty if the target is a local variable or parameter.
     */
    private Optional<String> extractFieldName(Expression target, MethodDeclaration method) {
        if (target instanceof FieldAccessExpr fa) {
            if (fa.getScope().toString().equals("this")) {
                return Optional.of(fa.getNameAsString());
            }
        } else if (target instanceof NameExpr name) {
            String varName = name.getNameAsString();
            // Check it's not a parameter
            boolean isParam = method.getParameters().stream()
                    .anyMatch(p -> p.getNameAsString().equals(varName));
            if (isParam) return Optional.empty();
            // Check it's not a local variable declared in the method
            if (method.getBody().isPresent()) {
                boolean isLocal = method.findAll(com.github.javaparser.ast.expr.VariableDeclarationExpr.class)
                        .stream()
                        .flatMap(vde -> vde.getVariables().stream())
                        .anyMatch(v -> v.getNameAsString().equals(varName));
                if (isLocal) return Optional.empty();
            }
            // It's likely a field
            return Optional.of(varName);
        } else if (target instanceof ArrayAccessExpr aa) {
            // arr[i] = ... — check if arr is a field
            return extractFieldName(aa.getName(), method);
        }
        return Optional.empty();
    }

    private String getParamType(MethodDeclaration method, String paramName) {
        return method.getParameters().stream()
                .filter(p -> p.getNameAsString().equals(paramName))
                .map(p -> p.getType().asString())
                .findFirst().orElse("unknown");
    }

    /**
     * Detects contradictory unconditional ensures clauses.
     * E.g., "ensures this.priority == 3" and "ensures this.priority == 2" can't both be true.
     * Conditional ensures (containing "==>") are excluded since only one branch applies.
     */
    private void checkContradictoryEnsures(String jmlSource, List<String> failures) {
        // Pattern: //@ ensures <lhs> == <literal>;
        // Group by LHS, check if multiple different constant RHS exist
        java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                "^\\s*//@ ensures\\s+(.+?)\\s*==\\s*(-?\\d+|\"[^\"]*\"|true|false)\\s*;\\s*$");

        // Only consider unconditional ensures (no ==> in the line)
        Map<String, Set<String>> lhsToValues = new HashMap<>();

        jmlSource.lines().forEach(line -> {
            String stripped = line.stripLeading();
            if (!stripped.startsWith("//@ ensures")) return;
            if (stripped.contains("==>")) return; // conditional, skip

            java.util.regex.Matcher m = pattern.matcher(line);
            if (m.matches()) {
                String lhs = m.group(1).strip();
                String rhs = m.group(2).strip();
                lhsToValues.computeIfAbsent(lhs, k -> new HashSet<>()).add(rhs);
            }
        });

        for (Map.Entry<String, Set<String>> entry : lhsToValues.entrySet()) {
            if (entry.getValue().size() > 1) {
                failures.add("Contradictory unconditional ensures: '" + entry.getKey() +
                        "' is claimed to equal all of " + entry.getValue() +
                        " — these should be conditional (using ==>)");
            }
        }
    }

    /**
     * Detects exact duplicate specification lines (same requires/ensures/assignable repeated).
     */
    private void checkDuplicateSpecs(String jmlSource, List<String> failures) {
        Map<String, Integer> specCounts = new HashMap<>();
        jmlSource.lines().forEach(line -> {
            String stripped = line.stripLeading();
            if (stripped.startsWith("//@ requires") || stripped.startsWith("//@ ensures") ||
                    stripped.startsWith("//@ assignable") || stripped.startsWith("//@ loop_invariant")) {
                specCounts.merge(stripped, 1, Integer::sum);
            }
        });

        for (Map.Entry<String, Integer> entry : specCounts.entrySet()) {
            if (entry.getValue() > 1) {
                failures.add("Duplicate spec (" + entry.getValue() + "x): " + entry.getKey());
            }
        }
    }

    /**
     * A method marked pure must not write to instance fields.
     */
    private void checkPureMethodDoesNotWriteFields(MethodDeclaration method, String jmlSource,
                                                     List<String> failures) {
        boolean hasPure = jmlSource.lines().anyMatch(line ->
                line.stripLeading().startsWith("/*@ pure"));
        if (!hasPure) return;
        if (method.getBody().isEmpty()) return;

        Set<String> writtenFields = new HashSet<>();
        for (AssignExpr assign : method.findAll(AssignExpr.class)) {
            extractFieldName(assign.getTarget(), method).ifPresent(writtenFields::add);
        }
        for (UnaryExpr unary : method.findAll(UnaryExpr.class)) {
            if (unary.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT) {
                extractFieldName(unary.getExpression(), method).ifPresent(writtenFields::add);
            }
        }

        if (!writtenFields.isEmpty()) {
            failures.add("Method is marked @pure but writes to fields: " + writtenFields);
        }
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
