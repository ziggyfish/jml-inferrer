package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;

import java.util.*;

/**
 * Analyzes numeric/conditional return values for postcondition inference.
 */
class ReturnValueAnalyzer {

    void analyzeNumericReturnBounds(MethodDeclaration methodDecl, Set<String> postconditions,
                                     ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;

        if (returnStmts.isEmpty()) {
            return;
        }

        // Track minimum value across all returns
        boolean allReturnsPositive = true;
        boolean allReturnsNonNegative = true;
        boolean allReturnsGreaterThanOne = true;

        for (ReturnStmt returnStmt : returnStmts) {
            if (returnStmt.getExpression().isEmpty()) {
                allReturnsNonNegative = false;
                allReturnsPositive = false;
                allReturnsGreaterThanOne = false;
                continue;
            }

            Expression expr = returnStmt.getExpression().get();

            // Check for literal values
            if (expr instanceof IntegerLiteralExpr) {
                int value = ((IntegerLiteralExpr) expr).asInt();
                if (value < 0) allReturnsNonNegative = false;
                if (value <= 0) allReturnsPositive = false;
                if (value <= 1) allReturnsGreaterThanOne = false;
            } else if (expr instanceof DoubleLiteralExpr) {
                double value = ((DoubleLiteralExpr) expr).asDouble();
                if (value < 0) allReturnsNonNegative = false;
                if (value <= 0) allReturnsPositive = false;
                if (value <= 1) allReturnsGreaterThanOne = false;
            } else if (expr instanceof MethodCallExpr) {
                // Check for operations that guarantee non-negative results
                MethodCallExpr call = (MethodCallExpr) expr;
                String methodName = call.getNameAsString();
                if (methodName.equals("length") || methodName.equals("size") || methodName.equals("count")) {
                    // These genuinely guarantee >= 0
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                } else if (methodName.equals("abs") && AnalysisUtils.isFloatingPointReturn(methodDecl)) {
                    // abs() only guarantees >= 0 for floating-point types;
                    // Math.abs(Integer.MIN_VALUE) returns Integer.MIN_VALUE (negative)
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                } else {
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                }
            } else if (expr instanceof BinaryExpr) {
                BinaryExpr binExpr = (BinaryExpr) expr;
                if (binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY && AnalysisUtils.isSelfMultiplication(binExpr)
                        && AnalysisUtils.isFloatingPointReturn(methodDecl)) {
                    // x * x is non-negative only for floating-point types;
                    // int/long can overflow to negative values
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                } else if (binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY &&
                           involvesRecursiveCall(binExpr, methodDecl)) {
                    // Recursive multiplication (e.g., n * factorial(n-1)):
                    // assume the recursive call preserves bounds properties
                } else if (binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                } else if (binExpr.getOperator() == BinaryExpr.Operator.PLUS &&
                           bothOperandsSyntacticallyNonNegative(binExpr, methodDecl)) {
                    // Recursive addition (e.g., fib(n-1) + fib(n-2)) — BOTH operands
                    // must preserve non-negativity. `arr[index] + recur(...)` doesn't
                    // qualify: arr[index] has unknown sign, so the sum can be negative
                    // (and overflow compounds with int arithmetic).
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                } else {
                    // Other operators (DIVIDE, PLUS, MINUS, etc.) — can't guarantee bounds
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                }
            } else if (expr instanceof NameExpr) {
                String name = ((NameExpr) expr).getNameAsString();
                boolean isParam = methodDecl.getParameters().stream()
                    .anyMatch(p -> p.getNameAsString().equals(name));
                if (!isParam) {
                    Expression resolved = resolveLocalVariable(methodDecl, name);
                    if (resolved != null && AnalysisUtils.isSelfMultiplication(resolved)
                            && AnalysisUtils.isFloatingPointReturn(methodDecl)) {
                        // resolved to x * x → non-negative only for floating-point types
                        allReturnsPositive = false;
                        allReturnsGreaterThanOne = false;
                    } else {
                        allReturnsNonNegative = false;
                        allReturnsPositive = false;
                        allReturnsGreaterThanOne = false;
                    }
                } else {
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                }
            } else if (!expr.isLiteralExpr()) {
                allReturnsNonNegative = false;
                allReturnsPositive = false;
                allReturnsGreaterThanOne = false;
            }
        }

        if (allReturnsGreaterThanOne && !postconditions.contains("\\result >= 0")) {
            postconditions.add("\\result >= 1");
        } else if (allReturnsPositive) {
            postconditions.add("\\result > 0");
        } else if (allReturnsNonNegative && !postconditions.contains("\\result >= 1")
                && !postconditions.contains("\\result > 0")) {
            postconditions.add("\\result >= 0");
        }
    }

    void analyzeReturnRelationToParameters(MethodDeclaration methodDecl, Set<String> postconditions,
                                             ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;

        // Count distinct return expressions that are parameters
        Set<String> returnedParams = new LinkedHashSet<>();
        for (ReturnStmt rs : returnStmts) {
            rs.getExpression().ifPresent(e -> {
                if (e instanceof NameExpr && methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(e.toString()))) {
                    returnedParams.add(e.toString());
                }
            });
        }

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                // Check for direct parameter return
                if (expr instanceof NameExpr) {
                    String exprName = expr.toString();
                    if (methodDecl.getParameters().stream()
                            .anyMatch(p -> p.getNameAsString().equals(exprName))) {
                        if (returnedParams.size() <= 1 && returnStmts.size() == 1
                                && !isParameterModified(methodDecl, exprName)) {
                            // `\result == a` refers to the entry-time value of a in JML.
                            // If the body mutates a (e.g., GCDE2E's loop updates a),
                            // the returned value is post-state, not entry-state, so
                            // the postcondition is unsound.
                            postconditions.add("\\result == " + exprName);
                        }
                    } else {
                        // Not a parameter — resolve local variable and analyze
                        Expression resolved = resolveLocalVariable(methodDecl, exprName);
                        if (resolved instanceof BinaryExpr) {
                            analyzeResolvedBinaryExprForParams((BinaryExpr) resolved, methodDecl, postconditions);
                        }
                    }
                }

                // Check for arithmetic operations with parameters
                Expression effective = expr;
                if (expr instanceof NameExpr) {
                    String name = ((NameExpr) expr).getNameAsString();
                    boolean isParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(name));
                    if (!isParam) {
                        Expression resolved = resolveLocalVariable(methodDecl, name);
                        if (resolved != null) {
                            effective = resolved;
                        }
                    }
                }
                if (effective instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) effective;
                    String left = binExpr.getLeft().toString();
                    String right = binExpr.getRight().toString();

                    boolean leftIsParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(left));
                    boolean rightIsParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(right));

                    if (leftIsParam && rightIsParam) {
                        if (returnStmts.size() == 1) {
                            switch (binExpr.getOperator()) {
                                case PLUS:
                                    postconditions.add("\\result == " + left + " + " + right);
                                    break;
                                case MINUS:
                                    postconditions.add("\\result == " + left + " - " + right);
                                    break;
                                case MULTIPLY:
                                    postconditions.add("\\result == " + left + " * " + right);
                                    break;
                                case DIVIDE:
                                    postconditions.add("\\result == " + left + " / " + right);
                                    break;
                            }
                        }
                    } else if (leftIsParam) {
                        switch (binExpr.getOperator()) {
                            case PLUS:
                                if (isPositiveLiteral(binExpr.getRight())) {
                                    postconditions.add("\\result > " + left);
                                }
                                break;
                            case MINUS:
                                if (isPositiveLiteral(binExpr.getRight())) {
                                    postconditions.add("\\result < " + left);
                                }
                                break;
                        }
                    } else if (rightIsParam) {
                        switch (binExpr.getOperator()) {
                            case PLUS:
                                if (isPositiveLiteral(binExpr.getLeft())) {
                                    postconditions.add("\\result > " + right);
                                }
                                break;
                        }
                    }
                }

                // Check for method calls on parameters
                if (expr instanceof MethodCallExpr) {
                    MethodCallExpr call = (MethodCallExpr) expr;
                    call.getScope().ifPresent(scope -> {
                        if (methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(scope.toString()))) {
                            String methodName = call.getNameAsString();
                            if (methodName.equals("length") || methodName.equals("size")) {
                                postconditions.add("\\result >= 0");
                            }
                        }
                    });
                }
            });
        }
    }

    void analyzeResolvedBinaryExprForParams(BinaryExpr binExpr, MethodDeclaration methodDecl, Set<String> postconditions) {
        String left = binExpr.getLeft().toString();
        String right = binExpr.getRight().toString();

        boolean leftIsParam = methodDecl.getParameters().stream()
            .anyMatch(p -> p.getNameAsString().equals(left));
        boolean rightIsParam = methodDecl.getParameters().stream()
            .anyMatch(p -> p.getNameAsString().equals(right));

        if (leftIsParam && rightIsParam) {
            switch (binExpr.getOperator()) {
                case PLUS:
                    postconditions.add("\\result == " + left + " + " + right);
                    break;
                case MINUS:
                    postconditions.add("\\result == " + left + " - " + right);
                    break;
                case MULTIPLY:
                    postconditions.add("\\result == " + left + " * " + right);
                    break;
                case DIVIDE:
                    postconditions.add("\\result == " + left + " / " + right);
                    break;
            }
        } else if (leftIsParam) {
            switch (binExpr.getOperator()) {
                case PLUS:
                    if (isPositiveLiteral(binExpr.getRight())) {
                        postconditions.add("\\result > " + left);
                    }
                    break;
                case MINUS:
                    if (isPositiveLiteral(binExpr.getRight())) {
                        postconditions.add("\\result < " + left);
                    }
                    break;
            }
        } else if (rightIsParam) {
            switch (binExpr.getOperator()) {
                case PLUS:
                    if (isPositiveLiteral(binExpr.getLeft())) {
                        postconditions.add("\\result > " + right);
                    }
                    break;
            }
        }
    }

    Expression resolveLocalVariable(MethodDeclaration methodDecl, String varName) {
        if (methodDecl.getBody().isEmpty()) {
            return null;
        }
        Expression resolved = null;
        for (com.github.javaparser.ast.Node stmt : methodDecl.getBody().get().getStatements()) {
            // Variable declaration: int b = expr;
            if (stmt instanceof ExpressionStmt) {
                Expression inner = ((ExpressionStmt) stmt).getExpression();
                if (inner instanceof VariableDeclarationExpr) {
                    for (com.github.javaparser.ast.body.VariableDeclarator vd :
                            ((VariableDeclarationExpr) inner).getVariables()) {
                        if (vd.getNameAsString().equals(varName) && vd.getInitializer().isPresent()) {
                            resolved = vd.getInitializer().get();
                        }
                    }
                }
                // Assignment: b = expr;
                if (inner instanceof AssignExpr) {
                    AssignExpr assign = (AssignExpr) inner;
                    if (assign.getTarget() instanceof NameExpr &&
                        ((NameExpr) assign.getTarget()).getNameAsString().equals(varName) &&
                        assign.getOperator() == AssignExpr.Operator.ASSIGN) {
                        resolved = assign.getValue();
                    }
                }
            }
        }
        return resolved;
    }

    /**
     * Recognises the simple loop-accumulator return pattern and emits a non-negativity
     * postcondition when sound:
     *   {@code int x = 0; for(...) { x += positiveLiteral; } return x;} → {@code \result >= 0}
     *   {@code int x = 0; for(...) { x++; } return x;}                  → {@code \result >= 0}
     *
     * <p>Soundness gate: the accumulator must be a local var that is (a) declared with a
     * non-negative integer-literal initialiser, (b) modified ONLY inside loops, and ONLY
     * by {@code ++} or {@code += positiveIntegerLiteral}. Any other write (assignment,
     * subtract, multiply, etc.) disqualifies the variable. We do NOT allow non-literal
     * RHS — those introduce overflow risk that JML would have to account for.
     */
    void analyzeLoopAccumulatorReturn(MethodDeclaration methodDecl, Set<String> postconditions) {
        if (methodDecl.getBody().isEmpty()) return;
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);
        if (returnStmts.isEmpty()) return;

        // Multi-return guard-then-compute shape: every "non-final" return must be a
        // non-negative integer literal inside an if-guard at the top of the method
        // (these are early-exit guards), and the LAST return must be the loop
        // accumulator variable. Drives GuardEarlyReturnThenCompute.sumOrZero where
        // `if (arr.length == 0) return 0;` precedes `return sum;`.
        ReturnStmt rs = returnStmts.get(returnStmts.size() - 1);
        if (returnStmts.size() > 1) {
            for (int i = 0; i < returnStmts.size() - 1; i++) {
                ReturnStmt early = returnStmts.get(i);
                if (early.getExpression().isEmpty()) return;
                Expression earlyExpr = early.getExpression().get();
                if (!(earlyExpr instanceof IntegerLiteralExpr lit)
                        || lit.asInt() < 0) return;
            }
        }
        if (rs.getExpression().isEmpty()) return;
        if (!(rs.getExpression().get() instanceof NameExpr returnName)) return;
        String varName = returnName.getNameAsString();

        boolean isParam = methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(varName));
        if (isParam) return;
        if (AnalysisUtils.isFieldReference(methodDecl, varName)) return;

        // Find the variable's declaration & initial value
        Expression init = null;
        for (com.github.javaparser.ast.body.VariableDeclarator vd
                : methodDecl.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
            if (vd.getNameAsString().equals(varName) && vd.getInitializer().isPresent()) {
                init = vd.getInitializer().get();
                break;
            }
        }
        if (init == null) return;
        boolean initNonNeg, initPositive;
        if (init.isIntegerLiteralExpr()) {
            int v = init.asIntegerLiteralExpr().asInt();
            initNonNeg = v >= 0;
            initPositive = v > 0;
        } else if (init.isLongLiteralExpr()) {
            try {
                String s = init.asLongLiteralExpr().getValue().replaceAll("[Ll_]", "");
                long v = Long.parseLong(s);
                initNonNeg = v >= 0;
                initPositive = v > 0;
            } catch (NumberFormatException ex) { return; }
        } else {
            return;
        }
        if (!initNonNeg) return;

        // Verify all writes to varName are inside a loop AND of monotonic-non-negative form
        boolean anyLoopWrite = false;
        for (AssignExpr a : methodDecl.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) continue;
            if (!PreconditionAnalyzer.isInsideLoop(a)) return; // outside-loop write — bail
            if (a.getOperator() != AssignExpr.Operator.PLUS) return; // only += allowed
            Expression rhs = a.getValue();
            if (!isKnownNonNegativeRhs(rhs)) return;
            anyLoopWrite = true;
        }
        for (UnaryExpr u : methodDecl.findAll(UnaryExpr.class)) {
            if (!(u.getExpression() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) continue;
            if (!PreconditionAnalyzer.isInsideLoop(u)) return;
            if (u.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && u.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) return;
            anyLoopWrite = true;
        }
        if (!anyLoopWrite) return;

        if (initPositive && !postconditions.contains("\\result >= 0")) {
            postconditions.add("\\result > 0");
        } else if (!postconditions.contains("\\result > 0")) {
            postconditions.add("\\result >= 0");
        }
    }

    /**
     * Mirror of {@link LoopInvariantAnalyzer}'s monotonic-counter RHS gate: accepts a
     * non-negative integer literal or a bit-mask {@code <expr> & <non-negative-literal>}.
     * The mask case bounds the result into {@code [0, mask]} which is always non-negative,
     * letting popcount-style accumulators like {@code count += v & 1} qualify.
     */
    private boolean isKnownNonNegativeRhs(Expression rhs) {
        if (rhs.isIntegerLiteralExpr() && rhs.asIntegerLiteralExpr().asInt() >= 0) return true;
        if (rhs instanceof BinaryExpr be && be.getOperator() == BinaryExpr.Operator.BINARY_AND) {
            return isNonNegativeIntegerLiteral(be.getLeft()) || isNonNegativeIntegerLiteral(be.getRight());
        }
        return false;
    }

    private boolean isNonNegativeIntegerLiteral(Expression e) {
        return e.isIntegerLiteralExpr() && e.asIntegerLiteralExpr().asInt() >= 0;
    }

    void analyzeExactReturnExpression(MethodDeclaration methodDecl, Set<String> postconditions,
                                      SymbolicExecutor symbolicExecutor) {
        if (methodDecl.getBody().isEmpty()) return;

        Set<String> paramNames = new LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            paramNames.add(p.getNameAsString());
        }

        Map<String, String> env = new LinkedHashMap<>();
        Map<String, List<SymbolicExecutor.SymbolicReturn>> conditionalAssignments = new LinkedHashMap<>();
        List<SymbolicExecutor.SymbolicReturn> results = new ArrayList<>();

        symbolicExecutor.walkStatements(methodDecl.getBody().get().getStatements(), env,
                conditionalAssignments, null, paramNames, results, 0);

        if (results.isEmpty()) return;

        // When the method returns String, any `\result == expr` is reference equality
        // in JML — wrong for string-concat results (`a + b` produces a fresh object).
        // Force `.equals()` in that case.
        boolean isStringReturn = "String".equals(methodDecl.getType().asString());

        // For sequenced reads (e.g. CircularBuffer2.dequeue: `int v = buffer[head]; head = ...; return v;`),
        // the resolvedExpr captures the value at the time of the assignment to the local —
        // but JML interprets bare field references in a postcondition as POST-STATE. Wrap
        // any field reference whose field is mutated AFTER the resolvedExpr was captured
        // with `\old(...)` so the postcondition correctly refers to the captured value.
        //
        // CRITICAL: this wrap MUST NOT fire when the return expression is direct
        // (i.e. the source `return data[top]` after `top--`). In the direct case the
        // resolvedExpr equals the originalExpr (no env substitution happened), and JML
        // post-state semantics already gives the right value. The wrapper would
        // incorrectly produce `\old(this.top)` when the source-level `top` was meant.
        // The `wrapIfSubstituted` helper consults SymbolicReturn.originalExpr as the
        // "did substitution happen?" flag.
        Set<String> mutatedFields = collectMutatedFieldNames(methodDecl);

        // Check if all results resolve to the same expression — emit single unconditional spec
        String firstExpr = wrapIfSubstituted(results.get(0), mutatedFields, methodDecl);
        boolean allSame = results.stream().allMatch(r ->
                wrapIfSubstituted(r, mutatedFields, methodDecl).equals(firstExpr));

        if (allSame && results.size() > 1) {
            // All paths return the same expression — treat as unconditional
            if (AnalysisUtils.isTrivialResult(firstExpr)) return;
            if (firstExpr.length() > 100) return;
            if (!symbolicExecutor.isMethodScopeSafe(firstExpr, methodDecl, paramNames)) return;
            postconditions.add(AnalysisUtils.buildResultEquality(firstExpr, isStringReturn));
            return;
        }

        // Single return path with a path condition: the path condition just describes which
        // input states reach the return (other paths throw). The ensures
        // \result == resolvedExpr holds unconditionally for any normal return — emit it
        // without the guard. This recovers ensures for guard-then-compute methods like
        // safeAdd, where conditions reference local vars and would otherwise be dropped.
        if (results.size() == 1 && results.get(0).pathCondition != null) {
            SymbolicExecutor.SymbolicReturn sr = results.get(0);
            String wrappedExpr = wrapIfSubstituted(sr, mutatedFields, methodDecl);
            if (!AnalysisUtils.isTrivialResult(wrappedExpr)
                    && wrappedExpr.length() <= 100
                    && symbolicExecutor.isMethodScopeSafe(wrappedExpr, methodDecl, paramNames)) {
                postconditions.add(AnalysisUtils.buildResultEquality(wrappedExpr, isStringReturn));
                return;
            }
        }

        // If any loop in the method contains a return, the symbolic executor walks
        // PAST the loop to statements that follow without accounting for whether
        // the loop returned early. That makes the path condition of any post-loop
        // return strictly weaker than the truth (it's missing the "loop didn't
        // return" clause). Emitting `cond ==> \result == X` in that setting is
        // unsound — the OR-form postconditions from LoopReturnPatternAnalyzer
        // already capture both the early-return and fallthrough-return cases.
        boolean hasLoopWithReturn = methodHasLoopWithReturn(methodDecl);

        for (SymbolicExecutor.SymbolicReturn sr : results) {
            String wrappedExpr = wrapIfSubstituted(sr, mutatedFields, methodDecl);
            if (sr.pathCondition == null) {
                // Unconditional — filter trivial results (single identifier, literal, etc.)
                if (AnalysisUtils.isTrivialResult(wrappedExpr)) continue;
                if (wrappedExpr.length() > 100) continue;
                if (!symbolicExecutor.isMethodScopeSafe(wrappedExpr, methodDecl, paramNames)) continue;
                if (returnsModifiedParameter(wrappedExpr, methodDecl)) continue;
                postconditions.add(AnalysisUtils.buildResultEquality(wrappedExpr, isStringReturn));
            } else {
                if (hasLoopWithReturn) continue;
                // Conditional — single identifiers are meaningful here
                // (e.g., "a >= b ==> \result == a"), only filter ternary/new expressions
                if (wrappedExpr.contains("?") && wrappedExpr.contains(":")) continue;
                if (wrappedExpr.contains("new ")) continue;
                if (wrappedExpr.length() > 100) continue;
                if (!symbolicExecutor.isMethodScopeSafe(wrappedExpr, methodDecl, paramNames)) continue;
                // Recursive postconditions like `\result == n * factorial(n - 1)`:
                // Z3 can't unfold the recursive call inside the SMT theory and times out
                // (Recursive1.factorial, Recursive5.power). Without an explicit measure
                // and inductive helper, the postcondition reduces to "validity unknown".
                // Skip — the per-base-case `n == 0 ==> \result == 1` and any non-recursive
                // bound (`\result > 0`) still describe useful properties of the function.
                if (containsRecursiveCallTo(wrappedExpr, methodDecl.getNameAsString())) continue;
                // Don't emit `cond ==> \result == true|false` — the path condition is
                // usually incomplete (the symbolic executor doesn't model loop bodies),
                // so promising a boolean result on a partial path generates contradictions
                // with the loop-derived spec.
                String trimmedExpr = wrappedExpr.trim();
                if (trimmedExpr.equals("true") || trimmedExpr.equals("false")) continue;
                // Also drop `cond ==> \result == PARAM` when PARAM is mutated inside the
                // method (e.g. GCDE2E.gcd's `return a` after the loop modifies `a`). JML
                // interprets parameter names in ensures clauses as the call-time value;
                // emitting `\result == a` when the body mutated `a` produces a wrong
                // postcondition that fails verification for any non-trivial input.
                if (returnsModifiedParameter(wrappedExpr, methodDecl)) continue;
                String simplifiedCond = AnalysisUtils.simplifyPathCondition(sr.pathCondition);
                if (simplifiedCond.length() > 80) continue;
                if (!symbolicExecutor.isMethodScopeSafe(simplifiedCond, methodDecl, paramNames)) continue;
                postconditions.add(simplifiedCond + " ==> "
                        + AnalysisUtils.buildResultEquality(wrappedExpr, isStringReturn));
            }
        }
    }

    /**
     * True when {@code expr} is a single parameter identifier AND that parameter is
     * mutated anywhere in the method body. Such a parameter has different values at
     * pre-state (the call-time value, which is what JML's ensures binding uses) and
     * post-state (the value at the return), so `\result == PARAM` is unsound.
     * Conservative: if {@code expr} is a compound expression that happens to contain
     * a mutated parameter name as a substring, we don't suppress (the surrounding
     * arithmetic might still yield a meaningful relationship).
     */
    private boolean returnsModifiedParameter(String expr, MethodDeclaration methodDecl) {
        if (expr == null) return false;
        String trimmed = expr.trim();
        for (Parameter p : methodDecl.getParameters()) {
            if (trimmed.equals(p.getNameAsString())
                    && isParameterModified(methodDecl, p.getNameAsString())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the names of every field assigned to or compound-modified anywhere
     * in {@code methodDecl}. Used to identify fields whose appearance in a
     * symbolically-resolved return expression must be wrapped with {@code \old}.
     */
    private Set<String> collectMutatedFieldNames(MethodDeclaration methodDecl) {
        if (methodDecl.getBody().isEmpty()) return java.util.Collections.emptySet();
        Set<String> fields = new java.util.LinkedHashSet<>();
        Set<String> classFields = methodDecl.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .map(com.github.javaparser.ast.body.VariableDeclarator::getNameAsString)
                        .collect(java.util.stream.Collectors.toSet()))
                .orElseGet(java.util.HashSet::new);
        for (AssignExpr ae : methodDecl.getBody().get().findAll(AssignExpr.class)) {
            String name = null;
            if (ae.getTarget() instanceof FieldAccessExpr fae && fae.getScope().toString().equals("this")) {
                name = fae.getNameAsString();
            } else if (ae.getTarget() instanceof NameExpr ne && classFields.contains(ne.getNameAsString())) {
                name = ne.getNameAsString();
            }
            if (name != null) fields.add(name);
        }
        for (UnaryExpr ue : methodDecl.getBody().get().findAll(UnaryExpr.class)) {
            UnaryExpr.Operator op = ue.getOperator();
            if (op != UnaryExpr.Operator.PREFIX_INCREMENT
                    && op != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && op != UnaryExpr.Operator.PREFIX_DECREMENT
                    && op != UnaryExpr.Operator.POSTFIX_DECREMENT) continue;
            String name = null;
            if (ue.getExpression() instanceof FieldAccessExpr fae && fae.getScope().toString().equals("this")) {
                name = fae.getNameAsString();
            } else if (ue.getExpression() instanceof NameExpr ne && classFields.contains(ne.getNameAsString())) {
                name = ne.getNameAsString();
            }
            if (name != null) fields.add(name);
        }
        return fields;
    }

    /**
     * Returns {@code sr.resolvedExpr} either as-is or with mutated-field references
     * wrapped in {@code \old(...)}. The wrap only fires when the SymbolicExecutor
     * actually substituted something — i.e. the return value came through a captured
     * local that snapshotted a pre-mutation value. For direct returns
     * ({@code resolvedExpr == originalExpr}), the source-level field references are
     * already correctly post-state in JML semantics and must NOT be wrapped.
     *
     * <p>Also wraps {@code paramArr[idx]} accesses with {@code \old(paramArr[idx])}
     * when {@code paramArr} has had any of its elements written via
     * {@code paramArr[*] = ...}. This captures the "extract-and-replace" pattern:
     * {@code int old = arr[idx]; arr[idx] = newVal; return old;} — the resolved
     * return is {@code arr[idx]}, but at post-state {@code arr[idx]} is the new
     * value. Without the wrap the postcondition {@code \result == arr[idx]} is
     * trivially false.</p>
     */
    private String wrapIfSubstituted(SymbolicExecutor.SymbolicReturn sr,
                                      Set<String> mutatedFields, MethodDeclaration methodDecl) {
        if (sr.originalExpr != null && sr.originalExpr.equals(sr.resolvedExpr)) {
            return sr.resolvedExpr;
        }
        String wrapped = wrapMutatedFieldsWithOld(sr.resolvedExpr, mutatedFields, methodDecl);
        // Also wrap parameter-array accesses when the array's elements are written.
        Set<String> mutatedArrayParams = collectMutatedArrayParams(methodDecl);
        if (!mutatedArrayParams.isEmpty()) {
            wrapped = wrapMutatedArrayAccessesWithOld(wrapped, mutatedArrayParams);
        }
        return wrapped;
    }

    /**
     * Returns the names of parameter arrays whose elements are written anywhere in
     * the method body via {@code arr[idx] = expr} (or compound-assign). These
     * arrays' elements have different pre- and post-state values, so any
     * {@code arr[idx]} reference in a postcondition that came through symbolic
     * substitution must be wrapped with {@code \old(...)} to refer to the
     * pre-state value.
     */
    private Set<String> collectMutatedArrayParams(MethodDeclaration methodDecl) {
        if (methodDecl.getBody().isEmpty()) return java.util.Collections.emptySet();
        Set<String> params = new java.util.LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            if (p.getType().asString().contains("[]")) params.add(p.getNameAsString());
        }
        if (params.isEmpty()) return java.util.Collections.emptySet();
        Set<String> mutated = new java.util.LinkedHashSet<>();
        for (AssignExpr ae : methodDecl.getBody().get().findAll(AssignExpr.class)) {
            if (!(ae.getTarget() instanceof ArrayAccessExpr aae)) continue;
            Expression base = aae.getName();
            while (base instanceof ArrayAccessExpr inner) base = inner.getName();
            if (base instanceof NameExpr ne && params.contains(ne.getNameAsString())) {
                mutated.add(ne.getNameAsString());
            }
        }
        return mutated;
    }

    /**
     * Wraps {@code paramArr[idx]} (and {@code paramArr[idx][j]}) in {@code expr}
     * with {@code \old(paramArr[idx])}. Skips already-wrapped occurrences.
     *
     * <p>Implementation: scan the string for {@code paramArr[}, find the matching
     * close-bracket via a depth counter (since indices can themselves be
     * expressions like {@code arr[i + 1]}), and rewrite to {@code \old(...)}.</p>
     */
    private String wrapMutatedArrayAccessesWithOld(String expr, Set<String> mutatedArrays) {
        String result = expr;
        for (String name : mutatedArrays) {
            // Match `name[` not preceded by alphanumeric, dot, or backslash (the latter
            // would mean we're inside an existing \old).
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                    "(?<![\\w.\\\\])" + java.util.regex.Pattern.quote(name) + "\\[");
            java.util.regex.Matcher m = p.matcher(result);
            StringBuilder sb = new StringBuilder();
            int last = 0;
            while (m.find()) {
                int start = m.start();
                int bracketStart = m.end() - 1; // position of '['
                int depth = 1;
                int i = bracketStart + 1;
                while (i < result.length() && depth > 0) {
                    char c = result.charAt(i);
                    if (c == '[') depth++;
                    else if (c == ']') depth--;
                    if (depth > 0) i++;
                }
                if (depth != 0) {
                    // Unmatched bracket — bail on this match
                    sb.append(result, last, m.end());
                    last = m.end();
                    continue;
                }
                int closeBracket = i;
                String accessExpr = result.substring(start, closeBracket + 1);
                // Skip if already inside \old(...) — we can't easily detect this
                // by string position, but the lookbehind on `\\\\` catches the
                // common case. As an extra guard, check for `\old(` ending right
                // before `start` after stripping spaces.
                String prefix = result.substring(0, start);
                if (prefix.endsWith("\\old(")) {
                    sb.append(result, last, closeBracket + 1);
                    last = closeBracket + 1;
                    continue;
                }
                sb.append(result, last, start);
                sb.append("\\old(").append(accessExpr).append(")");
                last = closeBracket + 1;
                m.region(closeBracket + 1, result.length());
            }
            sb.append(result.substring(last));
            result = sb.toString();
        }
        return result;
    }

    /**
     * Wraps occurrences of mutated-field names in {@code expr} with {@code \old(...)},
     * matching whole-word and either bare or {@code this.}-qualified forms. Idempotent:
     * never double-wraps an already-wrapped reference.
     *
     * Skips when {@code mutatedFields} is empty or the expression contains nothing to wrap.
     */
    private String wrapMutatedFieldsWithOld(String expr, Set<String> mutatedFields,
                                             MethodDeclaration methodDecl) {
        if (expr == null || mutatedFields.isEmpty()) return expr;
        // Avoid clobbering parameters that share a name with a field — when the
        // method has a parameter `count` shadowing field `count`, the local
        // identifier in the resolvedExpr refers to the parameter, not the field.
        Set<String> paramNames = new java.util.LinkedHashSet<>();
        methodDecl.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));

        String result = expr;
        for (String field : mutatedFields) {
            if (paramNames.contains(field)) continue;
            // Wrap `this.field` → `\old(this.field)`
            String thisQual = "this." + field;
            if (result.contains(thisQual) && !result.contains("\\old(" + thisQual + ")")) {
                result = result.replace(thisQual, "\\old(" + thisQual + ")");
            }
            // Wrap bare `field` → `\old(this.field)` (skip already-old occurrences)
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                    "(?<![\\w.\\\\])" + java.util.regex.Pattern.quote(field) + "(?!\\w)");
            java.util.regex.Matcher m = p.matcher(result);
            StringBuffer sb = new StringBuffer();
            while (m.find()) {
                m.appendReplacement(sb,
                        java.util.regex.Matcher.quoteReplacement("\\old(this." + field + ")"));
            }
            m.appendTail(sb);
            result = sb.toString();
        }
        return result;
    }

    /** True when any loop in the method body contains a return statement. */
    private boolean methodHasLoopWithReturn(MethodDeclaration methodDecl) {
        if (methodDecl.getBody().isEmpty()) return false;
        for (Statement s : methodDecl.getBody().get().findAll(Statement.class)) {
            if (!(s instanceof ForStmt) && !(s instanceof WhileStmt)
                    && !(s instanceof ForEachStmt) && !(s instanceof DoStmt)) continue;
            Statement body;
            if (s instanceof ForStmt fs) body = fs.getBody();
            else if (s instanceof WhileStmt ws) body = ws.getBody();
            else if (s instanceof ForEachStmt fes) body = fes.getBody();
            else body = ((DoStmt) s).getBody();
            if (!body.findAll(ReturnStmt.class).isEmpty()) return true;
        }
        return false;
    }

    void analyzeConditionalReturns(MethodDeclaration methodDecl, Set<String> postconditions,
                                    ASTCollector collector) {
        if (!methodDecl.getBody().isPresent()) return;

        // Analyze if/else statements with return in both branches
        // Total returns in the method — lets us detect fall-through paths that our
        // two-branch summary would miss.
        int totalReturns = methodDecl.getBody().isPresent()
                ? methodDecl.getBody().get().findAll(ReturnStmt.class).size() : 0;
        collector.ifStmts.forEach(ifStmt -> {
            Optional<Statement> elseStmt = ifStmt.getElseStmt();
            if (elseStmt.isEmpty()) return;

            List<ReturnStmt> thenReturns = ifStmt.getThenStmt().findAll(ReturnStmt.class);
            List<ReturnStmt> elseReturns = elseStmt.get().findAll(ReturnStmt.class);

            if (thenReturns.isEmpty() || elseReturns.isEmpty()) return;

            ReturnStmt thenReturn = thenReturns.get(0);
            ReturnStmt elseReturn = elseReturns.get(0);

            if (thenReturn.getExpression().isEmpty() || elseReturn.getExpression().isEmpty()) return;

            Expression thenExpr = thenReturn.getExpression().get();
            Expression elseExpr = elseReturn.getExpression().get();
            Expression condition = ifStmt.getCondition();

            // If the method has returns OUTSIDE this if/else (i.e. there's a
            // fall-through path), the then/else pair doesn't fully characterise
            // \result and the disjunctive postcondition ends up unsound for
            // the fall-through — skip case 1.
            int thisIfReturns = thenReturns.size() + elseReturns.size();

            // Case 1: Every reachable return below this if/else returns a
            // literal -> disjunctive postcondition over all distinct literal
            // values. Walking the full subtree (rather than just `thenReturns
            // .get(0)` and `elseReturns.get(0)`) is what fixes IfElseChain's
            // `if(...) "A"; else if(...) "B"; else if(...) "C"; else "F";`
            // where the previous code emitted only `\result == "A" || \result
            // == "B"` and IGNORED C/D/F, then failed verification on every
            // path that returned C/D/F.
            if (thisIfReturns == totalReturns
                    && thenReturns.stream().allMatch(r -> r.getExpression().isPresent()
                            && isLiteralOrNegativeLiteral(r.getExpression().get()))
                    && elseReturns.stream().allMatch(r -> r.getExpression().isPresent()
                            && isLiteralOrNegativeLiteral(r.getExpression().get()))) {
                java.util.LinkedHashSet<String> literals = new java.util.LinkedHashSet<>();
                for (ReturnStmt rs : thenReturns) literals.add(rs.getExpression().get().toString());
                for (ReturnStmt rs : elseReturns) literals.add(rs.getExpression().get().toString());
                if (literals.size() == 1) {
                    postconditions.add(AnalysisUtils.buildResultEquality(literals.iterator().next()));
                } else {
                    String disj = literals.stream()
                            .map(AnalysisUtils::buildResultEquality)
                            .collect(java.util.stream.Collectors.joining(" || "));
                    postconditions.add(disj);
                }
            }

            // Case 2: Null check condition -> conditional postcondition
            if (condition instanceof BinaryExpr) {
                BinaryExpr binCond = (BinaryExpr) condition;
                boolean isNullCheck = (binCond.getOperator() == BinaryExpr.Operator.EQUALS ||
                                       binCond.getOperator() == BinaryExpr.Operator.NOT_EQUALS) &&
                                      (binCond.getLeft().isNullLiteralExpr() || binCond.getRight().isNullLiteralExpr());

                if (isNullCheck) {
                    Expression checkedVar = binCond.getLeft().isNullLiteralExpr()
                            ? binCond.getRight() : binCond.getLeft();
                    boolean isEqualsNull = binCond.getOperator() == BinaryExpr.Operator.EQUALS;

                    // When the null-check param is non-null, the result comes from the else/then branch
                    Expression nonNullBranchExpr = isEqualsNull ? elseExpr : thenExpr;
                    if (!nonNullBranchExpr.isNullLiteralExpr()) {
                        postconditions.add(checkedVar + " != null ==> \\result != null");
                    }
                }
            }
        });

        // Analyze ternary expressions in return statements
        collector.returnStmts.forEach(returnStmt -> {
            returnStmt.getExpression().ifPresent(expr -> {
                if (expr instanceof ConditionalExpr) {
                    ConditionalExpr ternary = (ConditionalExpr) expr;
                    Expression thenExpr = ternary.getThenExpr();
                    Expression elseExpr = ternary.getElseExpr();

                    // Both values are literals -> disjunctive postcondition
                    if (isLiteralOrNegativeLiteral(thenExpr) && isLiteralOrNegativeLiteral(elseExpr)) {
                        String thenStr = thenExpr.toString();
                        String elseStr = elseExpr.toString();
                        if (thenStr.equals(elseStr)) {
                            postconditions.add(AnalysisUtils.buildResultEquality(thenStr));
                        } else {
                            postconditions.add(AnalysisUtils.buildResultEquality(thenStr) + " || "
                                    + AnalysisUtils.buildResultEquality(elseStr));
                        }
                    }

                    // Null check in ternary condition
                    Expression condition = ternary.getCondition();
                    if (condition instanceof BinaryExpr) {
                        BinaryExpr binCond = (BinaryExpr) condition;
                        boolean isNullCheck = (binCond.getOperator() == BinaryExpr.Operator.EQUALS ||
                                               binCond.getOperator() == BinaryExpr.Operator.NOT_EQUALS) &&
                                              (binCond.getLeft().isNullLiteralExpr() || binCond.getRight().isNullLiteralExpr());

                        if (isNullCheck) {
                            Expression checkedVar = binCond.getLeft().isNullLiteralExpr()
                                    ? binCond.getRight() : binCond.getLeft();
                            boolean isEqualsNull = binCond.getOperator() == BinaryExpr.Operator.EQUALS;
                            Expression nonNullBranchExpr = isEqualsNull ? elseExpr : thenExpr;
                            if (!nonNullBranchExpr.isNullLiteralExpr()) {
                                postconditions.add(checkedVar + " != null ==> \\result != null");
                            }
                        }
                    }
                }
            });
        });
    }

    boolean isLiteralOrNegativeLiteral(Expression expr) {
        if (expr.isLiteralExpr()) return true;
        if (expr instanceof UnaryExpr) {
            UnaryExpr unary = (UnaryExpr) expr;
            return unary.getOperator() == UnaryExpr.Operator.MINUS && unary.getExpression().isLiteralExpr();
        }
        return false;
    }

    /**
     * True when the body of {@code methodDecl} reassigns the parameter named
     * {@code paramName} (including compound assignments and unary inc/dec).
     * Parameters of reference type aren't tracked for field mutation — only the
     * binding itself matters for spec-level reasoning about the parameter symbol.
     */
    boolean isParameterModified(MethodDeclaration methodDecl, String paramName) {
        if (methodDecl.getBody().isEmpty()) return false;
        for (AssignExpr ae : methodDecl.getBody().get().findAll(AssignExpr.class)) {
            if (ae.getTarget() instanceof NameExpr ne
                    && ne.getNameAsString().equals(paramName)) {
                return true;
            }
        }
        for (UnaryExpr ue : methodDecl.getBody().get().findAll(UnaryExpr.class)) {
            if (ue.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && ue.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT
                    && ue.getOperator() != UnaryExpr.Operator.POSTFIX_DECREMENT
                    && ue.getOperator() != UnaryExpr.Operator.PREFIX_DECREMENT) continue;
            if (ue.getExpression() instanceof NameExpr ne
                    && ne.getNameAsString().equals(paramName)) {
                return true;
            }
        }
        return false;
    }

    boolean involvesRecursiveCall(BinaryExpr binExpr, MethodDeclaration methodDecl) {
        String methodName = methodDecl.getNameAsString();
        return containsRecursiveCall(binExpr.getLeft(), methodName) ||
               containsRecursiveCall(binExpr.getRight(), methodName);
    }

    /**
     * True when BOTH operands of the sum can be syntactically argued non-negative:
     * a non-negative literal, a .length()/.size()/.count() call, a self-multiplication
     * on a float/double method, or a recursive call to the enclosing method (which we
     * optimistically assume preserves non-negativity — the prover will re-check this).
     * The purpose is to block `\result >= 0` when one side is e.g. `arr[index]` whose
     * sign is unknown at the spec level.
     */
    boolean bothOperandsSyntacticallyNonNegative(BinaryExpr binExpr, MethodDeclaration methodDecl) {
        return isSyntacticallyNonNegative(binExpr.getLeft(), methodDecl)
                && isSyntacticallyNonNegative(binExpr.getRight(), methodDecl);
    }

    boolean isSyntacticallyNonNegative(Expression expr, MethodDeclaration methodDecl) {
        if (expr instanceof IntegerLiteralExpr lit) {
            return lit.asInt() >= 0;
        }
        if (expr instanceof DoubleLiteralExpr dlit) {
            return dlit.asDouble() >= 0;
        }
        if (expr instanceof MethodCallExpr call) {
            String name = call.getNameAsString();
            if (name.equals(methodDecl.getNameAsString())) {
                return true; // recursive call — assume it preserves non-negativity
            }
            if (name.equals("length") || name.equals("size") || name.equals("count")) {
                return true;
            }
            if (name.equals("abs") && AnalysisUtils.isFloatingPointReturn(methodDecl)) {
                return true;
            }
        }
        if (expr instanceof BinaryExpr b) {
            if (b.getOperator() == BinaryExpr.Operator.PLUS
                    || b.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                return isSyntacticallyNonNegative(b.getLeft(), methodDecl)
                        && isSyntacticallyNonNegative(b.getRight(), methodDecl);
            }
        }
        if (expr instanceof EnclosedExpr encl) {
            return isSyntacticallyNonNegative(encl.getInner(), methodDecl);
        }
        return false;
    }

    boolean containsRecursiveCall(Expression expr, String methodName) {
        if (expr instanceof MethodCallExpr) {
            return ((MethodCallExpr) expr).getNameAsString().equals(methodName);
        }
        return expr.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getNameAsString().equals(methodName));
    }

    /**
     * String-level check: does {@code exprText} contain a syntactic call to
     * {@code methodName} (i.e. {@code methodName(...)})? Used to filter recursive
     * postconditions from the rendered ensures form before they reach the
     * AnnotationToJMLConverter — Z3 can't unfold recursive function definitions
     * in the SMT theory, so a `\result == self(...)` clause causes a timeout
     * with no useful progress.
     */
    boolean containsRecursiveCallTo(String exprText, String methodName) {
        if (exprText == null || methodName == null || methodName.isEmpty()) return false;
        // Match `methodName` followed by an opening paren, with a non-identifier char
        // before the name (start of string or operator/whitespace) so we don't trip on
        // `factoryMethodName(` for methodName = "ame".
        java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                "(^|[^\\w$.])" + java.util.regex.Pattern.quote(methodName) + "\\s*\\(");
        return p.matcher(exprText).find();
    }

    boolean isPositiveLiteral(Expression expr) {
        if (expr instanceof IntegerLiteralExpr) {
            return ((IntegerLiteralExpr) expr).asInt() > 0;
        } else if (expr instanceof DoubleLiteralExpr) {
            return ((DoubleLiteralExpr) expr).asDouble() > 0;
        }
        return false;
    }
}
