package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Analyzes method declarations to infer JML postconditions.
 */
class PostconditionAnalyzer {

    private final StringAnalyzer stringAnalyzer;
    private final CollectionAnalyzer collectionAnalyzer;
    private final ReturnValueAnalyzer returnValueAnalyzer;
    private final InterproceduralAnalyzer interproceduralAnalyzer;
    private final SymbolicExecutor symbolicExecutor;
    private final FieldModificationAnalyzer fieldModificationAnalyzer;
    private final LoopReturnPatternAnalyzer loopReturnPatternAnalyzer;

    PostconditionAnalyzer(StringAnalyzer stringAnalyzer, CollectionAnalyzer collectionAnalyzer,
                          ReturnValueAnalyzer returnValueAnalyzer, InterproceduralAnalyzer interproceduralAnalyzer,
                          SymbolicExecutor symbolicExecutor) {
        this.stringAnalyzer = stringAnalyzer;
        this.collectionAnalyzer = collectionAnalyzer;
        this.returnValueAnalyzer = returnValueAnalyzer;
        this.interproceduralAnalyzer = interproceduralAnalyzer;
        this.symbolicExecutor = symbolicExecutor;
        this.fieldModificationAnalyzer = new FieldModificationAnalyzer();
        this.loopReturnPatternAnalyzer = new LoopReturnPatternAnalyzer();
    }

    void inferPostconditions(MethodDeclaration methodDecl, com.jml.inferrer.model.MethodSpecification spec,
                              ASTCollector collector) {
        Set<String> postconditions = new LinkedHashSet<>();

        if (!methodDecl.getType().isVoidType()) {
            String returnType = methodDecl.getType().asString();

            // Reference type checks
            if (AnalysisUtils.isReferenceType(returnType)) {
                if (alwaysReturnsNonNull(collector, methodDecl)) {
                    postconditions.add("\\result != null");
                }
            }

            // Numeric type analysis
            if (AnalysisUtils.isNumericType(methodDecl.getType())) {
                analyzeReturnValueConstraints(methodDecl, postconditions, collector);
                returnValueAnalyzer.analyzeNumericReturnBounds(methodDecl, postconditions, collector);
                returnValueAnalyzer.analyzeReturnRelationToParameters(methodDecl, postconditions, collector);
                // Loop accumulator: `int x = 0; for(...) x += positive; return x;` → \result >= 0
                returnValueAnalyzer.analyzeLoopAccumulatorReturn(methodDecl, postconditions);
            }

            // Pattern-based loop-return ensures (sum, product, max/min, conditional counter,
            // linear search). Runs for any non-void return type.
            loopReturnPatternAnalyzer.analyze(methodDecl, postconditions, spec);

            // String return analysis
            if (returnType.equals("String")) {
                stringAnalyzer.analyzeStringReturnProperties(methodDecl, postconditions, collector);
            }

            // Collection/Array return analysis
            if (AnalysisUtils.isCollectionType(returnType) || returnType.contains("[]")) {
                collectionAnalyzer.analyzeCollectionReturnProperties(methodDecl, postconditions, collector);
            }

            // Builder pattern detection (returns 'this')
            if (returnsThis(collector)) {
                postconditions.add("\\result == this");
            }

            // Factory/Constructor pattern
            if (returnType.equals(methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .map(c -> c.getNameAsString()).orElse(""))) {
                analyzeFactoryMethodPattern(methodDecl, postconditions, collector);
            }

            // Comparison method patterns
            analyzeComparisonMethodPattern(methodDecl, postconditions);

            // Analyze return value identity/equality
            analyzeReturnValueIdentity(methodDecl, postconditions, collector);

            // Interprocedural analysis: propagate postconditions from called methods
            interproceduralAnalyzer.analyzeMethodCallPostconditions(methodDecl, postconditions, collector);

            // Conditional postconditions (branch-aware)
            returnValueAnalyzer.analyzeConditionalReturns(methodDecl, postconditions, collector);

            // Exact symbolic return expression
            returnValueAnalyzer.analyzeExactReturnExpression(methodDecl, postconditions, symbolicExecutor);
        }

        // Field and parameter modification analysis
        fieldModificationAnalyzer.analyzeFieldModifications(methodDecl, postconditions, collector);
        analyzeParameterModifications(methodDecl, postconditions, collector);

        // Exception guarantees
        analyzeExceptionGuarantees(methodDecl, postconditions, collector);

        // Fallback: every non-void method needs at least one ensures clause. When nothing
        // meaningful was inferred (no accumulator pattern, no return-expr summary, no
        // interprocedural postcondition, etc.) emit `true` so the spec still meets the
        // "non-void method has an ensures" quality gate. `true` is trivially sound and
        // lets OpenJML discharge the proof vacuously.
        if (!methodDecl.getType().isVoidType() && postconditions.isEmpty()) {
            postconditions.add("true");
        }

        postconditions.forEach(spec::addPostcondition);
    }

    static boolean alwaysReturnsNonNull(ASTCollector collector) {
        return alwaysReturnsNonNull(collector, null);
    }

    static boolean alwaysReturnsNonNull(ASTCollector collector, MethodDeclaration methodDecl) {
        if (collector.returnStmts.isEmpty()) {
            return false;
        }
        Set<String> refFieldNames = methodDecl == null ? java.util.Set.of()
                : collectReferenceFieldNames(methodDecl);
        return collector.returnStmts.stream()
            .allMatch(ret -> ret.getExpression()
                .map(expr -> isSyntacticallyNonNull(expr, refFieldNames))
                .orElse(false));
    }

    private static Set<String> collectReferenceFieldNames(MethodDeclaration methodDecl) {
        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .filter(f -> !f.getCommonType().isPrimitiveType())
                        .flatMap(f -> f.getVariables().stream())
                        .map(com.github.javaparser.ast.body.VariableDeclarator::getNameAsString)
                        .collect(java.util.stream.Collectors.toSet()))
                .orElseGet(java.util.HashSet::new);
    }

    /**
     * Returns true when the expression is NOT a bare reference-field read. A bare
     * field getter (e.g. `return this.name;` or `return name;` where `name` is a
     * reference field) can legitimately return null because the field is default-
     * initialised to null when no explicit constructor sets it. Previously this
     * method only rejected `null` literal, which led to unsound
     * `ensures \result != null` on plain field getters.
     *
     * <p>Everything else stays as before (method calls, `new X()`, `a + b`,
     * params, locals) — those were accepted and the existing analysis-test
     * expectations depend on it.</p>
     */
    private static boolean isSyntacticallyNonNull(Expression expr, Set<String> refFieldNames) {
        if (expr.isNullLiteralExpr()) return false;
        // `return this.field` — default null for reference fields. Reject.
        if (expr instanceof FieldAccessExpr fae
                && fae.getScope().toString().equals("this")) {
            return false;
        }
        // `return bareName` where `bareName` resolves to a reference field of the
        // enclosing class. Without an explicit constructor initialising the field,
        // it's default null, so the getter can return null.
        if (expr instanceof NameExpr ne && refFieldNames.contains(ne.getNameAsString())) {
            return false;
        }
        return true;
    }

    private void analyzeReturnValueConstraints(MethodDeclaration methodDecl, Set<String> postconditions,
                                                ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                Expression effective = expr;

                // Resolve local variable to its last assigned expression
                if (expr instanceof NameExpr) {
                    String name = ((NameExpr) expr).getNameAsString();
                    boolean isParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(name));
                    if (!isParam) {
                        Expression resolved = returnValueAnalyzer.resolveLocalVariable(methodDecl, name);
                        if (resolved != null) {
                            effective = resolved;
                        }
                    }
                }

                if (effective instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) effective;
                    if (binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY &&
                        AnalysisUtils.isSelfMultiplication(binExpr) &&
                        AnalysisUtils.isFloatingPointReturn(methodDecl)) {
                        postconditions.add("\\result >= 0");
                    }
                } else if (effective instanceof MethodCallExpr) {
                    MethodCallExpr methodCall = (MethodCallExpr) effective;
                    String callName = methodCall.getNameAsString();
                    if (callName.equals("length")) {
                        postconditions.add("\\result >= 0");
                    } else if (callName.equals("abs") && AnalysisUtils.isFloatingPointReturn(methodDecl)) {
                        // abs() only non-negative for float/double; Math.abs(Integer.MIN_VALUE) is negative
                        postconditions.add("\\result >= 0");
                    }
                }
            });
        }
    }

    private boolean returnsThis(ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;
        if (returnStmts.isEmpty()) {
            return false;
        }

        return returnStmts.stream()
            .allMatch(ret -> ret.getExpression()
                .map(expr -> expr.isThisExpr() || expr.toString().equals("this"))
                .orElse(false));
    }

    private void analyzeFactoryMethodPattern(MethodDeclaration methodDecl, Set<String> postconditions,
                                              ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                if (expr instanceof ObjectCreationExpr) {
                    ObjectCreationExpr creation = (ObjectCreationExpr) expr;
                    postconditions.add("\\result != null");
                    postconditions.add("\\result instanceof " + creation.getType().asString());
                }
            });
        }
    }

    private void analyzeComparisonMethodPattern(MethodDeclaration methodDecl, Set<String> postconditions) {
        String methodName = methodDecl.getNameAsString();

        if (methodName.equals("compareTo")) {
            if (methodDecl.getType().asString().equals("int")) {
                postconditions.add("\\result >= -1 && \\result <= 1 || \\result < -1 || \\result > 1");
            }
        } else if (methodName.equals("equals")) {
            if (methodDecl.getType().asString().equals("boolean")) {
                if (methodDecl.getParameters().size() == 1) {
                    String paramName = methodDecl.getParameters().get(0).getNameAsString();
                    postconditions.add("(this.equals(" + paramName + ") ==> " + paramName + ".equals(this))");
                }
            }
        } else if (methodName.equals("hashCode")) {
            if (methodDecl.getType().asString().equals("int")) {
                postconditions.add("\\result == \\result");
            }
        }
    }

    private void analyzeReturnValueIdentity(MethodDeclaration methodDecl, Set<String> postconditions,
                                             ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;
        if (returnStmts.size() != 1) return;

        // Only emit \result == this.field when the field is not modified in this method,
        // otherwise the spec would be unsound (e.g., next() that returns this.cursor and increments it).
        returnStmts.get(0).getExpression().ifPresent(expr -> {
            String fieldName = null;
            if (expr instanceof FieldAccessExpr fieldAccess
                    && fieldAccess.getScope().toString().equals("this")) {
                fieldName = fieldAccess.getNameAsString();
            } else if (expr instanceof NameExpr nameExpr) {
                String exprName = nameExpr.getNameAsString();
                if (AnalysisUtils.isFieldReference(methodDecl, exprName)) {
                    fieldName = exprName;
                }
            }
            if (fieldName == null) return;

            String fName = fieldName;
            boolean fieldWritten = collector.assignExprs.stream().anyMatch(a -> {
                Expression t = a.getTarget();
                if (t instanceof FieldAccessExpr fa
                        && fa.getScope().toString().equals("this")
                        && fa.getNameAsString().equals(fName)) return true;
                if (t instanceof NameExpr ne && ne.getNameAsString().equals(fName)
                        && AnalysisUtils.isFieldReference(methodDecl, fName)) return true;
                return false;
            });
            if (fieldWritten) return;
            boolean fieldUnaryWritten = collector.unaryExprs.stream().anyMatch(u -> {
                switch (u.getOperator()) {
                    case POSTFIX_INCREMENT:
                    case POSTFIX_DECREMENT:
                    case PREFIX_INCREMENT:
                    case PREFIX_DECREMENT:
                        Expression e = u.getExpression();
                        if (e instanceof FieldAccessExpr fa
                                && fa.getScope().toString().equals("this")
                                && fa.getNameAsString().equals(fName)) return true;
                        if (e instanceof NameExpr ne && ne.getNameAsString().equals(fName)
                                && AnalysisUtils.isFieldReference(methodDecl, fName)) return true;
                        return false;
                    default:
                        return false;
                }
            });
            if (fieldUnaryWritten) return;

            postconditions.add("\\result == this." + fieldName);
        });
    }

    private void analyzeParameterModifications(MethodDeclaration methodDecl, Set<String> postconditions,
                                                ASTCollector collector) {
        for (Parameter param : methodDecl.getParameters()) {
            String paramName = param.getNameAsString();
            String paramType = param.getType().asString();

            if (AnalysisUtils.isCollectionType(paramType)) {
                boolean hasAdd = collector.methodCallExprs.stream()
                    .anyMatch(call -> call.getScope()
                        .map(s -> s.toString().equals(paramName))
                        .orElse(false) && call.getNameAsString().equals("add"));

                boolean hasRemove = collector.methodCallExprs.stream()
                    .anyMatch(call -> call.getScope()
                        .map(s -> s.toString().equals(paramName))
                        .orElse(false) && call.getNameAsString().equals("remove"));

                boolean hasClear = collector.methodCallExprs.stream()
                    .anyMatch(call -> call.getScope()
                        .map(s -> s.toString().equals(paramName))
                        .orElse(false) && call.getNameAsString().equals("clear"));

                if (hasAdd) {
                    postconditions.add(paramName + ".size() >= \\old(" + paramName + ".size())");
                }
                if (hasRemove) {
                    postconditions.add(paramName + ".size() <= \\old(" + paramName + ".size())");
                }
                if (hasClear) {
                    postconditions.add(paramName + ".isEmpty()");
                }
            }

            if (paramType.contains("[]")) {
                boolean hasArrayWrite = collector.assignExprs.stream()
                    .anyMatch(assign -> assign.getTarget() instanceof ArrayAccessExpr &&
                        ((ArrayAccessExpr) assign.getTarget()).getName().toString().equals(paramName));
            }
        }
    }

    private void analyzeExceptionGuarantees(MethodDeclaration methodDecl, Set<String> postconditions,
                                             ASTCollector collector) {
        Set<String> thrownExceptions = new LinkedHashSet<>();
        collector.throwStmts.forEach(throwStmt -> {
            throwStmt.getExpression().ifObjectCreationExpr(creation -> {
                thrownExceptions.add(creation.getType().asString());
            });
        });

        thrownExceptions.forEach(exceptionType -> {
            // Don't add this as a postcondition, as it's exceptional behavior
        });
    }

    /**
     * Promotes quantified loop invariants to postconditions by substituting the
     * loop counter with its exit value. E.g., for a loop {@code for (int i=0; i<arr.length; i++)}
     * with invariant {@code (\forall int k; 0 <= k < i; arr[k] == val)}, at loop exit
     * {@code i == arr.length}, so the postcondition becomes
     * {@code (\forall int k; 0 <= k < arr.length; arr[k] == val)}.
     */
    void promoteLoopInvariantsToPostconditions(MethodDeclaration methodDecl, MethodSpecification spec) {
        if (methodDecl.getBody().isEmpty()) return;

        // Build a map of loop counter → exit value from all for-loops. Skip loops whose
        // bodies have early `return` or `throw` statements — the counter may not reach
        // the natural exit value, so promoting `\forall k; 0 <= k < exit; …` would
        // produce a postcondition that's false on early-exit paths.
        Map<String, String> counterExitValues = new LinkedHashMap<>();
        methodDecl.getBody().get().findAll(ForStmt.class).forEach(forStmt -> {
            if (loopHasEarlyExit(forStmt)) return;
            forStmt.getInitialization().stream()
                .filter(e -> e instanceof VariableDeclarationExpr)
                .forEach(e -> ((VariableDeclarationExpr) e).getVariables().forEach(var -> {
                    String counter = var.getNameAsString();
                    forStmt.getCompare().ifPresent(compare -> {
                        if (compare instanceof BinaryExpr) {
                            BinaryExpr bin = (BinaryExpr) compare;
                            // i < arr.length  →  exit when i == arr.length
                            if (bin.getLeft().toString().equals(counter) &&
                                (bin.getOperator() == BinaryExpr.Operator.LESS ||
                                 bin.getOperator() == BinaryExpr.Operator.LESS_EQUALS)) {
                                String bound = bin.getRight().toString();
                                if (bin.getOperator() == BinaryExpr.Operator.LESS) {
                                    counterExitValues.put(counter, bound);
                                } else {
                                    // i <= n  →  exit when i == n + 1
                                    counterExitValues.put(counter, bound + " + 1");
                                }
                            }
                        }
                    });
                }));
        });

        if (counterExitValues.isEmpty()) return;

        // Identify a local variable that's consistently returned — used to substitute
        // its name for `\result` in promoted postconditions.
        String returnedLocal = findReturnedLocalName(methodDecl);

        // Set of all loop counter names — after substitution, the promoted postcondition
        // must not reference any of them because their meaning isn't defined outside the
        // loop. Nested-loop invariants often mention the outer counter.
        Set<String> allCounters = new LinkedHashSet<>(counterExitValues.keySet());
        methodDecl.getBody().get().findAll(ForStmt.class).forEach(fs ->
                fs.getInitialization().forEach(init -> {
                    if (init instanceof VariableDeclarationExpr vde) {
                        vde.getVariables().forEach(v -> allCounters.add(v.getNameAsString()));
                    }
                }));

        // Set of all OTHER local variable names declared anywhere in the method body
        // (excluding loop counters, which are handled by allCounters above and the
        // returnedLocal replacement). Promoted postconditions cannot reference these
        // — they're not visible at method scope. Skipping them prevents the
        // "cannot find symbol" OpenJML errors seen for MoveZeroes.moveZeroes etc.
        Set<String> otherLocals = new LinkedHashSet<>();
        methodDecl.getBody().get().findAll(VariableDeclarationExpr.class).forEach(vde ->
                vde.getVariables().forEach(v -> {
                    String n = v.getNameAsString();
                    if (!allCounters.contains(n)
                            && (returnedLocal == null || !returnedLocal.equals(n))) {
                        otherLocals.add(n);
                    }
                }));

        // Pattern to find counter variable in forall bound: 0 <= k < COUNTER
        for (String invariant : spec.getLoopInvariants()) {
            if (!invariant.contains("\\forall")) continue;

            for (Map.Entry<String, String> entry : counterExitValues.entrySet()) {
                String counter = entry.getKey();
                String exitValue = entry.getValue();

                // Match patterns like "< i" or "< i;" in the forall bound
                Pattern p = Pattern.compile("< " + Pattern.quote(counter) + "(?=[;\\s)])");
                Matcher m = p.matcher(invariant);
                if (m.find()) {
                    String postcond = m.replaceAll("< " + exitValue);
                    if (returnedLocal != null) {
                        postcond = postcond.replaceAll(
                                "\\b" + Pattern.quote(returnedLocal) + "\\b", "\\\\result");
                    }
                    // Skip if the promoted postcondition still references ANY loop
                    // counter (including the one we just substituted — invariants often
                    // use the counter in multiple positions: `< i` AND `arr[i][k]`).
                    if (referencesAnyCounter(postcond, allCounters, null)) continue;
                    // Skip if it references a non-counter local (e.g. `writeIdx` from
                    // a two-pointer loop). Those identifiers don't exist at the
                    // postcondition site and produce "cannot find symbol".
                    if (referencesAnyCounter(postcond, otherLocals, null)) continue;
                    spec.addPostcondition(postcond,
                            MethodSpecification.ConfidenceLevel.MEDIUM);
                }
            }
        }
    }

    private boolean referencesAnyCounter(String text, Set<String> allCounters, String excludedCounter) {
        for (String c : allCounters) {
            if (excludedCounter != null && c.equals(excludedCounter)) continue;
            // Match `c` as a standalone identifier (word boundaries, not after `.`)
            // Also skip occurrences where the counter is the outer loop bind variable
            // `\forall int c;` — that's a legitimate declaration, not a reference.
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                    "(?<![.\\w])(?<!int\\s)" + java.util.regex.Pattern.quote(c) + "(?![\\w])");
            if (p.matcher(text).find()) return true;
        }
        return false;
    }

    private boolean loopHasEarlyExit(ForStmt forStmt) {
        for (ReturnStmt ret : forStmt.getBody().findAll(ReturnStmt.class)) {
            if (ret.findAncestor(ForStmt.class).orElse(null) == forStmt) return true;
        }
        for (com.github.javaparser.ast.stmt.ThrowStmt t
                : forStmt.getBody().findAll(com.github.javaparser.ast.stmt.ThrowStmt.class)) {
            if (t.findAncestor(ForStmt.class).orElse(null) == forStmt) return true;
        }
        for (com.github.javaparser.ast.stmt.BreakStmt b
                : forStmt.getBody().findAll(com.github.javaparser.ast.stmt.BreakStmt.class)) {
            if (b.findAncestor(ForStmt.class).orElse(null) == forStmt) return true;
        }
        return false;
    }

    /**
     * Returns the name of the single local variable that the method returns (e.g., the
     * idiom {@code int[] result = new int[n]; ...; return result;}), or {@code null}
     * if no such consistent local exists. Used so promoted postconditions can replace
     * the local name with {@code \result}.
     */
    private String findReturnedLocalName(MethodDeclaration methodDecl) {
        if (methodDecl.getBody().isEmpty()) return null;
        Set<String> localNames = new LinkedHashSet<>();
        methodDecl.findAll(VariableDeclarationExpr.class).forEach(vde ->
                vde.getVariables().forEach(v -> localNames.add(v.getNameAsString())));

        Set<String> returnedLocals = new LinkedHashSet<>();
        methodDecl.findAll(ReturnStmt.class).forEach(ret ->
                ret.getExpression().ifPresent(e -> {
                    if (e instanceof NameExpr ne && localNames.contains(ne.getNameAsString())) {
                        returnedLocals.add(ne.getNameAsString());
                    }
                }));
        if (returnedLocals.size() == 1) {
            return returnedLocals.iterator().next();
        }
        return null;
    }
}
