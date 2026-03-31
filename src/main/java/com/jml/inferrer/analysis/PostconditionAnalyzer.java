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

    PostconditionAnalyzer(StringAnalyzer stringAnalyzer, CollectionAnalyzer collectionAnalyzer,
                          ReturnValueAnalyzer returnValueAnalyzer, InterproceduralAnalyzer interproceduralAnalyzer,
                          SymbolicExecutor symbolicExecutor) {
        this.stringAnalyzer = stringAnalyzer;
        this.collectionAnalyzer = collectionAnalyzer;
        this.returnValueAnalyzer = returnValueAnalyzer;
        this.interproceduralAnalyzer = interproceduralAnalyzer;
        this.symbolicExecutor = symbolicExecutor;
        this.fieldModificationAnalyzer = new FieldModificationAnalyzer();
    }

    void inferPostconditions(MethodDeclaration methodDecl, com.jml.inferrer.model.MethodSpecification spec,
                              ASTCollector collector) {
        Set<String> postconditions = new LinkedHashSet<>();

        if (!methodDecl.getType().isVoidType()) {
            String returnType = methodDecl.getType().asString();

            // Reference type checks
            if (AnalysisUtils.isReferenceType(returnType)) {
                if (alwaysReturnsNonNull(collector)) {
                    postconditions.add("\\result != null");
                }
            }

            // Numeric type analysis
            if (AnalysisUtils.isNumericType(methodDecl.getType())) {
                analyzeReturnValueConstraints(methodDecl, postconditions, collector);
                returnValueAnalyzer.analyzeNumericReturnBounds(methodDecl, postconditions, collector);
                returnValueAnalyzer.analyzeReturnRelationToParameters(methodDecl, postconditions, collector);
            }

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

        postconditions.forEach(spec::addPostcondition);
    }

    static boolean alwaysReturnsNonNull(ASTCollector collector) {
        if (collector.returnStmts.isEmpty()) {
            return false;
        }

        return collector.returnStmts.stream()
            .allMatch(ret -> ret.getExpression()
                .map(expr -> !expr.isNullLiteralExpr())
                .orElse(false));
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
        String methodName = methodDecl.getNameAsString();

        if (methodName.startsWith("get") && returnStmts.size() == 1) {
            returnStmts.get(0).getExpression().ifPresent(expr -> {
                if (expr instanceof FieldAccessExpr) {
                    FieldAccessExpr fieldAccess = (FieldAccessExpr) expr;
                    if (fieldAccess.getScope().toString().equals("this")) {
                        postconditions.add("\\result == this." + fieldAccess.getNameAsString());
                    }
                } else if (expr instanceof NameExpr) {
                    methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                        .ifPresent(classDecl -> {
                            String exprName = expr.toString();
                            classDecl.getFields().forEach(field -> {
                                field.getVariables().forEach(var -> {
                                    if (var.getNameAsString().equals(exprName)) {
                                        postconditions.add("\\result == this." + exprName);
                                    }
                                });
                            });
                        });
                }
            });
        }
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

        // Build a map of loop counter → exit value from all for-loops
        Map<String, String> counterExitValues = new LinkedHashMap<>();
        methodDecl.getBody().get().findAll(ForStmt.class).forEach(forStmt -> {
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
                    spec.addPostcondition(postcond,
                            MethodSpecification.ConfidenceLevel.MEDIUM);
                }
            }
        }
    }
}
