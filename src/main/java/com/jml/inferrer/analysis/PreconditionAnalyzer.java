package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.*;

/**
 * Analyzes method declarations to infer JML preconditions.
 */
class PreconditionAnalyzer {

    void inferPreconditions(MethodDeclaration methodDecl, com.jml.inferrer.model.MethodSpecification spec,
                            InterproceduralAnalyzer interproceduralAnalyzer, ASTCollector collector) {
        Set<String> preconditions = new LinkedHashSet<>();

        for (Parameter param : methodDecl.getParameters()) {
            String paramName = param.getNameAsString();
            com.github.javaparser.ast.type.Type paramType = param.getType();

            // Reference type null checks
            if (paramType.isReferenceType() && !paramType.isPrimitiveType()) {
                if (hasNullCheckOrAccess(methodDecl, paramName, collector)) {
                    preconditions.add(paramName + " != null");
                }
            }

            // String-specific preconditions
            if (paramType.asString().equals("String")) {
                analyzeStringParameterConstraints(methodDecl, paramName, preconditions, collector);
            }

            // Numeric type constraints
            if (AnalysisUtils.isNumericType(paramType)) {
                analyzeNumericConstraints(methodDecl, paramName, preconditions, collector);
            }

            // Array and collection constraints
            if (paramType.asString().contains("[]")) {
                analyzeArrayParameterConstraints(methodDecl, paramName, preconditions, collector);
            } else if (AnalysisUtils.isCollectionType(paramType.asString())) {
                analyzeCollectionParameterConstraints(methodDecl, paramName, preconditions, collector);
            }
        }

        // Analyze early validation patterns
        analyzeEarlyValidation(methodDecl, preconditions, collector);

        // Analyze null checks in method body
        NullCheckVisitor nullCheckVisitor = new NullCheckVisitor();
        methodDecl.accept(nullCheckVisitor, null);
        preconditions.addAll(nullCheckVisitor.getNullChecks());

        // Analyze parameter relationships
        analyzeParameterRelationships(methodDecl, preconditions, collector);

        // Interprocedural analysis: propagate preconditions from called methods
        interproceduralAnalyzer.analyzeMethodCallPreconditions(methodDecl, preconditions, collector);

        preconditions.forEach(spec::addPrecondition);
    }

    boolean hasNullCheckOrAccess(MethodDeclaration methodDecl, String paramName, ASTCollector collector) {
        // Check for explicit null checks
        boolean hasNullCheck = collector.binaryExprs.stream()
            .anyMatch(binExpr -> {
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS ||
                    binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS) {
                    return (binExpr.getLeft().toString().equals(paramName) && binExpr.getRight().isNullLiteralExpr()) ||
                           (binExpr.getRight().toString().equals(paramName) && binExpr.getLeft().isNullLiteralExpr());
                }
                return false;
            });

        // Check for method calls on the parameter
        boolean hasMethodCall = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false));

        // Check for field access on the parameter
        boolean hasFieldAccess = collector.fieldAccessExprs.stream()
            .anyMatch(field -> field.getScope().toString().equals(paramName));

        // Check for for-each loop over the parameter (implies non-null)
        boolean hasForEachUsage = collector.forEachStmts.stream()
            .anyMatch(forEach -> forEach.getIterable().toString().equals(paramName));

        return hasNullCheck || hasMethodCall || hasFieldAccess || hasForEachUsage;
    }

    private void analyzeStringParameterConstraints(MethodDeclaration methodDecl, String paramName,
                                                    Set<String> preconditions, ASTCollector collector) {
        // Check for null requirement
        if (hasNullCheckOrAccess(methodDecl, paramName, collector)) {
            preconditions.add(paramName + " != null");
        }

        // Check for isEmpty() calls
        boolean hasEmptyCheck = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("isEmpty"));

        // Check for length() calls with comparisons
        collector.methodCallExprs.stream()
            .filter(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("length"))
            .forEach(lengthCall -> {
                // Look for comparisons with this length call
                collector.binaryExprs.stream()
                    .filter(binExpr -> binExpr.getLeft().toString().contains(paramName + ".length()") ||
                                       binExpr.getRight().toString().contains(paramName + ".length()"))
                    .forEach(binExpr -> {
                        if (binExpr.getOperator() == BinaryExpr.Operator.GREATER &&
                            binExpr.getLeft().toString().contains(paramName + ".length()")) {
                            preconditions.add(paramName + ".length() > " + binExpr.getRight());
                        }
                    });
            });

        // If isEmpty() is called, check whether it's used in a guard condition (if/else).
        // If the method handles both empty and non-empty cases, don't add as precondition.
        if (hasEmptyCheck) {
            boolean isGuardCondition = collector.ifStmts.stream()
                    .anyMatch(ifStmt -> {
                        String condStr = ifStmt.getCondition().toString();
                        return condStr.contains(paramName + ".isEmpty()");
                    });
            if (!isGuardCondition) {
                // isEmpty() is called but not as a guard — likely needs non-empty
                preconditions.add("!" + paramName + ".isEmpty()");
            }
            // If it IS a guard, the method handles both cases, so no precondition needed
        }

        // Check for charAt() calls - implies non-empty
        boolean hasCharAt = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("charAt"));

        if (hasCharAt) {
            preconditions.add(paramName + ".length() > 0");
        }
    }

    private void analyzeArrayParameterConstraints(MethodDeclaration methodDecl, String paramName,
                                                    Set<String> preconditions, ASTCollector collector) {
        // Check for null requirement
        boolean hasArrayAccess = collector.arrayAccessExprs.stream()
            .anyMatch(access -> access.getName().toString().equals(paramName));

        boolean hasLengthAccess = collector.fieldAccessExprs.stream()
            .anyMatch(field -> field.getScope().toString().equals(paramName) &&
                              field.getNameAsString().equals("length"));

        if (hasArrayAccess || hasLengthAccess) {
            preconditions.add(paramName + " != null");
        }

        // Check for array index access to infer non-empty requirement
        if (hasArrayAccess) {
            // Check if accessing specific indices
            collector.arrayAccessExprs.stream()
                .filter(access -> access.getName().toString().equals(paramName))
                .forEach(access -> {
                    Expression index = access.getIndex();
                    if (index instanceof IntegerLiteralExpr) {
                        int indexValue = ((IntegerLiteralExpr) index).asInt();
                        preconditions.add(paramName + ".length > " + indexValue);
                    } else if (index instanceof NameExpr) {
                        // Index is a variable — check if it's a parameter
                        String indexName = ((NameExpr) index).getNameAsString();
                        boolean isParam = methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(indexName));
                        if (isParam) {
                            // Generate proper bounds: idx >= 0 && idx < arr.length
                            preconditions.add(indexName + " >= 0");
                            preconditions.add(indexName + " < " + paramName + ".length");
                        } else {
                            // Non-parameter variable (e.g. loop var) — just need non-empty
                            preconditions.add(paramName + ".length > 0");
                        }
                    } else {
                        // Complex index expression — just need non-empty
                        preconditions.add(paramName + ".length > 0");
                    }
                });
        }

        // Check for length comparisons in conditionals
        analyzeArrayLengthConstraints(methodDecl, paramName, preconditions, collector);
    }

    private void analyzeCollectionParameterConstraints(MethodDeclaration methodDecl, String paramName,
                                                        Set<String> preconditions, ASTCollector collector) {
        // Check for null requirement
        boolean hasMethodCall = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false));

        if (hasMethodCall) {
            preconditions.add(paramName + " != null");
        }

        // Check for size() calls
        boolean hasSizeCheck = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("size"));

        // Check for isEmpty() calls
        boolean hasEmptyCheck = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("isEmpty"));

        // Check for iterator or get operations - implies non-empty
        boolean hasGet = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("get"));

        if (hasGet) {
            preconditions.add(paramName + ".size() > 0");
        }
    }

    private void analyzeEarlyValidation(MethodDeclaration methodDecl, Set<String> preconditions,
                                         ASTCollector collector) {
        collector.ifStmts.forEach(ifStmt -> {
            // Check if this if statement throws an exception
            boolean throwsException = ifStmt.getThenStmt().findAll(ThrowStmt.class).size() > 0;

            if (throwsException) {
                Expression condition = ifStmt.getCondition();

                // Invert the condition to get the precondition
                if (condition instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) condition;
                    String invertedCondition = invertCondition(binExpr);
                    if (invertedCondition != null && !invertedCondition.isEmpty()) {
                        preconditions.add(invertedCondition);
                    }
                } else if (condition instanceof UnaryExpr) {
                    UnaryExpr unaryExpr = (UnaryExpr) condition;
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
                        // !(condition) in if-throw means condition must be true
                        preconditions.add(unaryExpr.getExpression().toString());
                    }
                }
            }
        });
    }

    private void analyzeParameterRelationships(MethodDeclaration methodDecl, Set<String> preconditions,
                                                ASTCollector collector) {
        List<Parameter> params = methodDecl.getParameters();

        // Only generate parameter relationship preconditions from early validation patterns
        // (if-throw blocks), not from general branching logic.
        collector.ifStmts.forEach(ifStmt -> {
            boolean throwsException = !ifStmt.getThenStmt().findAll(ThrowStmt.class).isEmpty();
            if (!throwsException) return;

            ifStmt.getCondition().findAll(BinaryExpr.class).forEach(binExpr -> {
                String left = binExpr.getLeft().toString();
                String right = binExpr.getRight().toString();

                boolean leftIsParam = params.stream().anyMatch(p -> p.getNameAsString().equals(left));
                boolean rightIsParam = params.stream().anyMatch(p -> p.getNameAsString().equals(right));

                if (leftIsParam && rightIsParam) {
                    // Invert the condition: if (a < b) throw → requires a >= b
                    String inverted = invertBinaryOperator(binExpr.getOperator());
                    if (inverted != null) {
                        preconditions.add(left + " " + inverted + " " + right);
                    }
                }
            });
        });
    }

    String invertBinaryOperator(BinaryExpr.Operator op) {
        switch (op) {
            case LESS: return ">=";
            case LESS_EQUALS: return ">";
            case GREATER: return "<=";
            case GREATER_EQUALS: return "<";
            case EQUALS: return "!=";
            case NOT_EQUALS: return "==";
            default: return null;
        }
    }

    private void analyzeArrayLengthConstraints(MethodDeclaration methodDecl, String paramName,
                                                Set<String> preconditions, ASTCollector collector) {
        Set<String> paramNames = new java.util.HashSet<>();
        methodDecl.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));

        collector.binaryExprs.stream()
            .filter(binExpr -> binExpr.getLeft().toString().equals(paramName + ".length") ||
                               binExpr.getRight().toString().equals(paramName + ".length"))
            .forEach(binExpr -> {
                if (binExpr.getLeft().toString().equals(paramName + ".length")) {
                    String otherSide = binExpr.getRight().toString();
                    // Only add precondition if the other side is a parameter or literal
                    if (!isParameterOrLiteral(otherSide, paramNames)) return;
                    switch (binExpr.getOperator()) {
                        case GREATER:
                            preconditions.add(paramName + ".length > " + otherSide);
                            break;
                        case GREATER_EQUALS:
                            preconditions.add(paramName + ".length >= " + otherSide);
                            break;
                        case EQUALS:
                            preconditions.add(paramName + ".length == " + otherSide);
                            break;
                    }
                } else if (binExpr.getRight().toString().equals(paramName + ".length")) {
                    String otherSide = binExpr.getLeft().toString();
                    // Only add precondition if the other side is a parameter or literal
                    if (!isParameterOrLiteral(otherSide, paramNames)) return;
                    switch (binExpr.getOperator()) {
                        case LESS:
                            preconditions.add(paramName + ".length > " + otherSide);
                            break;
                        case LESS_EQUALS:
                            preconditions.add(paramName + ".length >= " + otherSide);
                            break;
                        case EQUALS:
                            preconditions.add(paramName + ".length == " + otherSide);
                            break;
                    }
                }
            });
    }

    private boolean isParameterOrLiteral(String expr, Set<String> paramNames) {
        if (paramNames.contains(expr)) return true;
        if (expr.matches("-?\\d+")) return true; // integer literal
        // Check for param.length, param.size(), etc.
        for (String param : paramNames) {
            if (expr.startsWith(param + ".")) return true;
        }
        return false;
    }

    String invertCondition(BinaryExpr binExpr) {
        String left = binExpr.getLeft().toString();
        String right = binExpr.getRight().toString();

        return switch (binExpr.getOperator()) {
            case LESS -> left + " >= " + right;
            case LESS_EQUALS -> left + " > " + right;
            case GREATER -> left + " <= " + right;
            case GREATER_EQUALS -> left + " < " + right;
            case EQUALS -> left + " != " + right;
            case NOT_EQUALS -> left + " == " + right;
            case OR -> {
                // !(a || b) means neither a nor b
                if (binExpr.getLeft() instanceof BinaryExpr && binExpr.getRight() instanceof BinaryExpr) {
                    String invertedLeft = invertCondition((BinaryExpr) binExpr.getLeft());
                    String invertedRight = invertCondition((BinaryExpr) binExpr.getRight());
                    yield invertedLeft + " && " + invertedRight;
                }
                yield null;
            }
            default -> null;
        };
    }

    void analyzeNumericConstraints(MethodDeclaration methodDecl, String paramName,
                                    Set<String> preconditions, ASTCollector collector) {
        collector.binaryExprs.stream()
            .filter(expr -> expr.getLeft().toString().equals(paramName) || expr.getRight().toString().equals(paramName))
            .filter(expr -> !isBranchingIfCondition(expr)) // Skip comparisons in if/else branching logic
            .filter(expr -> !isGuardThrowCondition(expr)) // Skip if-throw guards (handled by analyzeEarlyValidation)
            .forEach(expr -> {
                if (expr.getOperator() == BinaryExpr.Operator.GREATER && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " > " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.GREATER_EQUALS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " >= " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.LESS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " < " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.LESS_EQUALS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " <= " + expr.getRight());
                }
            });
    }

    boolean isBranchingIfCondition(Expression expr) {
        com.github.javaparser.ast.Node current = expr;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) parent;
                if (current == ifStmt.getCondition()) {
                    // Only filter if both branches are handled (has else)
                    return ifStmt.getElseStmt().isPresent();
                }
            }
            // Ternary condition is branching logic, not a precondition
            if (parent instanceof ConditionalExpr) {
                ConditionalExpr ternary = (ConditionalExpr) parent;
                if (current == ternary.getCondition()) {
                    return true;
                }
            }
            // Also check if embedded inside a larger condition (e.g., x > 0 && y > 0)
            if (parent instanceof BinaryExpr) {
                BinaryExpr parentBin = (BinaryExpr) parent;
                if (parentBin.getOperator() == BinaryExpr.Operator.AND ||
                    parentBin.getOperator() == BinaryExpr.Operator.OR) {
                    current = parent;
                    continue;
                }
            }
            break;
        }
        return false;
    }

    boolean isGuardThrowCondition(Expression expr) {
        com.github.javaparser.ast.Node current = expr;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) parent;
                if (current == ifStmt.getCondition()) {
                    // if-throw: handled by analyzeEarlyValidation
                    if (!ifStmt.getThenStmt().findAll(ThrowStmt.class).isEmpty()) {
                        return true;
                    }
                    // if-return without else: guard clause, method handles both paths
                    if (!ifStmt.getElseStmt().isPresent() &&
                        !ifStmt.getThenStmt().findAll(ReturnStmt.class).isEmpty()) {
                        return true;
                    }
                    return false;
                }
            }
            if (parent instanceof BinaryExpr) {
                BinaryExpr parentBin = (BinaryExpr) parent;
                if (parentBin.getOperator() == BinaryExpr.Operator.AND ||
                    parentBin.getOperator() == BinaryExpr.Operator.OR) {
                    current = parent;
                    continue;
                }
            }
            break;
        }
        return false;
    }

    /**
     * Visitor to detect null checks in the method body.
     */
    static class NullCheckVisitor extends VoidVisitorAdapter<Void> {
        private final Set<String> nullChecks = new LinkedHashSet<>();

        @Override
        public void visit(IfStmt ifStmt, Void arg) {
            ifStmt.getCondition().ifBinaryExpr(binExpr -> {
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS &&
                    (binExpr.getRight().isNullLiteralExpr() || binExpr.getLeft().isNullLiteralExpr())) {
                    Expression nonNullExpr = binExpr.getRight().isNullLiteralExpr() ? binExpr.getLeft() : binExpr.getRight();
                    nullChecks.add(nonNullExpr.toString() + " != null");
                } else if (binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS &&
                          (binExpr.getRight().isNullLiteralExpr() || binExpr.getLeft().isNullLiteralExpr())) {
                    Expression nonNullExpr = binExpr.getRight().isNullLiteralExpr() ? binExpr.getLeft() : binExpr.getRight();
                    nullChecks.add(nonNullExpr.toString() + " != null");
                }
            });
            super.visit(ifStmt, arg);
        }

        public Set<String> getNullChecks() {
            return nullChecks;
        }
    }
}
