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
                if (methodName.equals("abs") || methodName.equals("length") ||
                    methodName.equals("size") || methodName.equals("count")) {
                    // These guarantee >= 0 but NOT > 0 (abs(0)==0, "".length()==0)
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                } else {
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                }
            } else if (expr instanceof BinaryExpr) {
                BinaryExpr binExpr = (BinaryExpr) expr;
                if (binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY && AnalysisUtils.isSelfMultiplication(binExpr)) {
                    // x * x is always non-negative; keep allReturnsNonNegative true
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
                           involvesRecursiveCall(binExpr, methodDecl)) {
                    // Recursive addition (e.g., fib(n-1) + fib(n-2)):
                    // if the recursive call preserves non-negativity, sum is also non-negative
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
                    if (resolved != null && AnalysisUtils.isSelfMultiplication(resolved)) {
                        // resolved to x * x → non-negative
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
                        if (returnedParams.size() <= 1 && returnStmts.size() == 1) {
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

        // Check if all results resolve to the same expression — emit single unconditional spec
        String firstExpr = results.get(0).resolvedExpr;
        boolean allSame = results.stream().allMatch(r -> r.resolvedExpr.equals(firstExpr));

        if (allSame && results.size() > 1) {
            // All paths return the same expression — treat as unconditional
            if (AnalysisUtils.isTrivialResult(firstExpr)) return;
            if (firstExpr.length() > 100) return;
            postconditions.add(AnalysisUtils.buildResultEquality(firstExpr));
            return;
        }

        for (SymbolicExecutor.SymbolicReturn sr : results) {
            if (AnalysisUtils.isTrivialResult(sr.resolvedExpr)) continue;

            if (sr.pathCondition == null) {
                // Unconditional
                if (sr.resolvedExpr.length() > 100) continue;
                postconditions.add(AnalysisUtils.buildResultEquality(sr.resolvedExpr));
            } else {
                // Conditional
                if (sr.resolvedExpr.length() > 100) continue;
                if (sr.pathCondition.length() > 80) continue;
                postconditions.add(sr.pathCondition + " ==> " + AnalysisUtils.buildResultEquality(sr.resolvedExpr));
            }
        }
    }

    void analyzeConditionalReturns(MethodDeclaration methodDecl, Set<String> postconditions,
                                    ASTCollector collector) {
        if (!methodDecl.getBody().isPresent()) return;

        // Analyze if/else statements with return in both branches
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

            // Case 1: Both branches return literals -> disjunctive postcondition
            if (isLiteralOrNegativeLiteral(thenExpr) && isLiteralOrNegativeLiteral(elseExpr)) {
                String thenStr = thenExpr.toString();
                String elseStr = elseExpr.toString();
                postconditions.add(AnalysisUtils.buildResultEquality(thenStr) + " || " + AnalysisUtils.buildResultEquality(elseStr));
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
                        postconditions.add(AnalysisUtils.buildResultEquality(thenStr) + " || " + AnalysisUtils.buildResultEquality(elseStr));
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

    boolean involvesRecursiveCall(BinaryExpr binExpr, MethodDeclaration methodDecl) {
        String methodName = methodDecl.getNameAsString();
        return containsRecursiveCall(binExpr.getLeft(), methodName) ||
               containsRecursiveCall(binExpr.getRight(), methodName);
    }

    boolean containsRecursiveCall(Expression expr, String methodName) {
        if (expr instanceof MethodCallExpr) {
            return ((MethodCallExpr) expr).getNameAsString().equals(methodName);
        }
        return expr.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getNameAsString().equals(methodName));
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
