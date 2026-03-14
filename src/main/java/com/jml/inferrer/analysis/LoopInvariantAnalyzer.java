package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Infers loop invariants by analyzing loop structures.
 */
class LoopInvariantAnalyzer {

    void inferLoopInvariants(MethodDeclaration methodDecl, MethodSpecification spec) {
        LoopInvariantVisitor loopVisitor = new LoopInvariantVisitor();
        methodDecl.accept(loopVisitor, null);
        loopVisitor.getInvariants().forEach(spec::addLoopInvariant);
    }

    /**
     * Visitor to analyze loops and infer loop invariants.
     */
    static class LoopInvariantVisitor extends VoidVisitorAdapter<Void> {
        private final Set<String> invariants = new LinkedHashSet<>();

        @Override
        public void visit(ForStmt forStmt, Void arg) {
            analyzeForLoop(forStmt);
            super.visit(forStmt, arg);
        }

        @Override
        public void visit(WhileStmt whileStmt, Void arg) {
            analyzeWhileLoop(whileStmt);
            super.visit(whileStmt, arg);
        }

        @Override
        public void visit(ForEachStmt forEachStmt, Void arg) {
            analyzeForEachLoop(forEachStmt);
            super.visit(forEachStmt, arg);
        }

        private void analyzeForLoop(ForStmt forStmt) {
            List<String> counterNames = new ArrayList<>();
            List<Expression> initValues = new ArrayList<>();

            forStmt.getInitialization().stream()
                .filter(expr -> expr instanceof VariableDeclarationExpr)
                .forEach(expr -> {
                    VariableDeclarationExpr varDecl = (VariableDeclarationExpr) expr;
                    varDecl.getVariables().forEach(var -> {
                        String varName = var.getNameAsString();
                        counterNames.add(varName);
                        var.getInitializer().ifPresent(initValues::add);

                        var.getInitializer().ifPresent(init -> {
                            if (init.isIntegerLiteralExpr()) {
                                int initVal = init.asIntegerLiteralExpr().asInt();
                                invariants.add(varName + " >= " + initVal);
                            } else {
                                invariants.add(varName + " >= 0");
                            }
                        });

                        forStmt.getCompare().ifPresent(compare -> {
                            if (compare instanceof BinaryExpr) {
                                BinaryExpr binExpr = (BinaryExpr) compare;
                                if (binExpr.getLeft().toString().equals(varName)) {
                                    invariants.add(varName + " " + getWeakenedOperatorForInvariant(binExpr.getOperator()) + " " + binExpr.getRight());
                                }
                            }
                        });

                        forStmt.getUpdate().forEach(updateExpr -> {
                            int stepSize = getStepSize(updateExpr, varName);
                            if (stepSize > 1) {
                                invariants.add(varName + " % " + stepSize + " == 0");
                            } else if (stepSize < 0) {
                                forStmt.getCompare().ifPresent(compare -> {
                                    if (compare instanceof BinaryExpr) {
                                        BinaryExpr binExpr = (BinaryExpr) compare;
                                        if (binExpr.getLeft().toString().equals(varName)) {
                                            String lowerBound = binExpr.getRight().toString();
                                            invariants.add(varName + " >= " + lowerBound);
                                        }
                                    }
                                });
                            }
                        });
                    });
                });

            if (counterNames.size() == 2) {
                String counter1 = counterNames.get(0);
                String counter2 = counterNames.get(1);

                if (initValues.size() == 2) {
                    try {
                        int init1 = getIntValue(initValues.get(0));
                        int init2 = getIntValue(initValues.get(1));
                        int sum = init1 + init2;

                        boolean oppositeUpdates = checkOppositeUpdates(forStmt, counter1, counter2);
                        if (oppositeUpdates) {
                            invariants.add(counter1 + " + " + counter2 + " == " + sum);
                        }
                    } catch (Exception e) {
                        // Couldn't determine constant sum
                    }
                }
            }

            analyzeAccumulators(forStmt.getBody(), invariants, counterNames);
            analyzeArraySegments(forStmt, invariants, counterNames);
            analyzeQuantifiedInvariants(forStmt, invariants, counterNames);
            analyzeVariableRelationships(forStmt.getBody(), invariants);
            analyzeLoopBodyForInvariants(forStmt.getBody(), invariants);
        }

        private int getStepSize(Expression updateExpr, String varName) {
            if (updateExpr instanceof UnaryExpr) {
                UnaryExpr unaryExpr = (UnaryExpr) updateExpr;
                if (unaryExpr.getExpression().toString().equals(varName)) {
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                        unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT) {
                        return 1;
                    } else if (unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT ||
                              unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) {
                        return -1;
                    }
                }
            } else if (updateExpr instanceof AssignExpr) {
                AssignExpr assignExpr = (AssignExpr) updateExpr;
                if (assignExpr.getTarget().toString().equals(varName)) {
                    Expression value = assignExpr.getValue();
                    if (value instanceof BinaryExpr) {
                        BinaryExpr binExpr = (BinaryExpr) value;
                        if (binExpr.getLeft().toString().equals(varName)) {
                            if (binExpr.getOperator() == BinaryExpr.Operator.PLUS) {
                                try {
                                    return getIntValue(binExpr.getRight());
                                } catch (Exception e) {
                                    return 1;
                                }
                            } else if (binExpr.getOperator() == BinaryExpr.Operator.MINUS) {
                                try {
                                    return -getIntValue(binExpr.getRight());
                                } catch (Exception e) {
                                    return -1;
                                }
                            }
                        }
                    }
                }
            }
            return 1;
        }

        private int getIntValue(Expression expr) {
            if (expr.isIntegerLiteralExpr()) {
                return expr.asIntegerLiteralExpr().asInt();
            }
            throw new IllegalArgumentException("Not an integer literal");
        }

        private boolean checkOppositeUpdates(ForStmt forStmt, String counter1, String counter2) {
            int[] steps = new int[2];
            int index = 0;

            for (Expression updateExpr : forStmt.getUpdate()) {
                if (index < 2) {
                    if (updateExpr.toString().contains(counter1)) {
                        steps[0] = getStepSize(updateExpr, counter1);
                    } else if (updateExpr.toString().contains(counter2)) {
                        steps[1] = getStepSize(updateExpr, counter2);
                    }
                    index++;
                }
            }

            return (steps[0] > 0 && steps[1] < 0) || (steps[0] < 0 && steps[1] > 0);
        }

        private void analyzeAccumulators(Statement body, Set<String> invariants, List<String> counterNames) {
            body.findAll(AssignExpr.class).forEach(assign -> {
                if (assign.getTarget() instanceof NameExpr) {
                    String varName = assign.getTarget().toString();

                    if (!counterNames.contains(varName)) {
                        Expression value = assign.getValue();

                        if (value instanceof BinaryExpr) {
                            BinaryExpr binExpr = (BinaryExpr) value;

                            if (binExpr.getLeft().toString().equals(varName) &&
                                binExpr.getOperator() == BinaryExpr.Operator.PLUS) {
                                invariants.add(varName + " >= 0");

                                if (!counterNames.isEmpty()) {
                                    String counter = counterNames.get(0);
                                    invariants.add(varName + " <= " + counter + " * Integer.MAX_VALUE");
                                }
                            }

                            if (binExpr.getOperator() == BinaryExpr.Operator.PLUS &&
                                binExpr.getRight().isIntegerLiteralExpr() &&
                                binExpr.getRight().asIntegerLiteralExpr().asInt() == 1) {

                                if (!counterNames.isEmpty()) {
                                    String counter = counterNames.get(0);
                                    invariants.add(varName + " >= 0");
                                    invariants.add(varName + " <= " + counter);
                                }
                            }
                        }
                    }
                }
            });
        }

        private void analyzeArraySegments(ForStmt forStmt, Set<String> invariants, List<String> counterNames) {
            if (counterNames.isEmpty()) return;
            String counter = counterNames.get(0);

            Statement body = forStmt.getBody();

            List<AssignExpr> arrayWrites = body.findAll(AssignExpr.class).stream()
                    .filter(assign -> assign.getTarget() instanceof ArrayAccessExpr)
                    .toList();

            if (!arrayWrites.isEmpty()) {
                ArrayAccessExpr firstWrite = (ArrayAccessExpr) arrayWrites.get(0).getTarget();
                String arrayName = firstWrite.getName().toString();
                String index = firstWrite.getIndex().toString();

                boolean allWritesToCounter = arrayWrites.stream()
                        .allMatch(assign -> {
                            if (assign.getTarget() instanceof ArrayAccessExpr) {
                                ArrayAccessExpr aae = (ArrayAccessExpr) assign.getTarget();
                                return aae.getIndex().toString().equals(counter);
                            }
                            return false;
                        });

                if (allWritesToCounter && index.equals(counter)) {
                    Expression firstValue = arrayWrites.get(0).getValue();
                    boolean allSameValue = arrayWrites.stream()
                            .allMatch(assign -> assign.getValue().toString().equals(firstValue.toString()));

                    if (allSameValue) {
                        if (firstValue.isLiteralExpr() || firstValue.isNameExpr()) {
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == " + firstValue + ")");
                        }
                    }
                }

                boolean hasSwap = body.findAll(MethodCallExpr.class).stream()
                        .anyMatch(call -> call.getNameAsString().equals("swap"));
            }
        }

        private void analyzeQuantifiedInvariants(ForStmt forStmt, Set<String> invariants, List<String> counterNames) {
            if (counterNames.isEmpty()) return;
            String counter = counterNames.get(0);

            Statement body = forStmt.getBody();

            body.findAll(AssignExpr.class).forEach(assign -> {
                if (assign.getTarget() instanceof ArrayAccessExpr) {
                    ArrayAccessExpr arrayAccess = (ArrayAccessExpr) assign.getTarget();
                    String arrayName = arrayAccess.getName().toString();
                    String index = arrayAccess.getIndex().toString();

                    if (index.equals(counter)) {
                        Expression value = assign.getValue();

                        if (value.isIntegerLiteralExpr() && value.asIntegerLiteralExpr().asInt() == 0) {
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == 0)");
                        } else if (value.isNullLiteralExpr()) {
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == null)");
                        } else if (value.isBooleanLiteralExpr()) {
                            boolean boolVal = value.asBooleanLiteralExpr().getValue();
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == " + boolVal + ")");
                        }
                    }
                }
            });

            body.findAll(IfStmt.class).forEach(ifStmt -> {
                ifStmt.getThenStmt().findAll(UnaryExpr.class).forEach(unaryExpr -> {
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                        unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT) {

                        String countVar = unaryExpr.getExpression().toString();
                        if (!counterNames.contains(countVar)) {
                            String condition = ifStmt.getCondition().toString();
                            String replacedCondition = condition.replaceAll(
                                    "\\b" + java.util.regex.Pattern.quote(counter) + "\\b", "k");
                            invariants.add("(\\num_of int k; 0 <= k < " + counter + "; " +
                                          replacedCondition + ") == " + countVar);
                        }
                    }
                });
            });
        }

        private void analyzeVariableRelationships(Statement body, Set<String> invariants) {
            body.findAll(IfStmt.class).forEach(ifStmt -> {
                Expression condition = ifStmt.getCondition();

                if (condition instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) condition;

                    if (binExpr.getOperator() == BinaryExpr.Operator.GREATER) {
                        String leftVar = binExpr.getLeft().toString();
                        String rightVar = binExpr.getRight().toString();
                        // Skip: natural language invariants are not valid JML
                    } else if (binExpr.getOperator() == BinaryExpr.Operator.LESS) {
                        String leftVar = binExpr.getLeft().toString();
                        String rightVar = binExpr.getRight().toString();
                        // Skip: natural language invariants are not valid JML
                    }
                }
            });
        }

        private void analyzeWhileLoop(WhileStmt whileStmt) {
            Expression condition = whileStmt.getCondition();
            Statement body = whileStmt.getBody();

            List<String> counterNames = detectCountersInBody(body);

            if (condition instanceof BinaryExpr) {
                BinaryExpr binExpr = (BinaryExpr) condition;

                if (!counterNames.isEmpty()) {
                    String left = binExpr.getLeft().toString();
                    String right = binExpr.getRight().toString();
                    if (counterNames.contains(left)) {
                        invariants.add(left + " " + getWeakenedOperatorForInvariant(binExpr.getOperator()) + " " + right);
                        invariants.add(left + " >= 0");
                    } else if (counterNames.contains(right)) {
                        invariants.add(right + " >= 0");
                    }
                }
            } else if (condition instanceof MethodCallExpr) {
                MethodCallExpr call = (MethodCallExpr) condition;
                call.getScope().ifPresent(scope ->
                    invariants.add(scope + " != null"));
            }

            analyzeAccumulators(body, invariants, counterNames);
            analyzeVariableRelationships(body, invariants);
            analyzeLoopBodyForInvariants(body, invariants);
        }

        private List<String> detectCountersInBody(Statement body) {
            List<String> counters = new ArrayList<>();

            body.findAll(UnaryExpr.class).forEach(unary -> {
                if (unary.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT ||
                    unary.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) {
                    String varName = unary.getExpression().toString();
                    if (!counters.contains(varName)) {
                        counters.add(varName);
                    }
                }
            });

            body.findAll(AssignExpr.class).forEach(assign -> {
                if (assign.getOperator() == AssignExpr.Operator.PLUS ||
                    assign.getOperator() == AssignExpr.Operator.MINUS) {
                    String varName = assign.getTarget().toString();
                    if (!counters.contains(varName)) {
                        counters.add(varName);
                    }
                }
            });

            return counters;
        }

        private void analyzeForEachLoop(ForEachStmt forEachStmt) {
            String iterableName = forEachStmt.getIterable().toString();

            invariants.add(iterableName + " != null");

            analyzeVariableRelationships(forEachStmt.getBody(), invariants);
            analyzeLoopBodyForInvariants(forEachStmt.getBody(), invariants);
        }

        private void analyzeLoopBodyForInvariants(Statement body, Set<String> invariants) {
            body.findAll(AssignExpr.class).stream()
                .filter(assign -> assign.getTarget() instanceof NameExpr)
                .forEach(assign -> {
                    String varName = assign.getTarget().toString();
                    if (assign.getValue() instanceof BinaryExpr) {
                        BinaryExpr binExpr = (BinaryExpr) assign.getValue();
                        if (binExpr.getOperator() == BinaryExpr.Operator.PLUS ||
                            binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                            invariants.add(varName + " >= 0");
                        }
                    }
                });
        }

        private String getOperatorSymbol(BinaryExpr.Operator operator) {
            return switch (operator) {
                case LESS -> "<";
                case LESS_EQUALS -> "<=";
                case GREATER -> ">";
                case GREATER_EQUALS -> ">=";
                case EQUALS -> "==";
                case NOT_EQUALS -> "!=";
                default -> operator.asString();
            };
        }

        private String getWeakenedOperatorForInvariant(BinaryExpr.Operator operator) {
            return switch (operator) {
                case LESS -> "<=";
                case GREATER -> ">=";
                case LESS_EQUALS -> "<=";
                case GREATER_EQUALS -> ">=";
                default -> getOperatorSymbol(operator);
            };
        }

        public Set<String> getInvariants() {
            return invariants;
        }
    }
}
