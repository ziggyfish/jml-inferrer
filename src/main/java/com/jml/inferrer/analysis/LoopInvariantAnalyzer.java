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
        loopVisitor.getInvariantsByOrdinal().forEach((ordinal, invs) ->
                invs.forEach(inv -> spec.addLoopInvariant(inv, ordinal)));
    }

    /**
     * Visitor to analyze loops and infer loop invariants.
     *
     * Each loop visited gets a sequential ordinal in document order (0, 1, 2, ...).
     * Invariants are tagged with the ordinal of the loop being visited at the time of
     * emission so the converter can place them above the matching loop without depending
     * on source line numbers (which shift when annotations are injected into the source).
     */
    static class LoopInvariantVisitor extends VoidVisitorAdapter<Void> {
        // Insertion-ordered map: loop ordinal -> invariants emitted for that loop.
        private final Map<Integer, List<String>> invariantsByOrdinal = new LinkedHashMap<>();
        private int currentLoopOrdinal = 0;
        private int loopCounter = 0;

        public Map<Integer, List<String>> getInvariantsByOrdinal() {
            return invariantsByOrdinal;
        }

        // Backed by a shadow set to keep dedup semantics; routes additions to the bucket
        // for whichever loop is currently being analysed.
        private final Set<String> seen = new LinkedHashSet<>();
        private final Set<String> invariants = new java.util.AbstractSet<String>() {
            @Override public boolean add(String s) {
                if (!seen.add(s)) return false;
                invariantsByOrdinal.computeIfAbsent(currentLoopOrdinal, k -> new ArrayList<>()).add(s);
                return true;
            }
            @Override public java.util.Iterator<String> iterator() { return seen.iterator(); }
            @Override public int size() { return seen.size(); }
            @Override public boolean contains(Object o) { return seen.contains(o); }
        };

        @Override
        public void visit(ForStmt forStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeForLoop(forStmt);
            super.visit(forStmt, arg);
            currentLoopOrdinal = prev;
        }

        @Override
        public void visit(WhileStmt whileStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeWhileLoop(whileStmt);
            super.visit(whileStmt, arg);
            currentLoopOrdinal = prev;
        }

        @Override
        public void visit(ForEachStmt forEachStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeForEachLoop(forEachStmt);
            super.visit(forEachStmt, arg);
            currentLoopOrdinal = prev;
        }

        @Override
        public void visit(DoStmt doStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeDoWhileLoop(doStmt);
            super.visit(doStmt, arg);
            currentLoopOrdinal = prev;
        }

        private void analyzeDoWhileLoop(DoStmt doStmt) {
            // Treat the do-while body the same way as while: same guard, same monotonic-counter
            // detection. The only semantic difference (body always runs at least once) does not
            // affect `counter >= 0` invariants that hold trivially on entry.
            Statement body = doStmt.getBody();
            Expression condition = doStmt.getCondition();

            List<String> counterNames = detectCountersInBody(body);

            for (Expression conjunct : flattenAndConjuncts(condition)) {
                if (conjunct instanceof BinaryExpr binExpr) {
                    if (counterNames.isEmpty()) continue;
                    String left = binExpr.getLeft().toString();
                    String right = binExpr.getRight().toString();
                    if (counterNames.contains(left)) {
                        invariants.add(left + " " + getWeakenedOperatorForInvariant(binExpr.getOperator()) + " " + right);
                        invariants.add(left + " >= 0");
                    } else if (counterNames.contains(right)) {
                        invariants.add(right + " >= 0");
                    }
                }
            }
            for (String counter : findMonotonicNonNegativeCounters(doStmt, body)) {
                invariants.add(counter + " >= 0");
            }

            analyzeAccumulators(body, invariants, counterNames);
            analyzeVariableRelationships(body, invariants);
            analyzeLoopBodyForInvariants(body, invariants);
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

            // Decompose `cond1 && cond2 && ...` into individual conjuncts so each numeric
            // condition gets a chance to contribute its own invariant.
            for (Expression conjunct : flattenAndConjuncts(condition)) {
                if (conjunct instanceof BinaryExpr binExpr) {
                    if (counterNames.isEmpty()) continue;
                    String left = binExpr.getLeft().toString();
                    String right = binExpr.getRight().toString();
                    if (counterNames.contains(left)) {
                        invariants.add(left + " " + getWeakenedOperatorForInvariant(binExpr.getOperator()) + " " + right);
                        invariants.add(left + " >= 0");
                    } else if (counterNames.contains(right)) {
                        invariants.add(right + " >= 0");
                    }
                } else if (conjunct instanceof MethodCallExpr call) {
                    call.getScope().ifPresent(scope -> invariants.add(scope + " != null"));
                }
            }

            // Independent of the guard shape: if a counter starts at 0 and is only ever
            // incremented (++ / += literal), then `counter >= 0` is sound throughout the loop.
            // This catches the common `count++` pattern even when the guard isn't of the form
            // `counter <op> something`.
            for (String counter : findMonotonicNonNegativeCounters(whileStmt, body)) {
                invariants.add(counter + " >= 0");
            }

            analyzeAccumulators(body, invariants, counterNames);
            analyzeVariableRelationships(body, invariants);
            analyzeLoopBodyForInvariants(body, invariants);
        }

        /**
         * Returns every operand of a chain of {@code &&} expressions, or the expression
         * itself if it isn't a top-level {@code &&}. Conservative: doesn't flatten {@code ||}.
         */
        private List<Expression> flattenAndConjuncts(Expression expr) {
            List<Expression> out = new ArrayList<>();
            if (expr instanceof BinaryExpr be && be.getOperator() == BinaryExpr.Operator.AND) {
                out.addAll(flattenAndConjuncts(be.getLeft()));
                out.addAll(flattenAndConjuncts(be.getRight()));
            } else {
                out.add(expr);
            }
            return out;
        }

        /**
         * Identifies counters that (a) are declared with a non-negative integer-literal
         * initializer immediately before the loop, AND (b) are only ever modified inside
         * the loop body by {@code ++} or {@code += positiveLiteral}.
         *
         * For these, {@code counter >= initialValue >= 0} is sound at every iteration:
         * non-negative on entry and a non-negative-preserving update.
         *
         * Soundness gate: any other write (including plain {@code =}, {@code -=},
         * {@code *=}, etc.) disqualifies the counter.
         */
        private List<String> findMonotonicNonNegativeCounters(com.github.javaparser.ast.Node loopNode, Statement body) {
            List<String> result = new ArrayList<>();

            // Pull all candidate-counter names from the body (++ / +=)
            Set<String> bodyCounters = new LinkedHashSet<>();
            body.findAll(UnaryExpr.class).forEach(u -> {
                if (u.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT) {
                    if (u.getExpression() instanceof NameExpr ne) bodyCounters.add(ne.getNameAsString());
                }
            });
            body.findAll(AssignExpr.class).forEach(a -> {
                if (a.getOperator() == AssignExpr.Operator.PLUS
                        && a.getTarget() instanceof NameExpr ne) {
                    bodyCounters.add(ne.getNameAsString());
                }
            });

            outer:
            for (String name : bodyCounters) {
                // Find the most recent declaration of `name` in the enclosing method,
                // require non-negative integer literal initialiser.
                Optional<MethodDeclaration> methodOpt = loopNode.findAncestor(MethodDeclaration.class);
                if (methodOpt.isEmpty()) continue;
                MethodDeclaration method = methodOpt.get();

                Expression init = null;
                for (com.github.javaparser.ast.body.VariableDeclarator vd
                        : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                    if (vd.getNameAsString().equals(name) && vd.getInitializer().isPresent()) {
                        init = vd.getInitializer().get();
                    }
                }
                if (init == null) continue;
                if (!init.isIntegerLiteralExpr()) continue;
                if (init.asIntegerLiteralExpr().asInt() < 0) continue;

                // Verify ALL writes to `name` in the method are either:
                // - the initialiser declaration itself (already non-negative)
                // - inside this loop's body and of the monotonic kind
                for (AssignExpr a : method.findAll(AssignExpr.class)) {
                    if (!(a.getTarget() instanceof NameExpr targ) || !targ.getNameAsString().equals(name)) continue;
                    if (!isInsideStatement(a, body)) continue outer; // write outside this loop body — bail
                    if (a.getOperator() != AssignExpr.Operator.PLUS) continue outer;
                    Expression rhs = a.getValue();
                    // RHS must be a non-negative integer literal (sound under bounded arithmetic
                    // only when overflow is excluded — but `count >= 0` is the inferred invariant
                    // and overflow would invalidate it; we leave proof of overflow-freedom to OpenJML).
                    if (!(rhs.isIntegerLiteralExpr() && rhs.asIntegerLiteralExpr().asInt() >= 0)) continue outer;
                }
                for (UnaryExpr u : method.findAll(UnaryExpr.class)) {
                    if (!(u.getExpression() instanceof NameExpr ne) || !ne.getNameAsString().equals(name)) continue;
                    if (!isInsideStatement(u, body)) continue outer;
                    if (u.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                            && u.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) continue outer;
                }
                result.add(name);
            }
            return result;
        }

        private boolean isInsideStatement(com.github.javaparser.ast.Node node, Statement container) {
            com.github.javaparser.ast.Node n = node;
            while (n.getParentNode().isPresent()) {
                n = n.getParentNode().get();
                if (n == container) return true;
            }
            return false;
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

    }
}
