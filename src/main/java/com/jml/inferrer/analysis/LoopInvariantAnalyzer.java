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
        LoopInvariantVisitor loopVisitor = new LoopInvariantVisitor(spec);
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
        private final MethodSpecification spec;

        LoopInvariantVisitor() { this(null); }

        LoopInvariantVisitor(MethodSpecification spec) {
            this.spec = spec;
        }

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
            ensureAtLeastOneInvariant(forStmt.getBody());
            currentLoopOrdinal = prev;
        }

        @Override
        public void visit(WhileStmt whileStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeWhileLoop(whileStmt);
            super.visit(whileStmt, arg);
            ensureAtLeastOneInvariant(whileStmt.getBody());
            currentLoopOrdinal = prev;
        }

        @Override
        public void visit(ForEachStmt forEachStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeForEachLoop(forEachStmt);
            super.visit(forEachStmt, arg);
            ensureAtLeastOneInvariant(forEachStmt.getBody());
            currentLoopOrdinal = prev;
        }

        @Override
        public void visit(DoStmt doStmt, Void arg) {
            int prev = currentLoopOrdinal;
            currentLoopOrdinal = loopCounter++;
            analyzeDoWhileLoop(doStmt);
            super.visit(doStmt, arg);
            ensureAtLeastOneInvariant(doStmt.getBody());
            currentLoopOrdinal = prev;
        }

        /**
         * Guarantees at least one loop_invariant per loop. Tries in order:
         *   1. Method preconditions whose free variables are NOT modified in the loop body
         *      (trivially preserved → sound invariants).
         *   2. The literal {@code true} as a last-resort placeholder. Always valid JML.
         *
         * No-op when the loop already has at least one invariant from the main analysis.
         */
        private void ensureAtLeastOneInvariant(Statement body) {
            if (invariantsByOrdinal.getOrDefault(currentLoopOrdinal, List.of()).size() > 0) return;

            if (spec != null) {
                Set<String> modified = collectModifiedNames(body);
                for (String precond : spec.getPreconditions()) {
                    if (!referencesAny(precond, modified) && isSafePreconditionForInvariant(precond)) {
                        invariants.add(precond);
                    }
                }
                if (invariantsByOrdinal.getOrDefault(currentLoopOrdinal, List.of()).size() > 0) return;
            }

            invariants.add("true");
        }

        /**
         * Names written to in {@code body} (assignments, compound-assignments, and unary
         * increment/decrement). Used to filter preconditions that wouldn't be preserved.
         */
        private Set<String> collectModifiedNames(Statement body) {
            Set<String> out = new LinkedHashSet<>();
            for (AssignExpr a : body.findAll(AssignExpr.class)) {
                Expression t = a.getTarget();
                if (t instanceof NameExpr ne) out.add(ne.getNameAsString());
                else if (t instanceof FieldAccessExpr fa) out.add(fa.getNameAsString());
                else if (t instanceof ArrayAccessExpr aa) out.add(aa.getName().toString());
            }
            for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
                if (u.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) {
                    if (u.getExpression() instanceof NameExpr ne) out.add(ne.getNameAsString());
                }
            }
            return out;
        }

        private boolean referencesAny(String precond, Set<String> names) {
            for (String n : names) {
                if (precond.matches(".*\\b" + java.util.regex.Pattern.quote(n) + "\\b.*")) return true;
            }
            return false;
        }

        /**
         * Keeps precondition-as-invariant propagation conservative: skip anything mentioning
         * JML-only identifiers (\old, \result, \forall, etc.) since those have meanings that
         * don't necessarily carry over into a loop_invariant context.
         */
        private boolean isSafePreconditionForInvariant(String precond) {
            return !precond.contains("\\old") && !precond.contains("\\result")
                    && !precond.contains("\\forall") && !precond.contains("\\exists");
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
                            int[] stepBox = new int[]{0};
                            forStmt.getUpdate().forEach(u -> {
                                int s = getStepSize(u, varName);
                                if (s != 0) stepBox[0] = s;
                            });
                            int step = stepBox[0];

                            if (init.isIntegerLiteralExpr()) {
                                int initVal = init.asIntegerLiteralExpr().asInt();
                                // Bound direction depends on step: incrementing loops
                                // preserve `var >= init`; decrementing loops preserve
                                // `var <= init`.
                                if (step >= 0) {
                                    invariants.add(varName + " >= " + initVal);
                                } else {
                                    invariants.add(varName + " <= " + initVal);
                                }
                            } else {
                                // For non-literal initializers (e.g. `i = start`), only the
                                // initializer expression itself is sound — and only as a
                                // lower bound when the loop INCREMENTS, or upper bound when
                                // it DECREMENTS.
                                MethodDeclaration encMethod = forStmt
                                        .findAncestor(MethodDeclaration.class).orElse(null);
                                if (encMethod != null
                                        && isPreStateExpressible(init.toString(), encMethod)) {
                                    if (step > 0) {
                                        invariants.add(varName + " >= " + init.toString());
                                    } else if (step < 0) {
                                        invariants.add(varName + " <= " + init.toString());
                                    }
                                } else if (step >= 0 && isStructurallyNonNegative(init, forStmt)) {
                                    // The init isn't pre-state-expressible (e.g. `j = i + 1`
                                    // where `i` is an outer loop var) but is structurally
                                    // non-negative — `>= 0` remains a sound, useful bound.
                                    invariants.add(varName + " >= 0");
                                }
                            }
                        });

                        // Compute the step size for this counter — needed both for a
                        // modulo invariant and for widening the exit-state upper bound when
                        // the step is > 1 (e.g., `i += 2` can overshoot `n` by 1).
                        int[] stepSizeBox = new int[]{0};
                        forStmt.getUpdate().forEach(updateExpr -> {
                            int ss = getStepSize(updateExpr, varName);
                            if (ss != 0) stepSizeBox[0] = ss;
                        });
                        final int stepSize = stepSizeBox[0];

                        forStmt.getCompare().ifPresent(compare -> {
                            if (compare instanceof BinaryExpr) {
                                BinaryExpr binExpr = (BinaryExpr) compare;
                                if (binExpr.getLeft().toString().equals(varName)) {
                                    BinaryExpr.Operator rawOp = binExpr.getOperator();
                                    String op = getWeakenedOperatorForInvariant(rawOp);
                                    String rhs = binExpr.getRight().toString();
                                    // For an increment loop the back-edge value of the counter
                                    // overshoots the boundary by one final step. When the
                                    // original comparator is `<` the weakening to `<=` already
                                    // absorbs one step; when it is `<=` we must widen by one
                                    // more step. For step > 1 either case can overshoot by up
                                    // to (step - 1) or (step) respectively.
                                    //
                                    // `for(i = 1; i <= n; i++)` → back-edge i = n + 1, so the
                                    // sound upper bound is `i <= n + 1`, not `i <= n`.
                                    if (stepSize >= 1) {
                                        int widen = 0;
                                        if (rawOp == BinaryExpr.Operator.LESS) {
                                            widen = stepSize - 1;
                                        } else if (rawOp == BinaryExpr.Operator.LESS_EQUALS) {
                                            widen = stepSize;
                                        }
                                        if (widen > 0) {
                                            rhs = "(" + rhs + " + " + widen + ")";
                                        }
                                    }
                                    // Emit the precondition FIRST. If we couldn't anchor the
                                    // invariant to a pre-state predicate (e.g. init is a local
                                    // like `s.length()` that we can't express in `requires`),
                                    // the invariant may fail at loop entry whenever the body
                                    // doesn't execute — skip it in that case.
                                    if (emitCounterBoundPrecondition(forStmt, varName, op, rhs)) {
                                        invariants.add(varName + " " + op + " " + rhs);
                                    }
                                }
                            }
                        });

                        forStmt.getUpdate().forEach(updateExpr -> {
                            int stepSizeLocal = getStepSize(updateExpr, varName);
                            if (stepSizeLocal > 1) {
                                invariants.add(varName + " % " + stepSizeLocal + " == 0");
                            } else if (stepSizeLocal < 0) {
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

            // Decreasing-bounded locals (declared outside, decremented inside) get
            // `local <= init` as a sound invariant. Covers `int right = arr.length - 1`
            // patterns common in two-pointer traversals.
            findMonotonicDecreasingBoundedCounters(forStmt, forStmt.getBody()).forEach((name, init) ->
                    invariants.add(name + " <= " + init));

            analyzeAccumulators(forStmt.getBody(), invariants, counterNames);
            analyzeArraySegments(forStmt, invariants, counterNames);
            analyzeQuantifiedInvariants(forStmt, invariants, counterNames);
            analyzeVariableRelationships(forStmt.getBody(), invariants);
            analyzeLoopBodyForInvariants(forStmt.getBody(), invariants);
            SumInductionAnalyzer.analyze(forStmt, counterNames, invariants);
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
                    AssignExpr.Operator op = assignExpr.getOperator();
                    // Compound: `i += K` / `i -= K` (value is the literal directly)
                    if (op == AssignExpr.Operator.PLUS) {
                        try { return getIntValue(value); } catch (Exception e) { return 1; }
                    } else if (op == AssignExpr.Operator.MINUS) {
                        try { return -getIntValue(value); } catch (Exception e) { return -1; }
                    }
                    // Plain: `i = i + K` / `i = i - K` (value is BinaryExpr)
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
                // Skip assignments that live inside a nested loop — the nested loop will
                // analyse them on its own visit, and mentioning its counters at this
                // outer-loop level would be a scope error.
                if (isInsideNestedLoopOf(assign, body)) return;
                if (assign.getTarget() instanceof NameExpr) {
                    String varName = assign.getTarget().toString();

                    if (!counterNames.contains(varName)) {
                        Expression value = assign.getValue();

                        if (value instanceof BinaryExpr) {
                            BinaryExpr binExpr = (BinaryExpr) value;

                            // `v = v + 1` (count-by-one accumulator) — the only shape we
                            // can reliably bound. Require the LEFT operand to be exactly
                            // `v`; otherwise e.g. `current = 3 * current + 1` (Collatz)
                            // wrongly inferred `current >= 0` and `current <= steps`,
                            // both of which break at the first iteration.
                            if (binExpr.getOperator() == BinaryExpr.Operator.PLUS
                                    && binExpr.getRight().isIntegerLiteralExpr()
                                    && binExpr.getRight().asIntegerLiteralExpr().asInt() == 1
                                    && binExpr.getLeft() instanceof NameExpr lne
                                    && lne.getNameAsString().equals(varName)) {

                                if (!counterNames.isEmpty()
                                        && !persistsAcrossEnclosingLoop(body, varName)) {
                                    String counter = counterNames.get(0);
                                    invariants.add(varName + " >= 0");
                                    invariants.add(varName + " <= " + counter);
                                }
                            }
                        }
                    }
                }
            });
            // Handle `v++` / `++v` pattern — same as `v = v + 1` for invariant purposes.
            // Skip increments that live inside a nested loop: those are the nested loop's
            // business (it will analyse them when visited) and at this outer-loop level
            // the nested counter isn't in scope.
            body.findAll(UnaryExpr.class).forEach(unary -> {
                if (unary.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                        && unary.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) return;
                if (!(unary.getExpression() instanceof NameExpr ne)) return;
                if (isInsideNestedLoopOf(unary, body)) return;
                String varName = ne.getNameAsString();
                if (counterNames.contains(varName)) return;
                if (counterNames.isEmpty()) return;
                if (persistsAcrossEnclosingLoop(body, varName)) return;
                String counter = counterNames.get(0);
                invariants.add(varName + " >= 0");
                invariants.add(varName + " <= " + counter);
            });
        }

        /**
         * True when {@code varName} is declared outside the loop that encloses the
         * current loop's body — meaning the variable persists across iterations of the
         * outer loop and its value isn't bounded by the inner loop's counter alone.
         *
         * Example: `int count = 0; for(i) for(j) count++;` — at the start of outer
         * iteration i=1, count == cols but j == 0, so `count <= j` is false.
         *
         * If there is no enclosing outer loop (the current loop is top-level within
         * the method), the counter bound is safe regardless of where the variable is
         * declared.
         */
        private boolean persistsAcrossEnclosingLoop(Statement body, String varName) {
            com.github.javaparser.ast.Node currentLoop = body.getParentNode().orElse(null);
            if (currentLoop == null) return false;
            com.github.javaparser.ast.Node enclosingLoop = findEnclosingLoop(currentLoop);
            if (enclosingLoop == null) return false;
            return !varDeclaredInside(enclosingLoop, varName);
        }

        private com.github.javaparser.ast.Node findEnclosingLoop(com.github.javaparser.ast.Node node) {
            com.github.javaparser.ast.Node cur = node.getParentNode().orElse(null);
            while (cur != null) {
                if (cur instanceof ForStmt || cur instanceof WhileStmt
                        || cur instanceof DoStmt || cur instanceof ForEachStmt) {
                    return cur;
                }
                cur = cur.getParentNode().orElse(null);
            }
            return null;
        }

        private boolean varDeclaredInside(com.github.javaparser.ast.Node scope, String varName) {
            for (com.github.javaparser.ast.body.VariableDeclarator vd
                    : scope.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                if (vd.getNameAsString().equals(varName)) return true;
            }
            for (ForStmt fs : scope.findAll(ForStmt.class)) {
                for (var init : fs.getInitialization()) {
                    if (init instanceof VariableDeclarationExpr vde) {
                        for (var v : vde.getVariables()) {
                            if (v.getNameAsString().equals(varName)) return true;
                        }
                    }
                }
            }
            return false;
        }

        /**
         * Returns true when {@code node} sits inside a loop that's nested within the
         * given outer loop body — i.e., there's a ForStmt/WhileStmt/DoStmt between
         * {@code node} and {@code outerBody}.
         */
        private boolean isInsideNestedLoopOf(com.github.javaparser.ast.Node node, Statement outerBody) {
            com.github.javaparser.ast.Node cur = node;
            while (cur.getParentNode().isPresent()) {
                com.github.javaparser.ast.Node parent = cur.getParentNode().get();
                if (parent == outerBody) return false;
                if (parent instanceof ForStmt || parent instanceof WhileStmt
                        || parent instanceof DoStmt || parent instanceof ForEachStmt) {
                    return true;
                }
                cur = parent;
            }
            return false;
        }

        /**
         * Returns the initial value of the for-loop counter, expressed as a string
         * suitable for use as the lower bound in a forall quantifier. Returns the
         * literal initializer when the counter is declared in the for's init with a
         * simple expression (integer literal, parameter name, or `.length`);
         * otherwise falls back to {@code "0"} as the safe (but potentially weakening)
         * lower bound.
         */
        private String forallLowerBound(ForStmt forStmt, String counter) {
            for (var init : forStmt.getInitialization()) {
                if (init instanceof VariableDeclarationExpr vde) {
                    for (var v : vde.getVariables()) {
                        if (v.getNameAsString().equals(counter) && v.getInitializer().isPresent()) {
                            Expression e = v.getInitializer().get();
                            if (e.isIntegerLiteralExpr() || e.isNameExpr()
                                    || e instanceof FieldAccessExpr) {
                                return e.toString();
                            }
                        }
                    }
                }
            }
            return "0";
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
                // The "array name" is actually the receiver of the innermost []. For
                // nested writes like `matrix[i][i] = 1`, the target is
                // ArrayAccessExpr(ArrayAccessExpr(matrix, i), i), and firstWrite.getName()
                // is the inner `matrix[i]` expression. A forall over `matrix[i][k]` is
                // unsound: `matrix[i]` depends on the loop counter, so the quantifier
                // ends up claiming something about the current row rather than the
                // pattern actually being written (matrix[j][j] for j < i).
                // Skip when the receiver is itself an ArrayAccessExpr.
                if (firstWrite.getName() instanceof ArrayAccessExpr) {
                    return;
                }
                String arrayName = firstWrite.getName().toString();
                String index = firstWrite.getIndex().toString();

                boolean allWritesToCounter = arrayWrites.stream()
                        .allMatch(assign -> {
                            if (assign.getTarget() instanceof ArrayAccessExpr) {
                                ArrayAccessExpr aae = (ArrayAccessExpr) assign.getTarget();
                                if (aae.getName() instanceof ArrayAccessExpr) return false;
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
                            // Use the for-loop's own init as the forall's lower bound.
                            // `for (int i = start; i < end; i++)` writing arr[i] only
                            // fills arr[start..counter), so the forall lower bound is
                            // `start`, not 0 — otherwise the invariant claims the
                            // elements before `start` are also `value`, which isn't
                            // ensured by the caller.
                            String lowerBound = forallLowerBound(forStmt, counter);
                            invariants.add("(\\forall int k; " + lowerBound
                                    + " <= k && k < " + counter + "; "
                                    + arrayName + "[k] == " + firstValue + ")");
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

            String lowerBound = forallLowerBound(forStmt, counter);
            body.findAll(AssignExpr.class).forEach(assign -> {
                if (assign.getTarget() instanceof ArrayAccessExpr) {
                    ArrayAccessExpr arrayAccess = (ArrayAccessExpr) assign.getTarget();
                    String arrayName = arrayAccess.getName().toString();
                    String index = arrayAccess.getIndex().toString();

                    if (index.equals(counter)) {
                        Expression value = assign.getValue();

                        if (value.isIntegerLiteralExpr() && value.asIntegerLiteralExpr().asInt() == 0) {
                            invariants.add("(\\forall int k; " + lowerBound + " <= k && k < "
                                    + counter + "; " + arrayName + "[k] == 0)");
                        } else if (value.isNullLiteralExpr()) {
                            invariants.add("(\\forall int k; " + lowerBound + " <= k && k < "
                                    + counter + "; " + arrayName + "[k] == null)");
                        } else if (value.isBooleanLiteralExpr()) {
                            boolean boolVal = value.asBooleanLiteralExpr().getValue();
                            invariants.add("(\\forall int k; " + lowerBound + " <= k && k < "
                                    + counter + "; " + arrayName + "[k] == " + boolVal + ")");
                        }
                    }
                }
            });

            // Conditional-counter `if (pred) counter++` is handled by
            // SumInductionAnalyzer with a more general low-bound.  Emitting a
            // second `\num_of` clause here just duplicates the same invariant in
            // slightly different syntax (e.g. `0 <= k < i` vs `0 <= k && k < i`),
            // which clutters every spec without adding information.

            // Universal-so-far pattern: `if (arr[i] <op> const) return <literal>;` inside a
            // for-loop means every already-seen element satisfies the negation of <op>.
            // Emit `(\forall int k; 0 <= k < i; arr[k] !op const)` so OpenJML can prove
            // the matching `\result == \forall …` postcondition at loop exit.
            Set<String> innerLoopCounters = collectInnerLoopCounters(forStmt);
            body.findAll(IfStmt.class).forEach(ifStmt -> {
                if (!alwaysReturnsOrThrows(ifStmt.getThenStmt())) return;
                if (!(ifStmt.getCondition() instanceof BinaryExpr bcond)) return;
                if (!isRelationalOp(bcond.getOperator())) return;
                if (!(bcond.getLeft() instanceof ArrayAccessExpr aae)) return;
                if (!aae.getIndex().toString().equals(counter)) return;
                String arrName = aae.getName().toString();
                String rhs = bcond.getRight().toString();
                // Skip if the RHS references an inner-loop variable — the resulting
                // invariant would bind `k` in a scope where the inner counter isn't
                // visible (or shadows the wrong thing).
                for (String innerCounter : innerLoopCounters) {
                    if (rhs.matches(".*\\b" + java.util.regex.Pattern.quote(innerCounter) + "\\b.*")) return;
                }
                BinaryExpr.Operator negated = negateRelationalOperator(bcond.getOperator());
                if (negated == null) return;
                String opStr = relOpString(negated);
                invariants.add("(\\forall int k; 0 <= k && k < " + counter + "; " +
                        arrName + "[k] " + opStr + " " + rhs + ")");
            });
        }

        private Set<String> collectInnerLoopCounters(ForStmt outer) {
            Set<String> inner = new LinkedHashSet<>();
            for (ForStmt nested : outer.getBody().findAll(ForStmt.class)) {
                if (nested == outer) continue;
                nested.getInitialization().forEach(init -> {
                    if (init instanceof VariableDeclarationExpr vde) {
                        vde.getVariables().forEach(v -> inner.add(v.getNameAsString()));
                    }
                });
            }
            return inner;
        }

        private boolean isRelationalOp(BinaryExpr.Operator op) {
            return op == BinaryExpr.Operator.LESS || op == BinaryExpr.Operator.LESS_EQUALS
                    || op == BinaryExpr.Operator.GREATER || op == BinaryExpr.Operator.GREATER_EQUALS
                    || op == BinaryExpr.Operator.EQUALS || op == BinaryExpr.Operator.NOT_EQUALS;
        }

        private BinaryExpr.Operator negateRelationalOperator(BinaryExpr.Operator op) {
            return switch (op) {
                case LESS -> BinaryExpr.Operator.GREATER_EQUALS;
                case LESS_EQUALS -> BinaryExpr.Operator.GREATER;
                case GREATER -> BinaryExpr.Operator.LESS_EQUALS;
                case GREATER_EQUALS -> BinaryExpr.Operator.LESS;
                case EQUALS -> BinaryExpr.Operator.NOT_EQUALS;
                case NOT_EQUALS -> BinaryExpr.Operator.EQUALS;
                default -> null;
            };
        }

        private String relOpString(BinaryExpr.Operator op) {
            return switch (op) {
                case LESS -> "<";
                case LESS_EQUALS -> "<=";
                case GREATER -> ">";
                case GREATER_EQUALS -> ">=";
                case EQUALS -> "==";
                case NOT_EQUALS -> "!=";
                default -> "";
            };
        }

        private boolean alwaysReturnsOrThrows(Statement stmt) {
            if (stmt instanceof com.github.javaparser.ast.stmt.ReturnStmt) return true;
            if (stmt instanceof com.github.javaparser.ast.stmt.ThrowStmt) return true;
            if (stmt instanceof com.github.javaparser.ast.stmt.BlockStmt block) {
                for (Statement s : block.getStatements()) {
                    if (s instanceof com.github.javaparser.ast.stmt.ReturnStmt
                            || s instanceof com.github.javaparser.ast.stmt.ThrowStmt) return true;
                }
            }
            return false;
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

            // Counters that are only ever INCREMENTED in the body — safe to declare
            // `counter >= 0` when the guard mentions them on the left. A decrementing
            // counter (e.g. `while (j >= 0) j--;`) reaches -1 at back-edge, so emitting
            // `j >= 0` as an invariant is unsound. Only monotonic-non-negative counters
            // (via the same detector used elsewhere) pass the gate.
            Set<String> monotonicNonNegative = new LinkedHashSet<>(
                    findMonotonicNonNegativeCounters(whileStmt, body));

            // Decompose `cond1 && cond2 && ...` into individual conjuncts so each numeric
            // condition gets a chance to contribute its own invariant.
            for (Expression conjunct : flattenAndConjuncts(condition)) {
                if (conjunct instanceof BinaryExpr binExpr) {
                    if (counterNames.isEmpty()) continue;
                    String left = binExpr.getLeft().toString();
                    String right = binExpr.getRight().toString();
                    if (counterNames.contains(left)) {
                        String weakened = getWeakenedOperatorForInvariant(binExpr.getOperator());
                        // The invariant `counter <op> bound` only holds at loop entry when
                        // the counter's initial value already satisfies the bound. We can only
                        // soundly add it if the bound is pre-state-expressible (so we can also
                        // emit a matching precondition). Otherwise the invariant could be false
                        // at loop entry — e.g. `while (left < right)` with `right = arr.length - 1`
                        // fails when arr.length == 0.
                        boolean preconditionEmitted =
                                emitCounterBoundPrecondition(whileStmt, left, weakened, right);
                        if (preconditionEmitted) {
                            invariants.add(left + " " + weakened + " " + right);
                        }
                        if (monotonicNonNegative.contains(left)) {
                            invariants.add(left + " >= 0");
                        }
                    } else if (counterNames.contains(right)) {
                        if (monotonicNonNegative.contains(right)) {
                            invariants.add(right + " >= 0");
                        }
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

            // For counters that start at a pre-state-expressible value and are only
            // decremented in the body, emit `counter <= init` — holds inductively because
            // decrement preserves the upper bound.
            findMonotonicDecreasingBoundedCounters(whileStmt, body).forEach((name, init) ->
                    invariants.add(name + " <= " + init));

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
        /**
         * Emits {@code requires initial OP bound} on the method spec when the counter has
         * a literal initializer AND the bound is expressible in pre-state (a parameter,
         * field, literal, or `param.length`). Without the pre-state check we'd emit
         * invariants that reference local variables, which OpenJML rejects.
         */
        private boolean emitCounterBoundPrecondition(com.github.javaparser.ast.Node loopNode,
                                                   String counter, String weakenedOp, String bound) {
            if (spec == null) return false;
            if (!weakenedOp.equals("<=") && !weakenedOp.equals(">=")) return false;
            Optional<MethodDeclaration> methodOpt = loopNode.findAncestor(MethodDeclaration.class);
            if (methodOpt.isEmpty()) return false;
            MethodDeclaration method = methodOpt.get();
            if (!isPreStateExpressible(bound, method)) return false;
            for (com.github.javaparser.ast.body.VariableDeclarator vd
                    : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                if (!vd.getNameAsString().equals(counter) || vd.getInitializer().isEmpty()) continue;
                Expression init = vd.getInitializer().get();
                String initStr;
                if (init.isIntegerLiteralExpr()) {
                    initStr = String.valueOf(init.asIntegerLiteralExpr().asInt());
                } else if (init.isNameExpr() && isPreStateExpressible(init.toString(), method)) {
                    initStr = init.toString();
                } else if (isPreStateExpressible(init.toString(), method)) {
                    // Compound initializers like `start + 1` or `arr.length - 1` are fine
                    // as precondition operands as long as every identifier inside them
                    // is pre-state-expressible. Without this, for-loops like
                    //   for (int i = start + 1; i < end; i++)
                    // lose their `i <= end` invariant — the precondition `start + 1 <= end`
                    // is perfectly representable and logically equivalent to the usual
                    // caller-supplied `start < end`, so the invariant should be safe to
                    // emit.
                    initStr = init.toString();
                } else {
                    continue;
                }
                String candidate = initStr + " " + weakenedOp + " " + bound;
                if (isTriviallyTrue(candidate)) return true; // already holds, skip
                spec.addPrecondition(candidate, MethodSpecification.ConfidenceLevel.MEDIUM);
                return true;
            }
            return false;
        }

        /**
         * Drops preconditions that are statically true — things like `0 >= 0`,
         * `5 <= 5`, `0 <= arr.length` (array lengths are always non-negative).
         * A noisy trivially-true requires doesn't fail verification but it makes
         * the inferred spec harder to read and can confuse downstream analyses.
         */
        private boolean isTriviallyTrue(String precond) {
            String p = precond.trim();
            // Identical-sides equality/inequality: `x >= x`, `x <= x`.
            int idx = p.indexOf(" >= ");
            if (idx < 0) idx = p.indexOf(" <= ");
            if (idx >= 0) {
                String left = p.substring(0, idx).trim();
                String right = p.substring(idx + 4).trim();
                if (left.equals(right)) return true;
                try {
                    int li = Integer.parseInt(left);
                    int ri = Integer.parseInt(right);
                    char op = p.charAt(idx + 1);
                    return (op == '>' && li >= ri) || (op == '<' && li <= ri);
                } catch (NumberFormatException ignored) { }
            }
            // `0 <= arr.length`, `0 <= list.size()` — always true.
            if (p.matches("0\\s*<=\\s*\\w+(\\.\\w+)*\\.(length|size\\(\\))")) return true;
            // `arr.length >= 0` — always true.
            if (p.matches("\\w+(\\.\\w+)*\\.(length|size\\(\\))\\s*>=\\s*0")) return true;
            return false;
        }

        /**
         * Returns true if {@code expr} only references parameters, fields, literals, and
         * the {@code .length} property of arrays.
         */
        /**
         * Returns true when {@code expr} can be statically shown to evaluate to a
         * non-negative integer. Currently recognises:
         * <ul>
         *   <li>Non-negative integer literals (including zero).</li>
         *   <li>{@code arr.length} — array lengths are always {@code >= 0}.</li>
         *   <li>A name reference to a loop variable in an enclosing for-loop whose
         *       initializer is itself structurally non-negative.</li>
         *   <li>A sum of two structurally non-negative expressions.</li>
         * </ul>
         * Used as a safety net when an initializer isn't pre-state-expressible but is
         * obviously {@code >= 0} (e.g., {@code j = i + 1} in a nested loop).
         */
        private boolean isStructurallyNonNegative(Expression expr,
                                                   com.github.javaparser.ast.Node fromNode) {
            if (expr instanceof EnclosedExpr en) return isStructurallyNonNegative(en.getInner(), fromNode);
            if (expr.isIntegerLiteralExpr()) {
                return expr.asIntegerLiteralExpr().asInt() >= 0;
            }
            if (expr instanceof FieldAccessExpr fae && fae.getNameAsString().equals("length")) {
                return true;
            }
            if (expr instanceof NameExpr ne) {
                String name = ne.getNameAsString();
                // Walk outward looking for a for-loop whose init declares this name and
                // whose own init is structurally non-negative.
                com.github.javaparser.ast.Node cur = fromNode.getParentNode().orElse(null);
                while (cur != null) {
                    if (cur instanceof ForStmt outer) {
                        for (Expression initExpr : outer.getInitialization()) {
                            if (initExpr instanceof VariableDeclarationExpr vde) {
                                for (com.github.javaparser.ast.body.VariableDeclarator vd
                                        : vde.getVariables()) {
                                    if (vd.getNameAsString().equals(name)
                                            && vd.getInitializer().isPresent()
                                            && isStructurallyNonNegative(
                                                    vd.getInitializer().get(), outer)) {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                    cur = cur.getParentNode().orElse(null);
                }
                return false;
            }
            if (expr instanceof BinaryExpr be
                    && be.getOperator() == BinaryExpr.Operator.PLUS) {
                return isStructurallyNonNegative(be.getLeft(), fromNode)
                        && isStructurallyNonNegative(be.getRight(), fromNode);
            }
            return false;
        }

        private boolean isPreStateExpressible(String expr, MethodDeclaration method) {
            Set<String> paramNames = new java.util.HashSet<>();
            method.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));
            Set<String> fieldNames = method.findAncestor(
                    com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .map(cls -> cls.getFields().stream()
                            .flatMap(f -> f.getVariables().stream())
                            .map(v -> v.getNameAsString())
                            .collect(java.util.stream.Collectors.toSet()))
                    .orElseGet(java.util.HashSet::new);

            java.util.regex.Matcher m = java.util.regex.Pattern
                    .compile("\\b([a-zA-Z_$][a-zA-Z_$0-9]*)\\b").matcher(expr);
            while (m.find()) {
                String tok = m.group(1);
                int idx = m.end();
                boolean followedByParen = idx < expr.length() && expr.charAt(idx) == '(';
                boolean afterDot = m.start() > 0 && expr.charAt(m.start() - 1) == '.';
                if (followedByParen || afterDot) continue;
                if (tok.equals("this") || tok.equals("true") || tok.equals("false")
                        || tok.equals("null") || tok.equals("Integer") || tok.equals("Long")) continue;
                if (paramNames.contains(tok) || fieldNames.contains(tok)) continue;
                return false;
            }
            return true;
        }

        /**
         * Returns a map of local variables that (a) are declared with an initializer
         * expression referencing only parameters, fields, and literals, and (b) are only
         * ever modified (anywhere in the enclosing method) by `--` or `-= positive-literal`
         * inside this loop's body. For such variables, `var <= initExpr` is a sound loop
         * invariant — the upper bound can't be violated by decrement.
         */
        private Map<String, String> findMonotonicDecreasingBoundedCounters(
                com.github.javaparser.ast.Node loopNode, Statement body) {
            Map<String, String> result = new LinkedHashMap<>();
            Optional<MethodDeclaration> methodOpt = loopNode.findAncestor(MethodDeclaration.class);
            if (methodOpt.isEmpty()) return result;
            MethodDeclaration method = methodOpt.get();

            // Candidate names: anything with a -- or -= in the body.
            Set<String> bodyCounters = new LinkedHashSet<>();
            body.findAll(UnaryExpr.class).forEach(u -> {
                if (u.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) {
                    if (u.getExpression() instanceof NameExpr ne) bodyCounters.add(ne.getNameAsString());
                }
            });
            body.findAll(AssignExpr.class).forEach(a -> {
                if (a.getOperator() == AssignExpr.Operator.MINUS
                        && a.getTarget() instanceof NameExpr ne) {
                    bodyCounters.add(ne.getNameAsString());
                }
            });

            outer:
            for (String name : bodyCounters) {
                Expression init = null;
                for (com.github.javaparser.ast.body.VariableDeclarator vd
                        : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                    if (vd.getNameAsString().equals(name) && vd.getInitializer().isPresent()) {
                        init = vd.getInitializer().get();
                    }
                }
                if (init == null) continue;
                if (!isPreStateExpressible(init.toString(), method)) continue;

                // All writes to `name` in the method must be inside this loop body and
                // of the monotonic-decreasing kind.
                for (AssignExpr a : method.findAll(AssignExpr.class)) {
                    if (!(a.getTarget() instanceof NameExpr targ) || !targ.getNameAsString().equals(name)) continue;
                    if (!isInsideStatement(a, body)) continue outer;
                    if (a.getOperator() != AssignExpr.Operator.MINUS) continue outer;
                    if (!isKnownNonNegativeRhs(a.getValue())) continue outer;
                }
                for (UnaryExpr u : method.findAll(UnaryExpr.class)) {
                    if (!(u.getExpression() instanceof NameExpr ne) || !ne.getNameAsString().equals(name)) continue;
                    if (!isInsideStatement(u, body)) continue outer;
                    if (u.getOperator() != UnaryExpr.Operator.POSTFIX_DECREMENT
                            && u.getOperator() != UnaryExpr.Operator.PREFIX_DECREMENT) continue outer;
                }
                result.put(name, init.toString());
            }
            return result;
        }

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
                    // RHS must be known non-negative: either a non-negative integer literal or a
                    // bit-mask expression `<expr> & <non-negative-literal>` (the mask bounds the
                    // result to [0, mask]). Overflow soundness is left to OpenJML as before.
                    if (!isKnownNonNegativeRhs(rhs)) continue outer;
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

        /**
         * True when the expression is guaranteed non-negative without semantic analysis:
         * a non-negative integer literal, or {@code <expr> & <non-negative-int-literal>}.
         * The latter covers popcount-style accumulators where {@code count += v & 1}.
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
            // Previously emitted `var >= 0` for any compound add/multiply, but that's
            // unsound: `sum += a[i] * b[i]` leaves sum negative when any product is.
            // The monotonic-non-negative counter detector (findMonotonicNonNegativeCounters)
            // covers the safe cases via a stricter whitelist on the RHS.
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
