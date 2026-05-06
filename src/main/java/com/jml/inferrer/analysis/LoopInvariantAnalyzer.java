package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
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
        loopVisitor.getDecreasesByOrdinal().forEach((ordinal, decs) ->
                decs.forEach(dec -> spec.addLoopDecreases(dec, ordinal)));
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
        // Parallel map: loop ordinal -> termination measures (loop_decreases) emitted.
        private final Map<Integer, List<String>> decreasesByOrdinal = new LinkedHashMap<>();
        private final Set<String> seenDecreases = new LinkedHashSet<>();
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

        public Map<Integer, List<String>> getDecreasesByOrdinal() {
            return decreasesByOrdinal;
        }

        /**
         * Adds a termination measure for the loop currently being analysed.
         * The expression must be a non-negative integer that strictly decreases
         * each iteration. When OpenJML cannot discharge it, the resulting
         * `LoopDecreases` failure is the intended bug-detection signal for
         * potentially-non-terminating loops.
         */
        protected void addDecreases(String expr) {
            if (expr == null || expr.isBlank()) return;
            String key = currentLoopOrdinal + "::" + expr;
            if (!seenDecreases.add(key)) return;
            decreasesByOrdinal.computeIfAbsent(currentLoopOrdinal, k -> new ArrayList<>()).add(expr);
        }

        // Backed by a shadow set to keep dedup semantics; routes additions to the bucket
        // for whichever loop is currently being analysed.
        // Per-loop dedup: each loop ordinal has its own set of seen invariants. This
        // matters for loops that share the same invariant — e.g. merge-style code with
        // three sequential while-loops over `i, j, k` should get `i >= 0` on each loop,
        // not just the first one.
        private final Map<Integer, Set<String>> seenByOrdinal = new LinkedHashMap<>();
        private final Set<String> invariants = new java.util.AbstractSet<String>() {
            @Override public boolean add(String s) {
                Set<String> seen = seenByOrdinal.computeIfAbsent(currentLoopOrdinal,
                        k -> new LinkedHashSet<>());
                if (!seen.add(s)) return false;
                invariantsByOrdinal.computeIfAbsent(currentLoopOrdinal, k -> new ArrayList<>()).add(s);
                return true;
            }
            @Override public java.util.Iterator<String> iterator() {
                Set<String> seen = seenByOrdinal.get(currentLoopOrdinal);
                return seen == null ? java.util.Collections.emptyIterator() : seen.iterator();
            }
            @Override public int size() {
                Set<String> seen = seenByOrdinal.get(currentLoopOrdinal);
                return seen == null ? 0 : seen.size();
            }
            @Override public boolean contains(Object o) {
                Set<String> seen = seenByOrdinal.get(currentLoopOrdinal);
                return seen != null && seen.contains(o);
            }
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
            // Wire termination measures for do-while loops. The same shapes recognised
            // for `while` (Euclidean, counter-bound, decrement-to-zero) apply: the only
            // semantic difference is that the body always runs at least once, which
            // doesn't change the measure. Drives DoWhilePattern.countDigits.
            emitDoLoopDecreases(doStmt, condition, body, counterNames);
        }

        /**
         * Termination-measure emission for do-while loops, mirroring
         * {@link #emitWhileLoopDecreases} but adapted to the {@link DoStmt} node type
         * (the underlying patterns are guard-shaped, so the body+condition pair is
         * what matters, not the loop-statement type).
         */
        private void emitDoLoopDecreases(DoStmt doStmt, Expression condition,
                                          Statement body, List<String> counterNames) {
            // Pattern 1 — Euclidean: same shape as while, applies if the guard is
            // `a != b` etc. and the body is `if (a > b) a -= b; else b -= a;`.
            if (condition instanceof BinaryExpr cond
                    && cond.getLeft() instanceof NameExpr lne
                    && cond.getRight() instanceof NameExpr rne) {
                String a = lne.getNameAsString();
                String b = rne.getNameAsString();
                if (isEuclideanSubtractionBody(body, a, b)) {
                    addDecreases(a + " + " + b);
                    invariants.add(a + " > 0");
                    invariants.add(b + " > 0");
                    return;
                }
            }

            // Patterns 2 & 3 — single-counter loop. Identify the counter from the guard
            // and the in-body update.
            for (Expression conjunct : flattenAndConjuncts(condition)) {
                if (!(conjunct instanceof BinaryExpr be)) continue;
                if (!(be.getLeft() instanceof NameExpr cn)) continue;
                String counter = cn.getNameAsString();
                String rhs = be.getRight().toString();
                int delta = bodyMonotonicDelta(body, counter);
                if (delta == 0) continue;

                if (delta > 0) {
                    BinaryExpr.Operator op = be.getOperator();
                    if (op == BinaryExpr.Operator.LESS) {
                        addDecreases(rhs + " - " + counter);
                    } else if (op == BinaryExpr.Operator.LESS_EQUALS) {
                        addDecreases("(" + rhs + " + 1) - " + counter);
                    }
                } else {
                    BinaryExpr.Operator op = be.getOperator();
                    if (op == BinaryExpr.Operator.GREATER && rhs.equals("0")) {
                        addDecreases(counter);
                    } else if (op == BinaryExpr.Operator.GREATER) {
                        addDecreases(counter + " - " + rhs);
                    } else if (op == BinaryExpr.Operator.GREATER_EQUALS) {
                        addDecreases(counter + " - (" + rhs + " - 1)");
                    }
                }
            }
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
                                    } else if (op.equals("<=") && stepSize >= 1
                                            && var.getInitializer().isPresent()
                                            && isInitBoundedByRhsViaOuterLoop(forStmt,
                                                    var.getInitializer().get(), rhs)) {
                                        // Nested-loop case: `for (int j = i + 1; j < arr.length; j++)`
                                        // where `i` is the outer counter with a known upper bound on
                                        // `arr.length`. The init `i + 1` isn't pre-state-expressible
                                        // but the inductive invariant `j <= arr.length` is still
                                        // sound: at entry `i + 1 <= arr.length` follows from the
                                        // outer loop's `i < arr.length - 1` invariant, and the
                                        // weakened comparator preserves the bound through the body.
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
            // Tight `count == i` invariant for unconditional `count++` in a single-step
            // for-loop body. Strictly stronger than `count <= i`; gates on no early
            // exits and a single write to count per iteration.
            addUnconditionalCounterEqualityInvariants(forStmt, invariants, counterNames);
            analyzeArraySegments(forStmt, invariants, counterNames);
            analyzeQuantifiedInvariants(forStmt, invariants, counterNames);
            analyzeVariableRelationships(forStmt.getBody(), invariants);
            analyzeLoopBodyForInvariants(forStmt.getBody(), invariants);
            SumInductionAnalyzer.analyze(forStmt, counterNames, invariants, spec);
            // Histogram / array-as-counter pattern: `for (int i = 0; i < N; i++) freq[X]++;`
            // (where freq is a fresh local int array). Each element is a non-negative
            // counter bounded by the loop's iteration count. Drives Histogram.countFrequency
            // and Encoder1.countRuns shapes.
            analyzeHistogramAccumulator(forStmt, invariants);

            // Termination measure: most for-loops have a clear monotonic counter
            // bounded by the comparison RHS. Emit `loop_decreases <bound> - <counter>`
            // for `for(c = LO; c < BOUND; c += STEP)` (STEP > 0) and the symmetric
            // `loop_decreases <counter> - <bound>` for decrementing loops. The
            // OpenJML check then rules out non-termination — when it can't, the
            // resulting LoopDecreases failure is a real bug-detection signal.
            emitForLoopDecreases(forStmt, counterNames);
        }

        /**
         * Emits a termination measure for a single-counter for-loop with a recognised
         * monotonic update and a comparable upper/lower bound. Skips multi-counter
         * loops (no canonical measure), missing-update loops (open-ended), and
         * non-monotonic shapes.
         */
        private void emitForLoopDecreases(ForStmt forStmt, List<String> counterNames) {
            if (counterNames.size() != 1) return;
            String counter = counterNames.get(0);
            int[] stepBox = new int[]{0};
            forStmt.getUpdate().forEach(u -> {
                int s = getStepSize(u, counter);
                if (s != 0) stepBox[0] = s;
            });
            int step = stepBox[0];
            if (step == 0) return;

            Expression cmp = forStmt.getCompare().orElse(null);
            if (!(cmp instanceof BinaryExpr be)) return;
            if (!(be.getLeft() instanceof NameExpr ln) || !ln.getNameAsString().equals(counter)) return;
            String rhs = be.getRight().toString();

            if (step > 0) {
                BinaryExpr.Operator op = be.getOperator();
                if (op == BinaryExpr.Operator.LESS) {
                    addDecreases(rhs + " - " + counter);
                } else if (op == BinaryExpr.Operator.LESS_EQUALS) {
                    addDecreases("(" + rhs + " + 1) - " + counter);
                }
            } else { // step < 0
                BinaryExpr.Operator op = be.getOperator();
                if (op == BinaryExpr.Operator.GREATER) {
                    addDecreases(counter + " - " + rhs);
                } else if (op == BinaryExpr.Operator.GREATER_EQUALS) {
                    addDecreases(counter + " - (" + rhs + " - 1)");
                }
            }
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

                                // `varName >= 0` is sound whenever the counter starts
                                // non-negative (initialised to 0 in the method body) AND
                                // only increments — holds regardless of persistence across
                                // an outer loop. `varName <= innerCounter` is NOT sound
                                // when the counter persists because at outer iteration 2
                                // the inner counter resets to 0 but varName already holds
                                // a positive value.
                                if (startsAtZeroLocal(body, varName)) {
                                    invariants.add(varName + " >= 0");
                                }
                                if (!counterNames.isEmpty()
                                        && !persistsAcrossEnclosingLoop(body, varName)
                                        && !isFieldAccumulator(body, varName)) {
                                    String counter = counterNames.get(0);
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
                // Emit `>= 0` even for persisting counters, but only `<= counter` if
                // the counter doesn't persist (otherwise it breaks at outer-iter 2+).
                if (startsAtZeroLocal(body, varName)) {
                    invariants.add(varName + " >= 0");
                }
                if (counterNames.isEmpty()) return;
                if (persistsAcrossEnclosingLoop(body, varName)) return;
                // A FIELD accumulator can be non-zero at method entry: `count <= i`
                // would fail LoopInvariantBeforeLoop on the very first check. The
                // field's class invariant (`count >= 0` if any) handles the lower
                // bound; the upper-bound `<= counter` is only sound for locals
                // that actually start at 0 in this method.
                if (isFieldAccumulator(body, varName)) return;
                String counter = counterNames.get(0);
                invariants.add(varName + " >= 0");
                invariants.add(varName + " <= " + counter);
            });

            // Math.max accumulator detector: when the body contains
            //   var = Math.max(var, OTHER);   // monotonic-non-decreasing
            // or
            //   var = Math.max(0, var + ELEM); // gated non-negative
            // emit the corresponding monotonic / non-negative invariants.
            // Drives Kadane.maxSubarraySum.
            analyzeMathMaxAccumulators(body, invariants);

            // Field-increment running-sum invariant: when a loop body has
            //   this.field++   (single-step instance-field increment)
            // emit `this.field == \old(this.field) + counter` so OpenJML can
            // discharge the per-iteration overflow check using the existing
            // method-level overflow precondition.
            analyzeFieldIncrementRunningSum(body, invariants, counterNames);
        }

        /**
         * Detects the field-increment shape {@code this.f++} (or {@code ++this.f})
         * inside a loop and emits {@code this.f == \\old(this.f) + counter} so the
         * field's value at any iteration is pinned to its method-entry value plus
         * the elapsed iteration count.
         *
         * <p>Without this invariant the per-iteration overflow check on
         * {@code this.f++} cannot be discharged by the method-level overflow
         * precondition (which bounds {@code this.f + n} at entry, but does not
         * tell OpenJML what {@code this.f} is at iteration {@code i}).</p>
         */
        private void analyzeFieldIncrementRunningSum(Statement body, Set<String> invariants,
                                                      List<String> counterNames) {
            if (counterNames.isEmpty()) return;
            String counter = counterNames.get(0);
            MethodDeclaration enclosing = body.findAncestor(MethodDeclaration.class).orElse(null);

            for (UnaryExpr unary : body.findAll(UnaryExpr.class)) {
                if (unary.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                        && unary.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) continue;
                if (isInsideNestedLoopOf(unary, body)) continue;
                Expression target = unary.getExpression();
                String fieldName = null;
                if (target instanceof FieldAccessExpr fae
                        && fae.getScope().toString().equals("this")) {
                    fieldName = fae.getNameAsString();
                } else if (target instanceof NameExpr ne
                        && enclosing != null
                        && AnalysisUtils.isFieldReference(enclosing, ne.getNameAsString())) {
                    fieldName = ne.getNameAsString();
                }
                if (fieldName == null) continue;
                // Only emit when the increment is unconditional within the loop
                // body (i.e. not inside an if). A guarded increment doesn't satisfy
                // the equality form; a separate heuristic could emit `<=` for
                // those, but the equality form is what OpenJML needs to discharge
                // the overflow precondition cleanly.
                if (isInsideConditional(unary, body)) continue;

                invariants.add("this." + fieldName + " == \\old(this." + fieldName + ") + " + counter);
            }
        }

        /**
         * True when {@code node} is inside an {@link IfStmt}, {@link SwitchStmt},
         * or {@link ConditionalExpr} that lives between {@code node} and
         * {@code body}. Used to gate emission of equality-form invariants that
         * are unsound for conditional increments.
         */
        private boolean isInsideConditional(com.github.javaparser.ast.Node node,
                                             Statement body) {
            com.github.javaparser.ast.Node cur = node;
            while (cur.getParentNode().isPresent()) {
                com.github.javaparser.ast.Node parent = cur.getParentNode().get();
                if (parent == body) return false;
                if (parent instanceof IfStmt
                        || parent instanceof SwitchStmt
                        || parent instanceof ConditionalExpr) return true;
                cur = parent;
            }
            return false;
        }

        /**
         * Recognises two Math.max accumulator shapes and emits matching invariants:
         * <ul>
         *   <li>{@code var = Math.max(var, OTHER)} — emits {@code var >= OTHER} (monotonic
         *       non-decreasing wrt the other operand).</li>
         *   <li>{@code var = Math.max(0, EXPR)} — emits {@code var >= 0} (the max-with-zero
         *       gate guarantees the variable can never be negative).</li>
         * </ul>
         */
        private void analyzeMathMaxAccumulators(Statement body, Set<String> invariants) {
            for (AssignExpr ae : body.findAll(AssignExpr.class)) {
                if (ae.getOperator() != AssignExpr.Operator.ASSIGN) continue;
                if (!(ae.getTarget() instanceof NameExpr targetNe)) continue;
                if (!(ae.getValue() instanceof MethodCallExpr mce)) continue;
                if (!mce.getNameAsString().equals("max")) continue;
                if (mce.getArguments().size() != 2) continue;
                String scope = mce.getScope().map(Object::toString).orElse("");
                if (!scope.isEmpty() && !scope.equals("Math")) continue;
                String varName = targetNe.getNameAsString();
                Expression argA = mce.getArgument(0);
                Expression argB = mce.getArgument(1);

                // Shape 1: var = Math.max(0, ...) → var >= 0
                boolean leftIsZero = argA.isIntegerLiteralExpr()
                        && argA.asIntegerLiteralExpr().asInt() == 0;
                boolean rightIsZero = argB.isIntegerLiteralExpr()
                        && argB.asIntegerLiteralExpr().asInt() == 0;
                if (leftIsZero || rightIsZero) {
                    invariants.add(varName + " >= 0");
                    continue;
                }
                // Shape 2: var = Math.max(var, OTHER) → var >= OTHER
                Expression otherSide = null;
                if (argA instanceof NameExpr lne && lne.getNameAsString().equals(varName)) {
                    otherSide = argB;
                } else if (argB instanceof NameExpr rne && rne.getNameAsString().equals(varName)) {
                    otherSide = argA;
                }
                if (otherSide instanceof NameExpr otherNe) {
                    invariants.add(varName + " >= " + otherNe.getNameAsString());
                }
            }
        }

        /**
         * Detects the unconditional-counter shape:
         * {@code for (int i = LO; i CMP BOUND; i++) { ...; v++; ...; }} where {@code v}
         * is a local int initialised to 0 in the method, the loop body has no early
         * exit (return / break / continue / throw), and {@code v} is incremented
         * exactly once per iteration with no other writes inside the loop.
         *
         * <p>For these shapes the relationship {@code v == i - LO} holds inductively,
         * which gives OpenJML a tight bound on {@code v + 1} at the next increment
         * (since {@code i < BOUND} bounds the iteration count). Without this the only
         * available invariant is {@code v >= 0 && v <= i}, and the increment overflow
         * check fails because the spec allows {@code v} all the way up to {@code i}
         * which itself can grow to {@code BOUND} which is unbounded in the spec.</p>
         */
        private void addUnconditionalCounterEqualityInvariants(ForStmt forStmt,
                Set<String> invariants, List<String> counterNames) {
            if (counterNames.size() != 1) return;
            String counter = counterNames.get(0);
            // Only safe when the body has no early-exit construct.
            if (loopBodyHasEarlyExit(forStmt.getBody())) return;
            // Loop init must be `int counter = LO`.
            if (forStmt.getInitialization().size() != 1) return;
            if (!(forStmt.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return;
            if (vde.getVariables().size() != 1) return;
            VariableDeclarator decl = vde.getVariables().get(0);
            if (!decl.getNameAsString().equals(counter)) return;
            Expression initExpr = decl.getInitializer().orElse(null);
            if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return;
            int lo = initExpr.asIntegerLiteralExpr().asInt();
            if (lo < 0) return;
            // Loop update must be exactly `counter++` (single step).
            if (forStmt.getUpdate().size() != 1) return;
            Expression upd = forStmt.getUpdate().get(0);
            if (!(upd instanceof UnaryExpr uue)) return;
            if (uue.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && uue.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) return;
            if (!(uue.getExpression() instanceof NameExpr uune)
                    || !uune.getNameAsString().equals(counter)) return;

            // For each `v++` in body: must be unconditional (not inside if/switch/ternary),
            // not in a nested loop, and the only write to `v` in the loop body.
            for (UnaryExpr inc : forStmt.getBody().findAll(UnaryExpr.class)) {
                if (inc == uue) continue;
                if (inc.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                        && inc.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) continue;
                if (!(inc.getExpression() instanceof NameExpr incNe)) continue;
                String varName = incNe.getNameAsString();
                if (counterNames.contains(varName)) continue;
                if (isInsideNestedLoopOf(inc, forStmt.getBody())) continue;
                if (isInsideConditionalOfLoop(inc, forStmt)) continue;
                if (!startsAtZeroLocal(forStmt.getBody(), varName)) continue;
                if (isFieldAccumulator(forStmt.getBody(), varName)) continue;
                if (persistsAcrossEnclosingLoop(forStmt.getBody(), varName)) continue;
                // Single-write check: count all writes to varName inside body.
                int writes = 0;
                for (UnaryExpr u2 : forStmt.getBody().findAll(UnaryExpr.class)) {
                    if (u2.getExpression() instanceof NameExpr ne2
                            && ne2.getNameAsString().equals(varName)
                            && (u2.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                                    || u2.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT
                                    || u2.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                                    || u2.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT)) {
                        writes++;
                    }
                }
                for (AssignExpr ae : forStmt.getBody().findAll(AssignExpr.class)) {
                    if (ae.getTarget() instanceof NameExpr aen
                            && aen.getNameAsString().equals(varName)) {
                        writes++;
                    }
                }
                if (writes != 1) continue;
                String inv = (lo == 0)
                        ? varName + " == " + counter
                        : varName + " == " + counter + " - " + lo;
                invariants.add(inv);
            }
        }

        /**
         * True when the loop body contains a return / break / continue / throw which
         * could change the relationship between counter and accumulators.
         */
        private boolean loopBodyHasEarlyExit(Statement body) {
            return !body.findAll(com.github.javaparser.ast.stmt.ReturnStmt.class).isEmpty()
                    || !body.findAll(com.github.javaparser.ast.stmt.BreakStmt.class).isEmpty()
                    || !body.findAll(com.github.javaparser.ast.stmt.ContinueStmt.class).isEmpty()
                    || !body.findAll(com.github.javaparser.ast.stmt.ThrowStmt.class).isEmpty();
        }

        /**
         * True when {@code child} sits inside an {@code if}/{@code switch}/ternary nested
         * within {@code forStmt}'s body — i.e. the increment is conditional rather than
         * happening every iteration.
         */
        private boolean isInsideConditionalOfLoop(com.github.javaparser.ast.Node child,
                                                   ForStmt forStmt) {
            com.github.javaparser.ast.Node cur = child;
            while (cur.getParentNode().isPresent()) {
                cur = cur.getParentNode().get();
                if (cur == forStmt) return false;
                if (cur instanceof IfStmt
                        || cur instanceof SwitchStmt
                        || cur instanceof ConditionalExpr) {
                    return true;
                }
            }
            return false;
        }

        /**
         * True when {@code varName} is a field of the enclosing class rather than
         * a local variable or parameter of the enclosing method. A field
         * accumulator can hold a positive value at method entry, so the
         * `varName <= loopCounter` invariant is unsound at loop entry (the
         * counter starts at 0 but the field doesn't have to).
         */
        private boolean isFieldAccumulator(Statement body, String varName) {
            Optional<MethodDeclaration> methodOpt = body.findAncestor(MethodDeclaration.class);
            if (methodOpt.isEmpty()) return false;
            return AnalysisUtils.isFieldReference(methodOpt.get(), varName);
        }

        /**
         * True when {@code varName} is declared somewhere in the enclosing method
         * with a non-negative integer-literal initializer AND the method never assigns
         * it anything other than increment-by-literal or `= 0`. That's the shape for
         * which `varName >= 0` is a sound loop invariant.
         */
        private boolean startsAtZeroLocal(Statement body, String varName) {
            Optional<MethodDeclaration> methodOpt = body.findAncestor(MethodDeclaration.class);
            if (methodOpt.isEmpty()) return false;
            MethodDeclaration method = methodOpt.get();

            boolean foundInit = false;
            for (com.github.javaparser.ast.body.VariableDeclarator vd
                    : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                if (!vd.getNameAsString().equals(varName)) continue;
                if (vd.getInitializer().isEmpty()) continue;
                Expression init = vd.getInitializer().get();
                if (init.isIntegerLiteralExpr() && init.asIntegerLiteralExpr().asInt() >= 0) {
                    foundInit = true;
                } else {
                    return false;
                }
            }
            if (!foundInit) return false;

            // All reassignments must either be `= non-neg literal` or compound PLUS by a
            // non-negative literal. Any other shape (MINUS, multiply by negative, etc.)
            // could make varName go negative.
            for (AssignExpr ae : method.findAll(AssignExpr.class)) {
                if (!(ae.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) continue;
                Expression v = ae.getValue();
                if (ae.getOperator() == AssignExpr.Operator.ASSIGN) {
                    if (v.isIntegerLiteralExpr() && v.asIntegerLiteralExpr().asInt() >= 0) continue;
                    return false;
                }
                if (ae.getOperator() == AssignExpr.Operator.PLUS
                        && v.isIntegerLiteralExpr() && v.asIntegerLiteralExpr().asInt() >= 0) continue;
                return false;
            }
            return true;
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
         * Returns true when {@code node} sits inside an {@code if} branch (then or
         * else) somewhere between itself and {@code outerBody}. Used to gate
         * unconditional-write invariant emission so that filter/transform shapes
         * like {@code if (pred) arr[i] = VAL} don't get the wrong `arr[k] == VAL`
         * forall — that invariant is only sound when the assignment is
         * unconditional.
         */
        private boolean isInsideIfBranchOf(com.github.javaparser.ast.Node node, Statement outerBody) {
            com.github.javaparser.ast.Node cur = node;
            while (cur.getParentNode().isPresent()) {
                com.github.javaparser.ast.Node parent = cur.getParentNode().get();
                if (parent == outerBody) return false;
                if (parent instanceof IfStmt) return true;
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

        /**
         * Histogram / array-as-counter pattern. When the loop body's only mutations to a
         * fresh local int array are increments {@code arr[KEY]++}, every element of the
         * array is non-negative throughout the loop and is bounded above by the maximum
         * iteration count. The local must be declared in the same method with a
         * literal-sized {@code new int[N]} initializer (so we know the array is freshly
         * zero-filled at loop entry).
         *
         * <p>Emits:</p>
         * <ul>
         *   <li>{@code (\forall int k; 0 <= k < arr.length; arr[k] >= 0)} —
         *       holds because zero initialisation + only ++ writes.</li>
         *   <li>{@code (\forall int k; 0 <= k < arr.length; arr[k] <= ITER_BOUND)}
         *       when the for-loop has a literal-bounded iteration count expressible
         *       in pre-state.</li>
         * </ul>
         *
         * <p>Conservative: bails when ANY non-increment write to {@code arr} appears in
         * the body, when the increment isn't a simple {@code arr[X]++} unary, or when
         * the loop bound isn't pre-state-expressible.</p>
         */
        private void analyzeHistogramAccumulator(ForStmt forStmt, Set<String> invariants) {
            // Identify all distinct local int arrays being incremented in the body.
            // Skip for-each / nested cases by requiring the for-loop to be the immediate
            // enclosing loop of every increment.
            Statement body = forStmt.getBody();
            Set<String> incrementedArrays = new java.util.LinkedHashSet<>();
            boolean anyNonIncrementWrite = false;

            for (UnaryExpr ue : body.findAll(UnaryExpr.class)) {
                UnaryExpr.Operator op = ue.getOperator();
                if (op != UnaryExpr.Operator.PREFIX_INCREMENT
                        && op != UnaryExpr.Operator.POSTFIX_INCREMENT) continue;
                Expression target = ue.getExpression();
                if (target instanceof ArrayAccessExpr aae
                        && aae.getName() instanceof NameExpr arrNe) {
                    incrementedArrays.add(arrNe.getNameAsString());
                }
            }
            if (incrementedArrays.isEmpty()) return;

            for (AssignExpr ae : body.findAll(AssignExpr.class)) {
                if (ae.getTarget() instanceof ArrayAccessExpr aae
                        && aae.getName() instanceof NameExpr arrNe
                        && incrementedArrays.contains(arrNe.getNameAsString())) {
                    anyNonIncrementWrite = true;
                    break;
                }
            }
            if (anyNonIncrementWrite) return;

            // Resolve each name to a local declared in the enclosing method as
            // `int[] name = new int[LIT]` (so the array is zero-initialized).
            MethodDeclaration method = forStmt.findAncestor(MethodDeclaration.class).orElse(null);
            if (method == null) return;
            Set<String> validHistogramArrays = new java.util.LinkedHashSet<>();
            for (com.github.javaparser.ast.body.VariableDeclarator vd
                    : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                if (!incrementedArrays.contains(vd.getNameAsString())) continue;
                if (vd.getInitializer().isEmpty()) continue;
                Expression init = vd.getInitializer().get();
                if (!(init instanceof ArrayCreationExpr ace)) continue;
                // Must be `new int[LIT]` (single dimension, no levels with explicit init).
                if (ace.getLevels().size() != 1) continue;
                if (ace.getLevels().get(0).getDimension().isEmpty()) continue;
                validHistogramArrays.add(vd.getNameAsString());
            }
            if (validHistogramArrays.isEmpty()) return;

            // Compute the loop's iteration upper bound, if pre-state-expressible.
            String iterBoundStr = simpleForLoopIterationBound(forStmt);

            for (String arr : validHistogramArrays) {
                invariants.add("(\\forall int k; 0 <= k && k < " + arr + ".length; "
                        + arr + "[k] >= 0)");
                if (iterBoundStr != null) {
                    invariants.add("(\\forall int k; 0 <= k && k < " + arr + ".length; "
                            + arr + "[k] <= " + iterBoundStr + ")");
                }
            }
        }

        /**
         * For {@code for (int i = LO; i < BOUND; i++)} (or {@code <=}) returns a string
         * for the maximum iteration count expressed in pre-state, or null if the
         * loop header isn't of that simple shape.
         */
        private String simpleForLoopIterationBound(ForStmt fs) {
            if (fs.getInitialization().size() != 1) return null;
            if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return null;
            if (vde.getVariables().size() != 1) return null;
            VariableDeclarator decl = vde.getVariables().get(0);
            Expression initExpr = decl.getInitializer().orElse(null);
            if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return null;
            int lo = initExpr.asIntegerLiteralExpr().asInt();
            if (lo < 0) return null;
            String loopVar = decl.getNameAsString();

            Expression cmpExpr = fs.getCompare().orElse(null);
            if (!(cmpExpr instanceof BinaryExpr cmp)) return null;
            BinaryExpr.Operator cmpOp = cmp.getOperator();
            if (cmpOp != BinaryExpr.Operator.LESS && cmpOp != BinaryExpr.Operator.LESS_EQUALS) return null;
            if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                    || !cmpLeft.getNameAsString().equals(loopVar)) return null;

            String boundStr = cmp.getRight().toString();
            if (cmpOp == BinaryExpr.Operator.LESS_EQUALS) boundStr = "(" + boundStr + " + 1)";
            if (lo > 0) boundStr = "(" + boundStr + " - " + lo + ")";
            return boundStr;
        }

        private void analyzeArraySegments(ForStmt forStmt, Set<String> invariants, List<String> counterNames) {
            if (counterNames.isEmpty()) return;
            String counter = counterNames.get(0);

            Statement body = forStmt.getBody();

            // Only consider UNCONDITIONAL writes — `if (pred(arr[i])) arr[i] = VAL`
            // is a filter/transform shape where prefix elements `arr[0..i)` are NOT
            // all equal to VAL (the ones where pred was false retain their original
            // value). The conditional case is handled by `analyzeFilterTransformLoop`
            // below, which emits a sound disjunction. Treating both shapes uniformly
            // here would emit `arr[k] == VAL` and break LoopInvariant inductively.
            List<AssignExpr> arrayWrites = body.findAll(AssignExpr.class).stream()
                    .filter(assign -> assign.getTarget() instanceof ArrayAccessExpr)
                    .filter(assign -> !isInsideIfBranchOf(assign, body))
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
                // Same gate as analyzeArraySegments: only UNCONDITIONAL writes give
                // a `\forall k; arr[k] == VAL` invariant. The filter/transform shape
                // (`if (pred) arr[i] = VAL`) is handled by `analyzeFilterTransformLoop`.
                if (isInsideIfBranchOf(assign, body)) return;
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
                // Element-wise comparison shape: `if (a[i] != b[i]) return false;` —
                // the RHS is itself an array access indexed by the loop counter.
                // Substitute the loop counter with the bound quantifier `k` so the
                // emitted invariant (`a[k] == b[k]`) ranges over the same prefix.
                // Bare-string `i` -> `k` substitution would corrupt names like `idx`.
                String rhs = rewriteCounterAccessForQuantifier(bcond.getRight(), counter);
                if (rhs == null) {
                    // Couldn't safely rewrite (RHS uses counter outside an array
                    // access whose own index is the counter). Fall back to the
                    // existing literal-RHS shape only when the RHS doesn't mention
                    // the counter at all — otherwise the resulting forall would
                    // pin every element to the LAST iteration's RHS value.
                    String rawRhs = bcond.getRight().toString();
                    if (rawRhs.matches(".*\\b" + java.util.regex.Pattern.quote(counter) + "\\b.*")) return;
                    rhs = rawRhs;
                }
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

            // Filter/transform pattern: `if (PRED(arr[i])) arr[i] = VAL` —
            // every element of the prefix `arr[0..i)` satisfies "PRED was false
            // (so element retained original value, satisfying !PRED) OR the
            // element was assigned VAL". The simplest sound generalisation is
            // `arr[k] (negated_op) RHS || arr[k] == VAL`.
            analyzeFilterTransformLoop(forStmt, body, counter, lowerBound,
                    innerLoopCounters, invariants);
        }

        /**
         * Filter/transform inductive invariant.
         *
         * <p>For a loop body of the shape</p>
         * <pre>
         * if (arr[i] OP RHS) arr[i] = VAL;
         * </pre>
         * <p>after iteration k the element {@code arr[k]} is either the original
         * (which failed the predicate, so satisfies {@code !(arr[k] OP RHS)}) or
         * the assigned literal {@code VAL}. The disjunction is preserved
         * inductively: the loop body either skips (leaving the element to satisfy
         * the negated predicate) or assigns {@code VAL}, and both sides of the
         * disjunction trivially hold for the new prefix.</p>
         */
        private void analyzeFilterTransformLoop(ForStmt forStmt, Statement body, String counter,
                                                String lowerBound, Set<String> innerLoopCounters,
                                                Set<String> invariants) {
            body.findAll(IfStmt.class).forEach(ifStmt -> {
                // Only top-level `if` directly in the loop body — nested ifs
                // produce more complex per-path invariants we don't model.
                if (!directBodyChild(ifStmt, body)) return;
                if (!(ifStmt.getCondition() instanceof BinaryExpr bcond)) return;
                if (!isRelationalOp(bcond.getOperator())) return;
                if (!(bcond.getLeft() instanceof ArrayAccessExpr aae)) return;
                if (!aae.getIndex().toString().equals(counter)) return;
                String arrName = aae.getName().toString();

                // Then-branch must consist only of `arr[i] = VAL` (single assign,
                // possibly inside a block). VAL must be a literal so the
                // post-iteration disjunction stays expressible without `\old`.
                AssignExpr lone = onlyArrayWriteToCounter(ifStmt.getThenStmt(), arrName, counter);
                if (lone == null) return;
                if (lone.getOperator() != AssignExpr.Operator.ASSIGN) return;
                Expression value = lone.getValue();
                if (!value.isLiteralExpr()) return;
                // Skip if there's an else-branch — that's a different transform
                // shape we don't model here.
                if (ifStmt.getElseStmt().isPresent()) return;

                String rhs = bcond.getRight().toString();
                // Same scope hygiene as the universal-so-far emission: the RHS
                // must not reference inner-loop counters or the outer counter
                // itself (the RHS in `arr[k] OP rhs` would be wrong).
                if (rhs.matches(".*\\b" + java.util.regex.Pattern.quote(counter) + "\\b.*")) return;
                for (String innerCounter : innerLoopCounters) {
                    if (rhs.matches(".*\\b" + java.util.regex.Pattern.quote(innerCounter) + "\\b.*")) return;
                }

                BinaryExpr.Operator negated = negateRelationalOperator(bcond.getOperator());
                if (negated == null) return;
                String negOpStr = relOpString(negated);
                String valStr = value.toString();
                invariants.add("(\\forall int k; " + lowerBound + " <= k && k < " + counter + "; "
                        + arrName + "[k] " + negOpStr + " " + rhs + " || "
                        + arrName + "[k] == " + valStr + ")");
            });
        }

        /**
         * If the then-statement (possibly a block) contains exactly one
         * statement that's an assignment to {@code arrName[counter]}, returns
         * the assignment; otherwise null. Used by
         * {@link #analyzeFilterTransformLoop} to verify the body shape is a
         * single transform of the current element.
         */
        private AssignExpr onlyArrayWriteToCounter(Statement then, String arrName, String counter) {
            Statement target = then;
            if (then instanceof BlockStmt block) {
                if (block.getStatements().size() != 1) return null;
                target = block.getStatements().get(0);
            }
            if (!(target instanceof ExpressionStmt es)) return null;
            if (!(es.getExpression() instanceof AssignExpr ae)) return null;
            if (!(ae.getTarget() instanceof ArrayAccessExpr aae)) return null;
            if (!aae.getName().toString().equals(arrName)) return null;
            if (!aae.getIndex().toString().equals(counter)) return null;
            return ae;
        }

        /**
         * Returns true when {@code stmt} is a direct child of {@code body} (or
         * the lone child of {@code body} when {@code body} is itself a block).
         * Excludes nested ifs and bodies of inner loops.
         */
        private boolean directBodyChild(Statement stmt, Statement body) {
            if (stmt == body) return true;
            if (body instanceof BlockStmt block) {
                return block.getStatements().contains(stmt);
            }
            // body is the single statement
            return body == stmt;
        }

        /**
         * Rewrites an expression for use as the RHS of a {@code \forall int k; ...}
         * invariant where {@code k} replaces the for-loop counter on prefix accesses.
         *
         * <p>The only safe substitution is for {@link ArrayAccessExpr}s whose own
         * index is exactly the loop counter — those refer to "this iteration's
         * element" of some other array, and inside the quantifier the analogous
         * element is at index {@code k}. Returns the rewritten string when the
         * substitution is structurally complete, or null when the expression
         * mentions the counter in a context where {@code k}-substitution would
         * change meaning (e.g. arithmetic on the counter).</p>
         */
        private String rewriteCounterAccessForQuantifier(Expression rhs, String counter) {
            String raw = rhs.toString();
            // Cheap fast path: RHS doesn't mention the counter at all → return as-is.
            if (!raw.matches(".*\\b" + java.util.regex.Pattern.quote(counter) + "\\b.*")) {
                return raw;
            }
            if (rhs instanceof ArrayAccessExpr aae && aae.getIndex().toString().equals(counter)) {
                // Substitute exactly this access's index. Use AST-aware print
                // rather than naive string replace (the array name itself could
                // legitimately be a single letter equal to the counter).
                return aae.getName().toString() + "[k]";
            }
            // Anything else: arithmetic on the counter, nested expressions, etc.
            // are too easy to get wrong silently. Bail out and let the caller
            // either skip emission or use a raw-RHS fallback.
            return null;
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
                        // `counter >= 0` is sound in two scenarios for a decrementing counter:
                        //   (1) Monotonic-non-negative detector: start >= 0, only increment.
                        //   (2) Strict guard `counter > 0` with decrement step 1: body entered
                        //       when counter >= 1, after decrement counter >= 0.
                        // Without the strict-guard case we'd lose sound invariants like
                        // `this.count >= 0` for `while (this.count > 0) this.count--;`
                        // (drainToZero pattern, preserved by the class invariant).
                        boolean strictGtZero = binExpr.getOperator() == BinaryExpr.Operator.GREATER
                                && right.equals("0");
                        if (monotonicNonNegative.contains(left) || strictGtZero) {
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
            // Merge-pattern synchronisation: for `while (i<a.length && j<b.length)`
            // where `i,j,k` start at 0 and the body increments `k` AND exactly one
            // of `i,j` per iteration, emit `k <= i + j`. Combined with i<=a.length,
            // j<=b.length, this lets OpenJML discharge `result[k]` index bounds
            // when `result.length == a.length + b.length`.
            emitMergeCounterSync(whileStmt, body);

            // Termination measures for while-loops, three patterns:
            // (1) Subtractive Euclidean: `while (a != b) { if (a > b) a -= b; else b -= a; }`
            //     Measure: a + b. Fails for non-positive inputs — exactly the gcd(0,-1) bug.
            // (2) Counter-bound: `while (counter < bound) { ...; counter++; }` →
            //     bound - counter (mirrors for-loop case).
            // (3) Decrement-to-zero: `while (counter > 0) { ...; counter--; }` →
            //     counter (already non-negative by guard).
            emitWhileLoopDecreases(whileStmt, condition, body, counterNames);
        }

        /**
         * Emits the merge-pattern synchronisation invariant {@code k <= i + j} when the
         * body shape matches:
         * <ul>
         *   <li>{@code k} is unconditionally incremented (e.g. {@code k++} at top level
         *       OR {@code k++} on every branch of a top-level if)</li>
         *   <li>exactly one of {@code i} or {@code j} is incremented per iteration
         *       (so {@code i + j} grows by exactly 1 per iteration, matching {@code k})</li>
         *   <li>all three start at 0 (sourced from local declarations earlier in the method)</li>
         * </ul>
         *
         * <p>The relationship needed is {@code k == i + j} (since both sides start at 0
         * and grow by exactly 1 per iteration) but {@code k <= i + j} is what OpenJML
         * needs for the in-loop {@code result[k]} access to be in bounds, and is sound
         * even if the body is conservative (e.g. compound-assigns through + a[i]).</p>
         */
        private void emitMergeCounterSync(WhileStmt whileStmt, Statement body) {
            // Body must be a single block with statements
            BlockStmt block;
            if (body instanceof BlockStmt bs) block = bs;
            else if (body instanceof ExpressionStmt) return; // single-stmt body — too simple
            else return;

            // Identify the body's k-update position and the i/j updates inside an if-else
            // top level. Use the structural shape:
            //   if (...) { ...; i++; } else { ...; j++; }
            //   k++;
            String iVar = null, jVar = null, kVar = null;
            // Look for top-level k++
            for (Statement s : block.getStatements()) {
                if (s instanceof ExpressionStmt es && es.getExpression() instanceof UnaryExpr ue
                        && (ue.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                            || ue.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT)
                        && ue.getExpression() instanceof NameExpr ne) {
                    kVar = ne.getNameAsString();
                    break;
                }
            }
            if (kVar == null) return;

            // Find an if-else at top level whose then-branch increments one var and
            // else-branch increments another.
            for (Statement s : block.getStatements()) {
                if (!(s instanceof IfStmt ifStmt)) continue;
                if (ifStmt.getElseStmt().isEmpty()) continue;
                String thenInc = findUniqueIncrementedNameInBranch(ifStmt.getThenStmt(), kVar);
                String elseInc = findUniqueIncrementedNameInBranch(ifStmt.getElseStmt().get(), kVar);
                if (thenInc != null && elseInc != null && !thenInc.equals(elseInc)) {
                    iVar = thenInc;
                    jVar = elseInc;
                    break;
                }
            }
            if (iVar == null || jVar == null) return;

            // All three must start at 0. Look for declarations of these names with
            // initialiser 0 in the enclosing method.
            MethodDeclaration method = whileStmt.findAncestor(MethodDeclaration.class).orElse(null);
            if (method == null) return;
            if (!isLocalInitialisedToZero(method, iVar)) return;
            if (!isLocalInitialisedToZero(method, jVar)) return;
            if (!isLocalInitialisedToZero(method, kVar)) return;

            invariants.add(kVar + " <= " + iVar + " + " + jVar);
        }

        /**
         * Returns the unique name {@code n} (other than {@code excludeName}) such that
         * {@code branch} contains {@code n++} (postfix or prefix). Returns null if no
         * such variable exists or there are zero / multiple candidates.
         */
        private String findUniqueIncrementedNameInBranch(Statement branch, String excludeName) {
            Set<String> incremented = new LinkedHashSet<>();
            for (UnaryExpr ue : branch.findAll(UnaryExpr.class)) {
                if (ue.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                        && ue.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) continue;
                if (!(ue.getExpression() instanceof NameExpr ne)) continue;
                String n = ne.getNameAsString();
                if (n.equals(excludeName)) continue;
                incremented.add(n);
            }
            return incremented.size() == 1 ? incremented.iterator().next() : null;
        }

        /**
         * True when the enclosing method contains a local-variable declaration
         * {@code int name = 0} (or any non-zero initialiser doesn't disqualify here as
         * long as the most recent declaration uses zero — for practical merge code
         * the declaration is unique).
         */
        private boolean isLocalInitialisedToZero(MethodDeclaration method, String name) {
            for (com.github.javaparser.ast.body.VariableDeclarator vd
                    : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                if (!vd.getNameAsString().equals(name)) continue;
                if (vd.getInitializer().isEmpty()) continue;
                Expression init = vd.getInitializer().get();
                if (init.isIntegerLiteralExpr()
                        && init.asIntegerLiteralExpr().asInt() == 0) return true;
                return false; // first match decides
            }
            return false;
        }

        /**
         * Detects three common while-loop termination shapes and emits a `loop_decreases`
         * for each. When emission isn't possible (loop has no obvious measure), the
         * absence of `loop_decreases` means OpenJML won't check termination at all —
         * which is the right tradeoff: we don't want to invent a wrong measure.
         */
        private void emitWhileLoopDecreases(WhileStmt whileStmt, Expression condition,
                                             Statement body, List<String> counterNames) {
            // Pattern 1: subtractive Euclidean. Guard `a != b` (or `a > b`/`a < b`),
            // body `if (a > b) a -= b; else b -= a;` or `a = a - b`/`b = b - a`.
            if (condition instanceof BinaryExpr cond
                    && cond.getLeft() instanceof NameExpr lne
                    && cond.getRight() instanceof NameExpr rne) {
                String a = lne.getNameAsString();
                String b = rne.getNameAsString();
                if (isEuclideanSubtractionBody(body, a, b)) {
                    addDecreases(a + " + " + b);
                    // Companion invariants: `a > 0 && b > 0` is preserved by the
                    // Euclidean body and is exactly what OpenJML needs to discharge
                    // the LoopDecreasesNonNegative obligation. They hold at entry
                    // only when the matching preconditions hold, so emit them too.
                    invariants.add(a + " > 0");
                    invariants.add(b + " > 0");
                    if (spec != null) {
                        spec.addPrecondition(a + " > 0",
                                MethodSpecification.ConfidenceLevel.MEDIUM);
                        spec.addPrecondition(b + " > 0",
                                MethodSpecification.ConfidenceLevel.MEDIUM);
                    }
                    return;
                }
            }

            // Pattern 2 & 3: single-counter loop. Identify the counter from the guard
            // and the in-body update.
            for (Expression conjunct : flattenAndConjuncts(condition)) {
                if (!(conjunct instanceof BinaryExpr be)) continue;
                if (!(be.getLeft() instanceof NameExpr cn)) continue;
                String counter = cn.getNameAsString();
                String rhs = be.getRight().toString();
                int delta = bodyMonotonicDelta(body, counter);
                if (delta == 0) continue;

                if (delta > 0) {
                    // Counter increasing toward bound (Pattern 2).
                    BinaryExpr.Operator op = be.getOperator();
                    if (op == BinaryExpr.Operator.LESS) {
                        addDecreases(rhs + " - " + counter);
                    } else if (op == BinaryExpr.Operator.LESS_EQUALS) {
                        addDecreases("(" + rhs + " + 1) - " + counter);
                    }
                } else { // delta < 0
                    // Counter decreasing toward bound (Pattern 3).
                    BinaryExpr.Operator op = be.getOperator();
                    if (op == BinaryExpr.Operator.GREATER && rhs.equals("0")) {
                        addDecreases(counter);
                    } else if (op == BinaryExpr.Operator.GREATER) {
                        addDecreases(counter + " - " + rhs);
                    } else if (op == BinaryExpr.Operator.GREATER_EQUALS) {
                        addDecreases(counter + " - (" + rhs + " - 1)");
                    }
                }
            }

            // Pattern 4: Newton/convergence shape: `while (Math.abs(EXPR) > eps) { ...; }`
            // The measure is `Math.abs(EXPR)` cast to a non-negative quantity. Even if
            // OpenJML can't prove the strict-decrease, emitting *some* loop_decreases
            // narrows the verification gap and matches the intended semantics. Drives
            // Guard4.squareRoot-style Newton iterations and similar fixed-point loops.
            emitConvergenceMeasure(condition, body);
        }

        /**
         * For loops shaped like {@code while (Math.abs(EXPR) > eps) BODY} (or {@code >= eps},
         * or {@code abs(...)}), emit a {@code loop_decreases Math.abs(EXPR)} measure. The
         * body is required to update at least one variable referenced inside EXPR — otherwise
         * the measure could never decrease and the inferred clause would be obviously wrong.
         */
        private void emitConvergenceMeasure(Expression condition, Statement body) {
            if (!(condition instanceof BinaryExpr cmp)) return;
            BinaryExpr.Operator op = cmp.getOperator();
            if (op != BinaryExpr.Operator.GREATER && op != BinaryExpr.Operator.GREATER_EQUALS) return;
            // LHS must be Math.abs(EXPR) or a bare abs(EXPR) call.
            if (!(cmp.getLeft() instanceof MethodCallExpr mce)) return;
            if (!mce.getNameAsString().equals("abs")) return;
            if (mce.getArguments().size() != 1) return;
            String absScope = mce.getScope().map(Object::toString).orElse("");
            if (!absScope.isEmpty() && !absScope.equals("Math")) return;
            // Body must reference at least one identifier that appears in EXPR — otherwise
            // there's no plausible way the measure decreases per iteration.
            Expression argExpr = mce.getArgument(0);
            Set<String> argIds = new java.util.LinkedHashSet<>();
            for (NameExpr ne : argExpr.findAll(NameExpr.class)) argIds.add(ne.getNameAsString());
            if (argIds.isEmpty()) return;
            Set<String> bodyAssigned = new java.util.LinkedHashSet<>();
            for (AssignExpr ae : body.findAll(AssignExpr.class)) {
                if (ae.getTarget() instanceof NameExpr ne) bodyAssigned.add(ne.getNameAsString());
            }
            for (UnaryExpr ue : body.findAll(UnaryExpr.class)) {
                UnaryExpr.Operator uop = ue.getOperator();
                if ((uop == UnaryExpr.Operator.PREFIX_INCREMENT
                        || uop == UnaryExpr.Operator.POSTFIX_INCREMENT
                        || uop == UnaryExpr.Operator.PREFIX_DECREMENT
                        || uop == UnaryExpr.Operator.POSTFIX_DECREMENT)
                        && ue.getExpression() instanceof NameExpr ne) {
                    bodyAssigned.add(ne.getNameAsString());
                }
            }
            boolean anyOverlap = argIds.stream().anyMatch(bodyAssigned::contains);
            if (!anyOverlap) return;
            addDecreases("Math.abs(" + argExpr + ")");
        }

        /**
         * True when {@code body} is the canonical subtractive-Euclidean shape:
         * one if-else where the then-branch decrements one variable by the other and
         * the else-branch does the reverse. Recognises both compound (`a -= b`) and
         * explicit (`a = a - b`) forms.
         */
        private boolean isEuclideanSubtractionBody(Statement body, String a, String b) {
            Statement inner = body;
            if (inner instanceof BlockStmt bs && bs.getStatements().size() == 1) {
                inner = bs.getStatements().get(0);
            }
            if (!(inner instanceof IfStmt ifStmt) || ifStmt.getElseStmt().isEmpty()) return false;
            return isSubtractStep(ifStmt.getThenStmt(), a, b)
                    && isSubtractStep(ifStmt.getElseStmt().get(), b, a);
        }

        /** Recognises a single statement of the shape `target -= other` or `target = target - other`. */
        private boolean isSubtractStep(Statement stmt, String target, String other) {
            Statement inner = stmt;
            if (inner instanceof BlockStmt bs && bs.getStatements().size() == 1) {
                inner = bs.getStatements().get(0);
            }
            if (!(inner instanceof ExpressionStmt es)) return false;
            Expression e = es.getExpression();
            if (!(e instanceof AssignExpr ae)) return false;
            if (!(ae.getTarget() instanceof NameExpr tn) || !tn.getNameAsString().equals(target)) return false;
            if (ae.getOperator() == AssignExpr.Operator.MINUS
                    && ae.getValue() instanceof NameExpr vn
                    && vn.getNameAsString().equals(other)) return true;
            if (ae.getOperator() == AssignExpr.Operator.ASSIGN
                    && ae.getValue() instanceof BinaryExpr be
                    && be.getOperator() == BinaryExpr.Operator.MINUS
                    && be.getLeft() instanceof NameExpr ln && ln.getNameAsString().equals(target)
                    && be.getRight() instanceof NameExpr rn && rn.getNameAsString().equals(other)) return true;
            return false;
        }

        /**
         * Net per-iteration delta for {@code counter} as seen at the top level of
         * {@code body}. Returns +N for `counter += N` / `counter++` (or +1 from each),
         * -N for `counter -= N` / `counter--`, 0 if the counter is left unchanged or
         * its update isn't a simple monotonic step (e.g. `counter = counter * 2`).
         * Aggregates multiple statements; conservative — returns 0 if any update is
         * non-monotonic or assigns from a non-counter source.
         */
        private int bodyMonotonicDelta(Statement body, String counter) {
            int delta = 0;
            List<Statement> stmts = (body instanceof BlockStmt bs) ? bs.getStatements() : List.of(body);
            for (Statement s : stmts) {
                if (!(s instanceof ExpressionStmt es)) continue;
                Expression e = es.getExpression();
                if (e instanceof UnaryExpr ue && ue.getExpression() instanceof NameExpr ne
                        && ne.getNameAsString().equals(counter)) {
                    if (ue.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                            || ue.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT) delta += 1;
                    else if (ue.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                            || ue.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) delta -= 1;
                } else if (e instanceof AssignExpr ae && ae.getTarget() instanceof NameExpr tn
                        && tn.getNameAsString().equals(counter)) {
                    if (ae.getOperator() == AssignExpr.Operator.PLUS
                            && ae.getValue().isIntegerLiteralExpr()) {
                        delta += ae.getValue().asIntegerLiteralExpr().asInt();
                    } else if (ae.getOperator() == AssignExpr.Operator.MINUS
                            && ae.getValue().isIntegerLiteralExpr()) {
                        delta -= ae.getValue().asIntegerLiteralExpr().asInt();
                    } else {
                        // Non-monotonic assignment — bail with 0.
                        return 0;
                    }
                }
            }
            return delta;
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
        /**
         * True when {@code init} is structurally bounded above by {@code rhs} via the
         * outer-loop invariants. Specifically recognises:
         * <ul>
         *   <li>{@code init = outerCounter + 1} where there is an enclosing
         *       {@code for (int outerCounter = ...; outerCounter < rhs - 1; ...)} loop
         *       — in that loop {@code outerCounter + 1 <= rhs - 1 + 1 = rhs} holds at
         *       entry, so the inner-loop invariant {@code j <= rhs} is sound.</li>
         *   <li>{@code init = outerCounter + 1} where the enclosing
         *       {@code for (int outerCounter = ...; outerCounter < rhs; ...)} loop
         *       guarantees {@code outerCounter < rhs}, hence
         *       {@code outerCounter + 1 <= rhs}.</li>
         * </ul>
         */
        private boolean isInitBoundedByRhsViaOuterLoop(ForStmt innerLoop, Expression init, String rhs) {
            Expression initExpr = init;
            while (initExpr instanceof EnclosedExpr en) initExpr = en.getInner();
            if (!(initExpr instanceof BinaryExpr be)) return false;
            if (be.getOperator() != BinaryExpr.Operator.PLUS) return false;
            if (!(be.getRight() instanceof IntegerLiteralExpr lit)) return false;
            int delta = lit.asInt();
            if (delta < 0) return false;
            if (!(be.getLeft() instanceof NameExpr outerNe)) return false;
            String outerName = outerNe.getNameAsString();

            // Walk outward looking for a for-loop whose counter is `outerName` and whose
            // compare is `outerName < rhs` or `outerName < rhs - delta` (or weaker).
            com.github.javaparser.ast.Node cur = innerLoop.getParentNode().orElse(null);
            while (cur != null) {
                if (cur instanceof ForStmt outer) {
                    boolean countsThis = false;
                    for (Expression initE : outer.getInitialization()) {
                        if (initE instanceof VariableDeclarationExpr vde) {
                            for (com.github.javaparser.ast.body.VariableDeclarator vd
                                    : vde.getVariables()) {
                                if (vd.getNameAsString().equals(outerName)) {
                                    countsThis = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (countsThis && outer.getCompare().isPresent()
                            && outer.getCompare().get() instanceof BinaryExpr cmp
                            && cmp.getLeft() instanceof NameExpr ln
                            && ln.getNameAsString().equals(outerName)) {
                        String outerRhs = cmp.getRight().toString();
                        // Case 1: `outer < rhs` → outer + 1 <= rhs (delta == 1)
                        if (delta == 1 && outerRhs.equals(rhs)
                                && cmp.getOperator() == BinaryExpr.Operator.LESS) {
                            return true;
                        }
                        // Case 2: `outer < rhs - 1` → outer + 1 <= rhs - 1 < rhs (delta == 1)
                        if (delta == 1 && cmp.getOperator() == BinaryExpr.Operator.LESS
                                && outerRhs.equals(rhs + " - 1")) {
                            return true;
                        }
                    }
                }
                cur = cur.getParentNode().orElse(null);
            }
            return false;
        }

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
                // Loop invariants can reference locals, so we don't require init to be
                // pre-state-expressible. isMethodScopeSafe only allows params/fields;
                // we extend that set with all locals declared anywhere in this method
                // so `int right = chars.length - 1` (chars = s.toCharArray()) qualifies.
                Set<String> scopeNames = new LinkedHashSet<>();
                method.getParameters().forEach(p -> scopeNames.add(p.getNameAsString()));
                for (com.github.javaparser.ast.body.VariableDeclarator vd
                        : method.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
                    scopeNames.add(vd.getNameAsString());
                }
                if (!new SymbolicExecutor().isMethodScopeSafe(
                        init.toString(), method, scopeNames)) continue;

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

                // Verify ALL writes to `name` in the method are monotonic-non-negative
                // (++ or += non-negative-literal). The variable starts non-negative and
                // every write preserves that, so `name >= 0` holds at every program
                // point — regardless of which loop the writes happen in. Common shape:
                // merge-style loops where `i, j, k` are incremented across multiple
                // sequential while-loops; each loop should still get the `>= 0`
                // invariant.
                for (AssignExpr a : method.findAll(AssignExpr.class)) {
                    if (!(a.getTarget() instanceof NameExpr targ) || !targ.getNameAsString().equals(name)) continue;
                    if (a.getOperator() != AssignExpr.Operator.PLUS) continue outer;
                    Expression rhs = a.getValue();
                    // RHS must be known non-negative: either a non-negative integer literal or a
                    // bit-mask expression `<expr> & <non-negative-literal>` (the mask bounds the
                    // result to [0, mask]). Overflow soundness is left to OpenJML as before.
                    if (!isKnownNonNegativeRhs(rhs)) continue outer;
                }
                for (UnaryExpr u : method.findAll(UnaryExpr.class)) {
                    if (!(u.getExpression() instanceof NameExpr ne) || !ne.getNameAsString().equals(name)) continue;
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
