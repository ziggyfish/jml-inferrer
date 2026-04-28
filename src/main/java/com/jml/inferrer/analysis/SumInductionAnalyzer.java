package com.jml.inferrer.analysis;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;

import java.util.List;
import java.util.Set;

/**
 * Emits {@code \sum}, {@code \product}, and {@code \num_of} loop invariants
 * that serve as inductive hypotheses when a method's postcondition speaks
 * in terms of the same quantifier. Without these, the SMT solver has to
 * close the recursion from scratch inside the loop exit condition — which
 * almost always times out for a {@code define-fun-rec} encoding. Emitting
 * the hypothesis at loop entry lets z3 / cvc5 carry the recursion along
 * step by step.
 *
 * <p>Patterns recognised for a loop of the shape
 * {@code for (int I = LO; I OP BOUND; I++) BODY}:</p>
 * <ul>
 *   <li>{@code total += summand(I)} &rarr;
 *       {@code total == (\sum int k; LO <= k && k < I; summand(k))}</li>
 *   <li>{@code p *= factor(I)} &rarr;
 *       {@code p == (\product int k; LO <= k && k < I; factor(k))}</li>
 *   <li>{@code if (pred(I)) count++} (or {@code count += 1}) &rarr;
 *       {@code count == (\num_of int k; LO <= k && k < I; pred(k))}</li>
 *   <li>{@code if (pred(I)) total += summand(I)} &rarr;
 *       {@code total == (\sum int k; LO <= k && k < I; pred(k) ? summand(k) : 0)}
 *       (the predicate is folded into the summand rather than the range so that
 *       the {@code define-fun-rec} encoding stays in its supported simple-range
 *       shape; analogously for {@code *=} the empty case is {@code 1})</li>
 * </ul>
 *
 * <p>The analyzer only emits invariants for loops with a single counter
 * whose initializer is a literal or a simple name/expression; multi-counter
 * loops and early-returning counters are out of scope.</p>
 */
final class SumInductionAnalyzer {

    private SumInductionAnalyzer() {}

    static void analyze(ForStmt forStmt, List<String> counterNames, Set<String> invariants) {
        analyze(forStmt, counterNames, invariants, null);
    }

    /**
     * Emits {@code \sum}/{@code \product}/{@code \num_of} loop invariants. When
     * {@code spec} is provided, emission is GATED on the spec already containing a
     * postcondition that references the same quantifier — without a discharge
     * target, the invariant just forces z3 to expand the {@code define-fun-rec}
     * encoding for nothing and the proof times out (the SOLVER_UNKNOWN bucket
     * documented in docs/solver-unknown-analysis.md). Per the user's bug-detection
     * directive, an unverifiable but correct spec is worse than no spec at all.
     */
    static void analyze(ForStmt forStmt, List<String> counterNames, Set<String> invariants,
                        com.jml.inferrer.model.MethodSpecification spec) {
        if (counterNames.size() != 1) return;
        String counter = counterNames.get(0);
        String lo = extractLowBound(forStmt, counter);
        if (lo == null) return;

        if (!hasMatchingQuantifierPostcondition(spec)) return;

        Statement body = forStmt.getBody();

        body.findAll(AssignExpr.class).forEach(ae ->
                handleCompoundAssign(ae, counter, lo, body, invariants));
        body.findAll(IfStmt.class).forEach(is -> {
            handleConditionalCounter(is, counter, lo, body, invariants);
            handleConditionalAccumulator(is, counter, lo, body, invariants);
        });
    }

    /**
     * True when the spec already contains a postcondition referencing one of the
     * three quantifiers this analyzer emits ({@code \sum}, {@code \product},
     * {@code \num_of}). Without such a postcondition, the loop invariants this
     * analyzer would emit have no discharge target — they just force z3 to
     * expand the recursive function definitions and (in practice) hit
     * `(possible timeout)` as documented in the SOLVER_UNKNOWN analysis.
     *
     * Returns {@code true} when {@code spec} is null (back-compat for tests that
     * call the simpler overload without spec context).
     */
    private static boolean hasMatchingQuantifierPostcondition(com.jml.inferrer.model.MethodSpecification spec) {
        if (spec == null) return true;
        for (String post : spec.getPostconditions()) {
            if (post.contains("\\sum") || post.contains("\\product") || post.contains("\\num_of")) {
                return true;
            }
        }
        return false;
    }

    private static String extractLowBound(ForStmt forStmt, String counter) {
        for (Expression init : forStmt.getInitialization()) {
            if (!(init instanceof VariableDeclarationExpr)) continue;
            for (VariableDeclarator vd : ((VariableDeclarationExpr) init).getVariables()) {
                if (vd.getNameAsString().equals(counter)) {
                    return vd.getInitializer().map(Expression::toString).orElse(null);
                }
            }
        }
        return null;
    }

    /**
     * Handles {@code target += RHS(counter)} (sum) and {@code target *= RHS(counter)}
     * (product). The target must not be the loop counter, and the RHS is rewritten
     * to use {@code k} wherever the loop counter appears so it can live under the
     * quantifier binding.
     */
    private static void handleCompoundAssign(AssignExpr ae, String counter, String lo,
                                             Statement body, Set<String> invariants) {
        if (!(ae.getTarget() instanceof NameExpr)) return;
        String target = ((NameExpr) ae.getTarget()).getNameAsString();
        if (target.equals(counter)) return;
        if (isInsideNestedLoop(ae, body)) return;
        if (isInsideIf(ae)) return; // guarded assignments handled by handleConditionalCounter
        // If target is declared outside an enclosing outer loop, the accumulator
        // persists across outer iterations and the single-loop invariant
        // `target == (\sum k; lo..i; ...)` is unsound — it claims the partial
        // sum is only over the current row/iteration, but target holds running
        // totals across all prior rows. Skip emission in that case.
        if (persistsAcrossEnclosingLoop(body, target)) return;

        AssignExpr.Operator op = ae.getOperator();

        // Compound shape: `target += RHS` or `target *= RHS` — RHS is the summand/factor.
        if (op == AssignExpr.Operator.PLUS || op == AssignExpr.Operator.MULTIPLY) {
            String summand = rewriteCounterToK(ae.getValue().toString(), counter);
            if (summand == null) return;
            String quant = (op == AssignExpr.Operator.PLUS) ? "\\sum" : "\\product";
            invariants.add(target + " == (" + quant + " int k; " + lo + " <= k && k < "
                    + counter + "; " + summand + ")");
            return;
        }

        // Explicit shape: `target = target + RHS` or `target = target * RHS` — RHS_REST
        // (the side without `target`) is the summand/factor. Both `target + x` and
        // `x + target` are recognised.
        if (op == AssignExpr.Operator.ASSIGN && ae.getValue() instanceof BinaryExpr be) {
            String summand = extractAccumulatorRhs(be, target);
            if (summand == null) return;
            String quant;
            if (be.getOperator() == BinaryExpr.Operator.PLUS) quant = "\\sum";
            else if (be.getOperator() == BinaryExpr.Operator.MULTIPLY) quant = "\\product";
            else return;
            String summandK = rewriteCounterToK(summand, counter);
            if (summandK == null) return;
            invariants.add(target + " == (" + quant + " int k; " + lo + " <= k && k < "
                    + counter + "; " + summandK + ")");
        }
    }

    /**
     * True when {@code varName} is declared outside the loop that encloses the
     * current loop's body — i.e., the accumulator persists across outer iterations
     * and the current loop's single-variable summary is unsound.
     */
    private static boolean persistsAcrossEnclosingLoop(Statement body, String varName) {
        Node currentLoop = body.getParentNode().orElse(null);
        if (currentLoop == null) return false;
        Node enclosing = currentLoop.getParentNode().orElse(null);
        while (enclosing != null) {
            if (enclosing instanceof ForStmt || enclosing instanceof WhileStmt
                    || enclosing instanceof DoStmt || enclosing instanceof ForEachStmt) {
                return !varDeclaredInside(enclosing, varName);
            }
            enclosing = enclosing.getParentNode().orElse(null);
        }
        return false;
    }

    private static boolean varDeclaredInside(Node scope, String varName) {
        for (VariableDeclarator vd : scope.findAll(VariableDeclarator.class)) {
            if (vd.getNameAsString().equals(varName)) return true;
        }
        return false;
    }

    /**
     * For an expression {@code target + RHS} or {@code RHS + target}, returns the
     * stringified {@code RHS}. Returns null when neither side is a name reference to
     * {@code target}, or when both sides are (which is too ambiguous to summarise).
     */
    private static String extractAccumulatorRhs(BinaryExpr be, String target) {
        boolean leftIsTarget = be.getLeft() instanceof NameExpr lne
                && lne.getNameAsString().equals(target);
        boolean rightIsTarget = be.getRight() instanceof NameExpr rne
                && rne.getNameAsString().equals(target);
        if (leftIsTarget == rightIsTarget) return null;
        return leftIsTarget ? be.getRight().toString() : be.getLeft().toString();
    }

    /**
     * Handles {@code if (pred) counter++} and {@code if (pred) counter += 1}.
     * Emits a {@code \num_of} invariant counting how often the predicate held
     * for indices already iterated.
     */
    private static void handleConditionalCounter(IfStmt is, String counter, String lo,
                                                 Statement body, Set<String> invariants) {
        if (is.getElseStmt().isPresent()) return;
        if (isInsideNestedLoop(is, body)) return;

        Statement then = is.getThenStmt();
        if (then instanceof BlockStmt) {
            BlockStmt bs = (BlockStmt) then;
            if (bs.getStatements().size() != 1) return;
            then = bs.getStatements().get(0);
        }
        if (!(then instanceof ExpressionStmt)) return;
        Expression e = ((ExpressionStmt) then).getExpression();

        String incrTarget = incrementTarget(e);
        if (incrTarget == null || incrTarget.equals(counter)) return;

        String condK = rewriteCounterToK(is.getCondition().toString(), counter);
        if (condK == null) return;

        invariants.add(incrTarget + " == (\\num_of int k; " + lo + " <= k && k < "
                + counter + "; " + condK + ")");
    }

    /**
     * Handles {@code if (pred) target += RHS} (and {@code *=}, plus the explicit
     * {@code target = target + RHS} forms). Emits a {@code \sum}/{@code \product}
     * invariant whose summand is a ternary that contributes only when the
     * predicate held. The range is kept in the simple {@code lo <= k && k < counter}
     * shape so that the fork's {@code define-fun-rec} encoding stays in its
     * supported form.
     *
     * Only fires when the then-branch is a single accumulator statement and there
     * is no else clause; mirrors the gating in handleConditionalCounter.
     */
    private static void handleConditionalAccumulator(IfStmt is, String counter, String lo,
                                                     Statement body, Set<String> invariants) {
        if (is.getElseStmt().isPresent()) return;
        if (isInsideNestedLoop(is, body)) return;

        Statement then = is.getThenStmt();
        if (then instanceof BlockStmt) {
            BlockStmt bs = (BlockStmt) then;
            if (bs.getStatements().size() != 1) return;
            then = bs.getStatements().get(0);
        }
        if (!(then instanceof ExpressionStmt)) return;
        Expression e = ((ExpressionStmt) then).getExpression();
        if (!(e instanceof AssignExpr ae)) return;
        if (!(ae.getTarget() instanceof NameExpr)) return;

        String target = ((NameExpr) ae.getTarget()).getNameAsString();
        if (target.equals(counter)) return;
        if (persistsAcrossEnclosingLoop(body, target)) return;

        AssignExpr.Operator op = ae.getOperator();
        String quant;
        String identity;
        String summand;

        if (op == AssignExpr.Operator.PLUS || op == AssignExpr.Operator.MULTIPLY) {
            boolean isSum = op == AssignExpr.Operator.PLUS;
            quant = isSum ? "\\sum" : "\\product";
            identity = isSum ? "0" : "1";
            summand = rewriteCounterToK(ae.getValue().toString(), counter);
        } else if (op == AssignExpr.Operator.ASSIGN && ae.getValue() instanceof BinaryExpr be) {
            String rhs = extractAccumulatorRhs(be, target);
            if (rhs == null) return;
            boolean isSum;
            if (be.getOperator() == BinaryExpr.Operator.PLUS) { isSum = true; }
            else if (be.getOperator() == BinaryExpr.Operator.MULTIPLY) { isSum = false; }
            else return;
            quant = isSum ? "\\sum" : "\\product";
            identity = isSum ? "0" : "1";
            summand = rewriteCounterToK(rhs, counter);
        } else {
            return;
        }
        if (summand == null) return;

        // Skip "+= 1" / "*= 1" — handleConditionalCounter already covers the +=1 case
        // with \num_of, and a constant *=1 is a no-op summary not worth emitting.
        if (summand.equals("1")) return;

        String condK = rewriteCounterToK(is.getCondition().toString(), counter);
        if (condK == null) return;

        invariants.add(target + " == (" + quant + " int k; " + lo + " <= k && k < "
                + counter + "; (" + condK + ") ? (" + summand + ") : " + identity + ")");
    }

    /**
     * Returns the name being incremented by {@code expr} if it's a recognised
     * shape ({@code v++}, {@code ++v}, {@code v += 1}, {@code v = v + 1}),
     * otherwise null.
     */
    private static String incrementTarget(Expression expr) {
        if (expr instanceof UnaryExpr) {
            UnaryExpr ue = (UnaryExpr) expr;
            if ((ue.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                    || ue.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT)
                    && ue.getExpression() instanceof NameExpr) {
                return ((NameExpr) ue.getExpression()).getNameAsString();
            }
            return null;
        }
        if (expr instanceof AssignExpr) {
            AssignExpr ae = (AssignExpr) expr;
            if (!(ae.getTarget() instanceof NameExpr)) return null;
            String target = ((NameExpr) ae.getTarget()).getNameAsString();
            if (ae.getOperator() == AssignExpr.Operator.PLUS
                    && ae.getValue() instanceof IntegerLiteralExpr
                    && ((IntegerLiteralExpr) ae.getValue()).asInt() == 1) {
                return target;
            }
            if (ae.getOperator() == AssignExpr.Operator.ASSIGN
                    && ae.getValue() instanceof BinaryExpr be
                    && be.getOperator() == BinaryExpr.Operator.PLUS
                    && be.getLeft() instanceof NameExpr lne
                    && lne.getNameAsString().equals(target)
                    && be.getRight() instanceof IntegerLiteralExpr ie
                    && ie.asInt() == 1) {
                return target;
            }
        }
        return null;
    }

    /**
     * Rewrites occurrences of {@code counter} to {@code k} as whole-word
     * substitutions, so an accumulator expression can live under the
     * quantifier binding. Returns null if the expression contains no
     * reference to the counter (that shape doesn't make sense as an
     * inductive summand — it'd be a constant sum of the loop trip count).
     */
    private static String rewriteCounterToK(String expr, String counter) {
        String rewritten = expr.replaceAll("\\b" + java.util.regex.Pattern.quote(counter) + "\\b", "k");
        if (rewritten.equals(expr)) {
            // No counter reference; summand is constant with respect to the index.
            // We still permit this (e.g. `count += 1` becomes `\sum ... 1`), but
            // for the caller it generally isn't useful beyond what existing
            // analyzers already emit.
            return rewritten;
        }
        return rewritten;
    }

    private static boolean isInsideNestedLoop(Node node, Statement outerBody) {
        Node cur = node;
        while (cur.getParentNode().isPresent()) {
            Node parent = cur.getParentNode().get();
            if (parent == outerBody) return false;
            if (parent instanceof ForStmt || parent instanceof WhileStmt
                    || parent instanceof DoStmt || parent instanceof ForEachStmt) {
                return true;
            }
            cur = parent;
        }
        return false;
    }

    private static boolean isInsideIf(Node node) {
        Node cur = node;
        while (cur.getParentNode().isPresent()) {
            Node parent = cur.getParentNode().get();
            if (parent instanceof IfStmt) return true;
            if (parent instanceof ForStmt || parent instanceof WhileStmt
                    || parent instanceof DoStmt || parent instanceof ForEachStmt) {
                return false;
            }
            cur = parent;
        }
        return false;
    }
}
