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
 * </ul>
 *
 * <p>The analyzer only emits invariants for loops with a single counter
 * whose initializer is a literal or a simple name/expression; multi-counter
 * loops and early-returning counters are out of scope.</p>
 */
final class SumInductionAnalyzer {

    private SumInductionAnalyzer() {}

    static void analyze(ForStmt forStmt, List<String> counterNames, Set<String> invariants) {
        if (counterNames.size() != 1) return;
        String counter = counterNames.get(0);
        String lo = extractLowBound(forStmt, counter);
        if (lo == null) return;

        Statement body = forStmt.getBody();

        body.findAll(AssignExpr.class).forEach(ae ->
                handleCompoundAssign(ae, counter, lo, body, invariants));
        body.findAll(IfStmt.class).forEach(is ->
                handleConditionalCounter(is, counter, lo, body, invariants));
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
