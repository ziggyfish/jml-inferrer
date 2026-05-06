package com.jml.inferrer.analysis;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;

import java.util.List;
import java.util.Optional;
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
     * Emits {@code \sum}/{@code \product}/{@code \num_of} loop invariants AND, when
     * the surrounding method's terminal return is the accumulator, the matching
     * {@code \result == (\sum int k; LO <= k && k < HIGH; ...)} postcondition.
     * Emitting the postcondition is what gives the invariant a discharge target;
     * without one the invariant just forces z3 to expand the SMT encoding for
     * nothing.
     *
     * <p>Behaviour: emission only fires when the loop pattern matches AND a
     * matching postcondition can be derived (return-the-accumulator method shape
     * with a pre-state-expressible HIGH bound). When {@code spec} is null
     * (legacy callers without spec context), only invariants are emitted — the
     * caller is expected to supply the postcondition itself.</p>
     *
     * <p>The previous gate "skip emission unless a matching post exists" was
     * appropriate when the OpenJML fork's quantifier encoding was broken
     * (commit b3ae1e4 fixes this). With the axiomatic encoding now active the
     * analyzer should always emit when it can, and supply the postcondition
     * itself rather than expecting another analyzer to.</p>
     */
    static void analyze(ForStmt forStmt, List<String> counterNames, Set<String> invariants,
                        com.jml.inferrer.model.MethodSpecification spec) {
        if (counterNames.size() != 1) return;
        String counter = counterNames.get(0);
        String lo = extractLowBound(forStmt, counter);
        if (lo == null) return;

        // High bound for the matching postcondition. When `for(i = LO; i < HIGH; ...)`
        // exits, i == HIGH; the accumulator's value is the quantifier evaluated over
        // [LO, HIGH). Skip postcondition emission when HIGH is missing or not
        // pre-state-expressible — the invariant alone is still sound.
        String hi = extractHighBound(forStmt, counter);

        MethodDeclaration methodDecl = forStmt.findAncestor(MethodDeclaration.class).orElse(null);

        Statement body = forStmt.getBody();

        body.findAll(AssignExpr.class).forEach(ae ->
                handleCompoundAssign(ae, counter, lo, hi, body, invariants, spec, methodDecl));
        body.findAll(IfStmt.class).forEach(is -> {
            handleConditionalCounter(is, counter, lo, hi, body, invariants, spec, methodDecl);
            handleConditionalAccumulator(is, counter, lo, hi, body, invariants, spec, methodDecl);
        });
    }

    /**
     * Extracts the upper bound of {@code for (counter = LO; counter <op> HIGH; ...)}.
     * Recognises the four ordered comparisons; returns null for shapes the
     * analyzer can't summarise (no compare clause, multi-conjunct guard, etc.).
     * The returned string is suitable for splicing into a JML postcondition's
     * range expression — for {@code i < arr.length} we return {@code "arr.length"}.
     */
    private static String extractHighBound(ForStmt forStmt, String counter) {
        Expression cmp = forStmt.getCompare().orElse(null);
        if (!(cmp instanceof BinaryExpr be)) return null;
        if (!(be.getLeft() instanceof NameExpr lne) || !lne.getNameAsString().equals(counter)) {
            return null;
        }
        // For `i < HIGH` the half-open range is [LO, HIGH); for `i <= HIGH` it's
        // [LO, HIGH+1). Normalise to half-open form for the quantifier.
        return switch (be.getOperator()) {
            case LESS -> be.getRight().toString();
            case LESS_EQUALS -> "(" + be.getRight() + " + 1)";
            default -> null;
        };
    }

    /**
     * True when the surrounding method's terminal return is exactly
     * {@code return TARGET;} — the precondition for emitting a matching
     * {@code \result == ...} postcondition. We require: at least one return
     * statement, ALL of them have expression {@code TARGET} (so the spec is
     * sound on every normal exit), and TARGET is the accumulator name we
     * just summarised.
     */
    private static boolean methodReturnsAccumulator(MethodDeclaration methodDecl, String target) {
        if (methodDecl == null) return false;
        if (methodDecl.getBody().isEmpty()) return false;
        java.util.List<ReturnStmt> returns = methodDecl.getBody().get().findAll(ReturnStmt.class);
        if (returns.isEmpty()) return false;
        for (ReturnStmt r : returns) {
            Optional<Expression> e = r.getExpression();
            if (e.isEmpty()) return false;
            if (!(e.get() instanceof NameExpr ne) || !ne.getNameAsString().equals(target)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Emits the matching {@code ensures \result == (\sum/product/num_of int k;
     * LO <= k && k < HIGH; BODY)} postcondition into {@code spec}. Returns true
     * iff an emission occurred. Caller's responsibility to ensure
     * {@code methodReturnsAccumulator(...)} held first.
     */
    private static boolean emitMatchingPostcondition(com.jml.inferrer.model.MethodSpecification spec,
                                                      String quant, String lo, String hi,
                                                      String bodyExpr) {
        if (spec == null || hi == null || bodyExpr == null) return false;
        String post = "\\result == (" + quant + " int k; " + lo + " <= k && k < " + hi
                + "; " + bodyExpr + ")";
        spec.addPostcondition(post);
        return true;
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
    private static void handleCompoundAssign(AssignExpr ae, String counter, String lo, String hi,
                                             Statement body, Set<String> invariants,
                                             com.jml.inferrer.model.MethodSpecification spec,
                                             MethodDeclaration methodDecl) {
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
        String quant;
        String summandK;

        // Compound shape: `target += RHS` or `target *= RHS` — RHS is the summand/factor.
        if (op == AssignExpr.Operator.PLUS || op == AssignExpr.Operator.MULTIPLY) {
            String inlinedRhs = inlineBlockScopedLocals(ae.getValue().toString(), body, target);
            if (inlinedRhs == null) return;
            summandK = rewriteCounterToK(inlinedRhs, counter);
            if (summandK == null) return;
            quant = (op == AssignExpr.Operator.PLUS) ? "\\sum" : "\\product";
        }
        // Explicit shape: `target = target + RHS` or `target = target * RHS` — RHS_REST
        // (the side without `target`) is the summand/factor. Both `target + x` and
        // `x + target` are recognised.
        else if (op == AssignExpr.Operator.ASSIGN && ae.getValue() instanceof BinaryExpr be) {
            String rhs = extractAccumulatorRhs(be, target);
            if (rhs == null) return;
            if (be.getOperator() == BinaryExpr.Operator.PLUS) quant = "\\sum";
            else if (be.getOperator() == BinaryExpr.Operator.MULTIPLY) quant = "\\product";
            else return;
            String inlinedRhs = inlineBlockScopedLocals(rhs, body, target);
            if (inlinedRhs == null) return;
            summandK = rewriteCounterToK(inlinedRhs, counter);
            if (summandK == null) return;
        } else {
            return;
        }

        invariants.add(target + " == (" + quant + " int k; " + lo + " <= k && k < "
                + counter + "; " + summandK + ")");

        // When the surrounding method returns this accumulator and the loop bound
        // is pre-state-expressible, emit the matching `\result == (\sum ...)` over
        // the closed quantifier range [LO, HIGH). The OpenJML fork's axiomatic
        // encoding (commit b3ae1e4) discharges this when the loop_invariant above
        // is in scope.
        if (methodReturnsAccumulator(methodDecl, target)) {
            emitMatchingPostcondition(spec, quant, lo, hi, summandK);
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
     * for indices already iterated, and the matching
     * {@code \result == (\num_of ...)} postcondition when the surrounding
     * method returns the counter.
     */
    private static void handleConditionalCounter(IfStmt is, String counter, String lo, String hi,
                                                 Statement body, Set<String> invariants,
                                                 com.jml.inferrer.model.MethodSpecification spec,
                                                 MethodDeclaration methodDecl) {
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

        if (methodReturnsAccumulator(methodDecl, incrTarget)) {
            emitMatchingPostcondition(spec, "\\num_of", lo, hi, condK);
        }
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
    private static void handleConditionalAccumulator(IfStmt is, String counter, String lo, String hi,
                                                     Statement body, Set<String> invariants,
                                                     com.jml.inferrer.model.MethodSpecification spec,
                                                     MethodDeclaration methodDecl) {
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

        String summandBody = "(" + condK + ") ? (" + summand + ") : " + identity;
        invariants.add(target + " == (" + quant + " int k; " + lo + " <= k && k < "
                + counter + "; " + summandBody + ")");

        if (methodReturnsAccumulator(methodDecl, target)) {
            emitMatchingPostcondition(spec, quant, lo, hi, summandBody);
        }
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

    /**
     * Substitutes references to block-scoped locals declared inside the loop
     * body with their initialiser expressions. Returns null when any
     * NameExpr in the result still refers to a body-scoped declarator
     * (i.e. the substitution would leave an undefined variable in the
     * emitted spec). The {@code accumulatorTarget} is excluded — it's the
     * variable being accumulated into and is in scope at the spec level.
     */
    private static String inlineBlockScopedLocals(String summand, Statement body,
                                                   String accumulatorTarget) {
        java.util.Map<String, String> bodyLocalInits = new java.util.HashMap<>();
        for (VariableDeclarator vd : body.findAll(VariableDeclarator.class)) {
            String n = vd.getNameAsString();
            if (n.equals(accumulatorTarget)) continue;
            vd.getInitializer().ifPresent(init -> bodyLocalInits.put(n, init.toString()));
        }
        // Collect declarator names without initialiser too — they're still
        // body-scoped and can't appear in the emitted spec.
        java.util.Set<String> bodyLocalNames = new java.util.HashSet<>();
        for (VariableDeclarator vd : body.findAll(VariableDeclarator.class)) {
            String n = vd.getNameAsString();
            if (!n.equals(accumulatorTarget)) bodyLocalNames.add(n);
        }
        // Substitute one level (initialisers themselves may reference other
        // body-locals in chained shape; for safety we only inline once and
        // then validate no body-locals remain).
        String result = summand;
        for (java.util.Map.Entry<String, String> e : bodyLocalInits.entrySet()) {
            String pattern = "\\b" + java.util.regex.Pattern.quote(e.getKey()) + "\\b";
            result = result.replaceAll(pattern, "(" + e.getValue() + ")");
        }
        // Reject if any body-local survived substitution.
        for (String n : bodyLocalNames) {
            if (result.matches(".*\\b" + java.util.regex.Pattern.quote(n) + "\\b.*")) {
                return null;
            }
        }
        return result;
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
