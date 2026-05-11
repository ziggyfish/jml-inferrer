package com.z3x.theory;

import com.z3x.solver.Solver;
import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Ground-unfolds applications of (define-fun) and (define-fun-rec) functions.
 *
 * Strategy: walk every input term, find App nodes whose symbol is a registered function
 * definition, and emit
 *     (= app body[args/params])
 * as a side assertion. Then recurse into the substituted body — if it contains another
 * recursive call, unfold that too. The expansion is bounded by:
 *  - a depth cap (so a recursion that doesn't reach its base case bails out as an opaque atom),
 *  - a global instance cap (so a wide call graph can't blow up the formula).
 *
 * This is sound but incomplete. When bounds are constants and the recursion's base case is
 * reachable, unfolding terminates and the formula is fully ground. When bounds are symbolic
 * (e.g. (\sum arr 0 n) with n unbound), the leaf calls remain as opaque atoms — the solver
 * will then return {@code unknown}-equivalent (typically sat by default model). For the JML
 * verification corpus, the dominant case is bounded recursion with concrete loop bounds, which
 * this handles fully.
 *
 * The standard {@code \sum}/{@code \product}/{@code \num_of} encoding (as emitted by the
 * patched OpenJML fork) looks like:
 *
 *   (define-fun-rec jsum ((arr (Array Int Int)) (lo Int) (hi Int)) Int
 *     (ite (&gt;= lo hi) 0 (+ (select arr lo) (jsum arr (+ lo 1) hi))))
 *
 * Unfolding (jsum arr 0 3) drives the ite condition `(&gt;= 0 3)` to false, then to true on the
 * fourth call, producing the fully ground sum.
 */
public final class RecursiveExpander {

    private static final int MAX_DEPTH = 256;
    private static final int MAX_INSTANCES = 4096;

    private final TermFactory tf;
    private final Map<String, Solver.FunDef> defs;
    private final List<Term> axioms = new ArrayList<>();
    /** Apps already emitted, by Term id — avoid duplicate axioms. */
    private final Set<Integer> emitted = new HashSet<>();
    private int instances = 0;

    public RecursiveExpander(TermFactory tf, Map<String, Solver.FunDef> defs) {
        this.tf = tf;
        this.defs = defs;
    }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) { walk(t, new HashSet<>()); }

    private void walk(Term t, Set<Integer> visited) {
        if (!visited.add(t.id)) return;
        for (Term c : t.children()) walk(c, visited);
        if (t instanceof Term.App app && defs.containsKey(app.symbol)) {
            unfold(app, 0);
        }
    }

    /** Emit (= app body[args/params]); recurse on substituted body to keep unfolding. */
    private void unfold(Term.App app, int depth) {
        if (!emitted.add(app.id)) return;
        if (instances >= MAX_INSTANCES) return;
        if (depth >= MAX_DEPTH) return;
        Solver.FunDef def = defs.get(app.symbol);
        if (def == null || app.args.size() != def.paramNames().size()) return;
        Map<String, Term> sub = new HashMap<>();
        for (int i = 0; i < def.paramNames().size(); i++) {
            sub.put(def.paramNames().get(i), app.args.get(i));
        }
        Term body = Quantifiers.substituteWith(tf, def.body(), sub);
        // Try to simplify ite, eq, etc. via the factory's built-in folding.
        Term simplified = simplify(body);
        axioms.add(tf.mkEq(app, simplified));
        instances++;
        // Walk the simplified body for further recursive calls.
        walkUnfoldRec(simplified, depth + 1);
    }

    private void walkUnfoldRec(Term t, int depth) {
        if (instances >= MAX_INSTANCES) return;
        if (t instanceof Term.App app && defs.containsKey(app.symbol)) {
            unfold(app, depth);
            return;
        }
        for (Term c : t.children()) walkUnfoldRec(c, depth);
    }

    /** Best-effort constant folding for the common ITE recursion-base pattern. */
    private Term simplify(Term t) {
        if (!(t instanceof Term.App app)) return t;
        // Recurse children.
        List<Term> newArgs = new ArrayList<>(app.args.size());
        boolean changed = false;
        for (Term c : app.args) {
            Term r = simplify(c);
            if (r != c) changed = true;
            newArgs.add(r);
        }
        Term cur = changed ? rebuild(app, newArgs) : app;
        // ITE with const condition.
        if (cur instanceof Term.App ce && ce.symbol.equals("ite") && ce.args.get(0) instanceof Term.BoolConst bc) {
            return bc.value ? ce.args.get(1) : ce.args.get(2);
        }
        // Comparisons of two int constants.
        if (cur instanceof Term.App ce && ce.args.size() == 2
                && ce.args.get(0) instanceof Term.IntConst a
                && ce.args.get(1) instanceof Term.IntConst b) {
            int cmp = a.value.compareTo(b.value);
            switch (ce.symbol) {
                case "<":  return tf.mkBool(cmp < 0);
                case "<=": return tf.mkBool(cmp <= 0);
                case ">":  return tf.mkBool(cmp > 0);
                case ">=": return tf.mkBool(cmp >= 0);
                default: break;
            }
        }
        return cur;
    }

    private Term rebuild(Term.App app, List<Term> newArgs) {
        return switch (app.symbol) {
            case "and" -> tf.mkAnd(newArgs);
            case "or"  -> tf.mkOr(newArgs);
            case "not" -> tf.mkNot(newArgs.get(0));
            case "ite" -> tf.mkIte(newArgs.get(0), newArgs.get(1), newArgs.get(2));
            case "="   -> tf.mkEq(newArgs.get(0), newArgs.get(1));
            case "+"   -> tf.mkAdd(newArgs);
            case "-"   -> tf.mkSub(newArgs);
            case "*"   -> tf.mkMul(newArgs);
            case "<="  -> tf.mkLe(newArgs.get(0), newArgs.get(1));
            case "<"   -> tf.mkLt(newArgs.get(0), newArgs.get(1));
            case ">="  -> tf.mkGe(newArgs.get(0), newArgs.get(1));
            case ">"   -> tf.mkGt(newArgs.get(0), newArgs.get(1));
            default    -> tf.mkAppRaw(app.symbol, newArgs, app.sort);
        };
    }
}
