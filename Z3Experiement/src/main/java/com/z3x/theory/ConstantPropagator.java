package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Substitute known constant equalities throughout the formula.
 *
 * Scans top-level assertions of the form <code>(= X V)</code> where V is an Int/Real/Bool/BV
 * constant and X is an uninterpreted atom (or interpreted atom whose value is forced). Replaces
 * every occurrence of X with V in the rest of the formula.
 *
 * Motivation: the recursive-function expander emits axioms like
 *     (jprod arr 0 3) = (select arr 0) * (jprod arr 1 3)
 * Without constant propagation, LIA can't evaluate the multiplication because both factors are
 * opaque. With propagation (after seeing (= (select arr 0) 2)), this becomes
 *     (jprod arr 0 3) = 2 * (jprod arr 1 3)
 * which is linear in (jprod arr 1 3) and now soluble.
 *
 * Only safe at top level (under positive polarity). Equalities inside negations, disjunctions,
 * or quantifier bodies are not used as substitutions.
 */
public final class ConstantPropagator {

    private final TermFactory tf;
    private final Map<Integer, Term> subMap = new HashMap<>();

    public ConstantPropagator(TermFactory tf) { this.tf = tf; }

    /** Scan the top-level assertions and collect (term-id → const-value) substitutions. */
    public void collectEqualities(List<Term> assertions) {
        for (Term t : assertions) {
            collectFromTopLevel(t);
        }
    }

    private void collectFromTopLevel(Term t) {
        if (t instanceof Term.App app && app.symbol.equals("=") && app.args.size() == 2) {
            Term l = app.args.get(0);
            Term r = app.args.get(1);
            // Only substitute when the non-constant side is a "simple" term — either a
            // Term.Var (uninterpreted constant) or a uninterpreted function application like
            // (select arr K) where the args are themselves constants. Substituting an
            // arbitrary App expression risks erasing the only linear-arithmetic constraint
            // tying its sub-vars together: replacing `(+ 1 x) → 7` removes the information
            // that `x = 6`, because the substituted term `(= 7 (+ 1 x))` simplifies to true.
            if (isConst(r) && isSubstitutable(l)) subMap.putIfAbsent(l.id, r);
            else if (isConst(l) && isSubstitutable(r)) subMap.putIfAbsent(r.id, l);
        }
        if (t instanceof Term.App app && app.symbol.equals("and")) {
            for (Term c : app.args) collectFromTopLevel(c);
        }
    }

    /** Atoms safe to substitute everywhere: variables and uninterpreted Apps. We reject
     *  arithmetic/boolean operators because substituting their result would erase the
     *  constraint linking their operands. Uninterpreted Apps like (select arr 0) or (f x y)
     *  are reference-valued and safe to substitute by Term-ID regardless of their args. */
    private static boolean isSubstitutable(Term t) {
        if (t instanceof Term.Var) return true;
        if (!(t instanceof Term.App app)) return false;
        return switch (app.symbol) {
            case "+","-","*","div","mod","abs","ite","and","or","not","=>","=","<","<=",">=",">",
                 "bvadd","bvsub","bvmul","bvneg","bvnot","bvand","bvor","bvxor",
                 "bvshl","bvlshr","bvashr","bvudiv","bvurem","bvsdiv","bvsrem","bvsmod",
                 "bvult","bvule","bvugt","bvuge","bvslt","bvsle","bvsgt","bvsge",
                 "str.++","str.len","str.at","str.substr" -> false;
            default -> true;
        };
    }

    private static boolean isConst(Term t) {
        return t instanceof Term.IntConst || t instanceof Term.RatConst
                || t instanceof Term.BoolConst || t instanceof Term.BvConst
                || t instanceof Term.StrConst;
    }

    public boolean hasSubstitutions() { return !subMap.isEmpty(); }

    /** Substitute throughout {@code t}, applying the collected constant equalities. */
    public Term apply(Term t) {
        Map<Integer, Term> cache = new HashMap<>();
        return rewrite(t, cache);
    }

    private Term rewrite(Term t, Map<Integer, Term> cache) {
        Term hit = subMap.get(t.id);
        if (hit != null) return hit;
        Term cached = cache.get(t.id);
        if (cached != null) return cached;
        Term out = doRewrite(t, cache);
        cache.put(t.id, out);
        return out;
    }

    private Term doRewrite(Term t, Map<Integer, Term> cache) {
        if (t instanceof Term.App app) {
            List<Term> newArgs = new java.util.ArrayList<>(app.args.size());
            boolean changed = false;
            for (Term c : app.args) {
                Term r = rewrite(c, cache);
                if (r != c) changed = true;
                newArgs.add(r);
            }
            if (!changed) return t;
            return rebuild(app, newArgs);
        }
        if (t instanceof Term.Quantifier q) {
            Term newBody = rewrite(q.body, cache);
            if (newBody == q.body) return t;
            return tf.mkQuantifier(q.kind, q.boundNames, q.boundSorts, newBody);
        }
        return t;
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
