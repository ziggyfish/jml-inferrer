package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Lift non-Boolean if-then-else into fresh constants plus side-conditions.
 *
 * For each subterm <code>(ite c t e)</code> whose result sort is not Bool, introduce a fresh
 * variable <code>X</code> of that sort and emit the side-assertion
 *     <code>(and (=&gt; c (= X t)) (=&gt; (not c) (= X e)))</code>
 * then replace the ITE with <code>X</code>. Repeated occurrences of the same ITE share their
 * skolem so the side-conditions stay linear in formula size.
 *
 * Boolean ITEs are left intact — the Tseitin layer handles them directly.
 */
public final class IteEliminator {

    private final TermFactory tf;
    private final Map<Integer, Term> rewriteCache = new HashMap<>();
    private final List<Term> sideAssertions = new ArrayList<>();
    private int counter = 0;

    public IteEliminator(TermFactory tf) { this.tf = tf; }

    public List<Term> sideAssertions() { return sideAssertions; }

    public Term rewrite(Term t) {
        Term cached = rewriteCache.get(t.id);
        if (cached != null) return cached;
        Term out = doRewrite(t);
        rewriteCache.put(t.id, out);
        return out;
    }

    private Term doRewrite(Term t) {
        if (!(t instanceof Term.App app)) return t;
        List<Term> newArgs = new ArrayList<>(app.args.size());
        boolean changed = false;
        for (Term c : app.args) {
            Term r = rewrite(c);
            if (r != c) changed = true;
            newArgs.add(r);
        }
        Term cur = changed ? rebuild(app, newArgs) : app;
        if (cur instanceof Term.App outer && outer.symbol.equals("ite") && outer.sort != Sort.BOOL) {
            Term c = outer.args.get(0);
            Term tBranch = outer.args.get(1);
            Term eBranch = outer.args.get(2);
            String name = "$ite" + (counter++);
            tf.declareFunction(name, List.of(), outer.sort);
            Term skolem = tf.mkVar(name, outer.sort);
            sideAssertions.add(tf.mkImplies(c, tf.mkEq(skolem, tBranch)));
            sideAssertions.add(tf.mkImplies(tf.mkNot(c), tf.mkEq(skolem, eBranch)));
            return skolem;
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
