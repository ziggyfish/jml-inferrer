package com.z3x.theory;

import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Eager axiomatisation of the theory of arrays. Walks every input term and rewrites
 * <code>(select (store a i v) j)</code> as <code>(ite (= i j) v (select a j))</code>.
 *
 * Iterates to a fixed point. The result mentions only {@code select} on uninterpreted
 * array variables, plus the standard equality and ITE the EUF + propositional layers
 * already handle. Extensionality is NOT covered here — the inferrer corpus does not need it.
 */
public final class ArrayPreprocessor {

    private final TermFactory tf;
    private final Map<Integer, Term> cache = new HashMap<>();

    public ArrayPreprocessor(TermFactory tf) { this.tf = tf; }

    public Term rewrite(Term t) {
        Term cur = t;
        while (true) {
            Term next = rewriteOnce(cur);
            if (next == cur) return next;
            cur = next;
        }
    }

    private Term rewriteOnce(Term t) {
        Term cached = cache.get(t.id);
        if (cached != null) return cached;
        Term result = doRewrite(t);
        cache.put(t.id, result);
        return result;
    }

    private Term doRewrite(Term t) {
        if (!(t instanceof Term.App app)) return t;
        // First rewrite children.
        List<Term> newArgs = new ArrayList<>(app.args.size());
        boolean changed = false;
        for (Term c : app.args) {
            Term r = rewriteOnce(c);
            if (r != c) changed = true;
            newArgs.add(r);
        }
        Term cur = changed ? rebuild(app, newArgs) : app;
        // (select (store a i v) j) → (ite (= i j) v (select a j))
        if (cur instanceof Term.App outer && outer.symbol.equals("select") && outer.args.size() == 2) {
            Term arr = outer.args.get(0);
            Term j = outer.args.get(1);
            if (arr instanceof Term.App inner && inner.symbol.equals("store") && inner.args.size() == 3) {
                Term a = inner.args.get(0);
                Term i = inner.args.get(1);
                Term v = inner.args.get(2);
                Term cond = tf.mkEq(i, j);
                Term elseB = tf.mkAppRaw("select", List.of(a, j), v.sort);
                return rewriteOnce(tf.mkIte(cond, v, elseB));
            }
        }
        return cur;
    }

    private Term rebuild(Term.App app, List<Term> newArgs) {
        return switch (app.symbol) {
            case "and"      -> tf.mkAnd(newArgs);
            case "or"       -> tf.mkOr(newArgs);
            case "not"      -> tf.mkNot(newArgs.get(0));
            case "ite"      -> tf.mkIte(newArgs.get(0), newArgs.get(1), newArgs.get(2));
            case "="        -> tf.mkEq(newArgs.get(0), newArgs.get(1));
            case "+"        -> tf.mkAdd(newArgs);
            case "-"        -> tf.mkSub(newArgs);
            case "*"        -> tf.mkMul(newArgs);
            case "<="       -> tf.mkLe(newArgs.get(0), newArgs.get(1));
            case "<"        -> tf.mkLt(newArgs.get(0), newArgs.get(1));
            case ">="       -> tf.mkGe(newArgs.get(0), newArgs.get(1));
            case ">"        -> tf.mkGt(newArgs.get(0), newArgs.get(1));
            default         -> tf.mkAppRaw(app.symbol, newArgs, app.sort);
        };
    }
}
