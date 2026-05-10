package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Replace every <code>(= a b)</code> whose arguments are arrays with the equivalent universal
 * <code>(forall ((k D)) (= (select a k) (select b k)))</code> — array extensionality.
 *
 * The downstream {@link Quantifiers} pass then:
 *   - at positive polarity → ground-instantiates the universal over known indices, and
 *   - at negative polarity → skolemises the implied existential witness.
 *
 * This is run BEFORE {@link ArrayPreprocessor} so the new selects participate in the
 * read-over-write rewrite.
 */
public final class ArrayExtensionality {

    private final TermFactory tf;
    private final Map<Integer, Term> cache = new HashMap<>();
    private int counter = 0;

    public ArrayExtensionality(TermFactory tf) { this.tf = tf; }

    public Term rewrite(Term t) {
        Term cached = cache.get(t.id);
        if (cached != null) return cached;
        Term out = doRewrite(t);
        cache.put(t.id, out);
        return out;
    }

    private Term doRewrite(Term t) {
        if (t instanceof Term.Quantifier q) {
            Term newBody = rewrite(q.body);
            if (newBody == q.body) return t;
            return tf.mkQuantifier(q.kind, q.boundNames, q.boundSorts, newBody);
        }
        if (!(t instanceof Term.App app)) return t;
        // Recurse children first.
        List<Term> newArgs = new java.util.ArrayList<>(app.args.size());
        boolean changed = false;
        for (Term c : app.args) {
            Term r = rewrite(c);
            if (r != c) changed = true;
            newArgs.add(r);
        }
        Term cur = changed ? rebuild(app, newArgs) : app;
        if (cur instanceof Term.App cApp && cApp.symbol.equals("=") && cApp.args.size() == 2
                && cApp.args.get(0).sort instanceof Sort.Array arrSort) {
            // Build (forall ((k D)) (= (select a k) (select b k))).
            String idx = "$ext" + (counter++);
            Term k = tf.mkVar(idx, arrSort.domain());
            tf.declareFunction(idx, List.of(), arrSort.domain());
            Term selA = tf.mkAppRaw("select", List.of(cApp.args.get(0), k), arrSort.range());
            Term selB = tf.mkAppRaw("select", List.of(cApp.args.get(1), k), arrSort.range());
            Term body = tf.mkEq(selA, selB);
            return tf.mkQuantifier(Term.Quantifier.Kind.FORALL,
                    List.of(idx), List.of(arrSort.domain()), body);
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
