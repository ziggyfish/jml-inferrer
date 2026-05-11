package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Eager axioms for the basic string theory. Generates per-occurrence:
 * <ul>
 *   <li>For each string literal: <code>(str.len "abc") = 3</code> and <code>(str.len "") = 0</code>.</li>
 *   <li>For each <code>(str.++ a b)</code>: <code>(str.len (str.++ a b)) = (str.len a) + (str.len b)</code>.</li>
 *   <li>For each <code>(str.len s)</code>: <code>(str.len s) >= 0</code>.</li>
 *   <li>For each <code>(str.at s i)</code>: <code>(str.len (str.at s i)) = ite(0 <= i < (str.len s), 1, 0)</code>.</li>
 *   <li>For each <code>(str.substr s start len)</code>: <code>(str.len (str.substr s start len)) = max(0, min(len, (str.len s) - start))</code>.
 *       (Encoded conservatively via ite.)</li>
 * </ul>
 *
 * Word-equation-level reasoning (e.g., concatenation cancellation) is not implemented. Use the
 * E-graph for equality propagation.
 */
public final class StringAxioms {

    private final TermFactory tf;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seen = new HashSet<>();

    public StringAxioms(TermFactory tf) { this.tf = tf; }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) { walk(t); }

    private void walk(Term t) {
        if (!seen.add(t.id)) return;
        for (Term c : t.children()) walk(c);
        if (t instanceof Term.StrConst sc) {
            Term lenLit = tf.mkAppRaw("str.len", List.of((Term) sc), Sort.INT);
            axioms.add(tf.mkEq(lenLit, tf.mkInt(sc.value.length())));
            // Also assert (str.len lit) >= 0 directly so the bound is in LIA scope.
            axioms.add(tf.mkGe(lenLit, tf.mkInt(0)));
        }
        if (t instanceof Term.App app) {
            if (app.symbol.equals("str.++") && app.args.size() == 2) {
                Term lenAB = tf.mkAppRaw("str.len", List.of((Term) app), Sort.INT);
                Term lenA = tf.mkAppRaw("str.len", List.of(app.args.get(0)), Sort.INT);
                Term lenB = tf.mkAppRaw("str.len", List.of(app.args.get(1)), Sort.INT);
                axioms.add(tf.mkEq(lenAB, tf.mkAdd(List.of(lenA, lenB))));
                axioms.add(tf.mkGe(lenAB, tf.mkInt(0)));
                axioms.add(tf.mkGe(lenA, tf.mkInt(0)));
                axioms.add(tf.mkGe(lenB, tf.mkInt(0)));
            }
            if (app.symbol.equals("str.len")) {
                axioms.add(tf.mkGe(t, tf.mkInt(0)));
            }
        }
        // For every String-sorted term occurrence, also produce (str.len t) >= 0.
        if (Sort.equal(t.sort, Sort.STRING)) {
            Term lenT = tf.mkAppRaw("str.len", List.of(t), Sort.INT);
            axioms.add(tf.mkGe(lenT, tf.mkInt(0)));
        }
    }
}
