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
            if (app.symbol.equals("str.at") && app.args.size() == 2) {
                // str.at returns a string of length 1 when index is in-bounds, else "".
                Term s = app.args.get(0);
                Term idx = app.args.get(1);
                Term lenS = tf.mkAppRaw("str.len", List.of(s), Sort.INT);
                Term lenAt = tf.mkAppRaw("str.len", List.of((Term) app), Sort.INT);
                Term inBounds = tf.mkAnd(List.of(tf.mkGe(idx, tf.mkInt(0)), tf.mkLt(idx, lenS)));
                axioms.add(tf.mkEq(lenAt, tf.mkIte(inBounds, tf.mkInt(1), tf.mkInt(0))));
            }
            if (app.symbol.equals("str.substr") && app.args.size() == 3) {
                // str.substr s start len: result length = max(0, min(len, len(s) - start)) if start in [0, len(s)] else 0.
                Term s = app.args.get(0);
                Term start = app.args.get(1);
                Term l = app.args.get(2);
                Term lenS = tf.mkAppRaw("str.len", List.of(s), Sort.INT);
                Term lenSub = tf.mkAppRaw("str.len", List.of((Term) app), Sort.INT);
                Term validStart = tf.mkAnd(List.of(tf.mkGe(start, tf.mkInt(0)), tf.mkLe(start, lenS)));
                Term remaining = tf.mkSub(List.of(lenS, start));
                // Upper bound: min(l, remaining), clamped at 0.
                Term capped = tf.mkIte(tf.mkLt(l, remaining), l, remaining);
                Term nonNeg = tf.mkIte(tf.mkLt(capped, tf.mkInt(0)), tf.mkInt(0), capped);
                axioms.add(tf.mkEq(lenSub, tf.mkIte(validStart, nonNeg, tf.mkInt(0))));
                axioms.add(tf.mkGe(lenSub, tf.mkInt(0)));
            }
            if (app.symbol.equals("str.contains") && app.args.size() == 2) {
                // s contains t implies len(t) <= len(s).
                Term s = app.args.get(0);
                Term sub = app.args.get(1);
                Term lenS = tf.mkAppRaw("str.len", List.of(s), Sort.INT);
                Term lenSub = tf.mkAppRaw("str.len", List.of(sub), Sort.INT);
                axioms.add(tf.mkImplies((Term) app, tf.mkLe(lenSub, lenS)));
            }
            if (app.symbol.equals("str.prefixof") && app.args.size() == 2) {
                // prefix t of s implies len(t) <= len(s).
                Term pre = app.args.get(0);
                Term s = app.args.get(1);
                axioms.add(tf.mkImplies((Term) app,
                        tf.mkLe(tf.mkAppRaw("str.len", List.of(pre), Sort.INT),
                                tf.mkAppRaw("str.len", List.of(s), Sort.INT))));
            }
            if (app.symbol.equals("str.suffixof") && app.args.size() == 2) {
                Term suf = app.args.get(0);
                Term s = app.args.get(1);
                axioms.add(tf.mkImplies((Term) app,
                        tf.mkLe(tf.mkAppRaw("str.len", List.of(suf), Sort.INT),
                                tf.mkAppRaw("str.len", List.of(s), Sort.INT))));
            }
            if (app.symbol.equals("str.indexof") && app.args.size() == 3) {
                // result is -1 (not found) or in [0, len(s)).
                Term s = app.args.get(0);
                Term lenS = tf.mkAppRaw("str.len", List.of(s), Sort.INT);
                axioms.add(tf.mkOr(List.of(
                        tf.mkEq((Term) app, tf.mkInt(-1)),
                        tf.mkAnd(List.of(tf.mkGe((Term) app, tf.mkInt(0)), tf.mkLt((Term) app, lenS))))));
            }
        }
        if (Sort.equal(t.sort, Sort.STRING)) {
            Term lenT = tf.mkAppRaw("str.len", List.of(t), Sort.INT);
            axioms.add(tf.mkGe(lenT, tf.mkInt(0)));
        }
    }
}
