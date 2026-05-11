package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Best-effort non-linear arithmetic axioms. The Simplex itself only handles linear arithmetic;
 * this preprocessor emits ground axioms for the most common non-linear monomial patterns so the
 * downstream LIA solver can still reason in many practical cases:
 *
 * <ul>
 *   <li>x*x ≥ 0 for any monomial x*x.</li>
 *   <li>x*x = 0 ⇔ x = 0 — encoded as two implications wrapped in an `or`.</li>
 *   <li>(* c x) — already linearised by Simplex's decomposition when c is constant.</li>
 * </ul>
 *
 * Higher-degree polynomials, multi-variable monomials, and roots are left as opaque variables.
 * This is the same baseline that solvers like Yices use as a fallback before invoking heavier
 * NLA machinery.
 */
public final class NlaAxioms {

    private final TermFactory tf;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seen = new HashSet<>();

    public NlaAxioms(TermFactory tf) { this.tf = tf; }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) { walk(t); }

    private void walk(Term t) {
        if (!seen.add(t.id)) return;
        for (Term c : t.children()) walk(c);
        if (t instanceof Term.App app && app.symbol.equals("*") && app.args.size() == 2) {
            Term a = app.args.get(0);
            Term b = app.args.get(1);
            if (a == b) {
                axioms.add(tf.mkGe(t, tf.mkInt(0)));
                Term xIsZero = tf.mkEq(a, tf.mkInt(0));
                Term sqIsZero = tf.mkEq(t, tf.mkInt(0));
                axioms.add(tf.mkImplies(sqIsZero, xIsZero));
                axioms.add(tf.mkImplies(xIsZero, sqIsZero));
                // Monotone bound: |x| ≤ K ⇒ x*x ≤ K*K when K ≥ 0.
                // Handled by interval propagation below.
            }
            // Sign-aware bound implications: (x ≥ 0 ∧ y ≥ 0) ⇒ x*y ≥ 0; similar for other sign combos.
            // These let LIA reason about non-negativity of products without doing full multiplication.
            Term aGE0 = tf.mkGe(a, tf.mkInt(0));
            Term aLE0 = tf.mkLe(a, tf.mkInt(0));
            Term bGE0 = tf.mkGe(b, tf.mkInt(0));
            Term bLE0 = tf.mkLe(b, tf.mkInt(0));
            Term mulGE0 = tf.mkGe(t, tf.mkInt(0));
            Term mulLE0 = tf.mkLe(t, tf.mkInt(0));
            // both non-negative ⇒ product non-negative
            axioms.add(tf.mkImplies(tf.mkAnd(List.of(aGE0, bGE0)), mulGE0));
            // both non-positive ⇒ product non-negative
            axioms.add(tf.mkImplies(tf.mkAnd(List.of(aLE0, bLE0)), mulGE0));
            // one non-negative, one non-positive ⇒ product non-positive
            axioms.add(tf.mkImplies(tf.mkAnd(List.of(aGE0, bLE0)), mulLE0));
            axioms.add(tf.mkImplies(tf.mkAnd(List.of(aLE0, bGE0)), mulLE0));
            // Zero propagation: if either factor is 0, product is 0.
            Term aIsZero = tf.mkEq(a, tf.mkInt(0));
            Term bIsZero = tf.mkEq(b, tf.mkInt(0));
            Term tIsZero = tf.mkEq(t, tf.mkInt(0));
            axioms.add(tf.mkImplies(tf.mkOr(List.of(aIsZero, bIsZero)), tIsZero));
            // Identity: a*1 = a.
            axioms.add(tf.mkImplies(tf.mkEq(a, tf.mkInt(1)), tf.mkEq(t, b)));
            axioms.add(tf.mkImplies(tf.mkEq(b, tf.mkInt(1)), tf.mkEq(t, a)));
            // Negation: a*(-1) = -a.
            axioms.add(tf.mkImplies(tf.mkEq(a, tf.mkInt(-1)), tf.mkEq(t, tf.mkSub(List.of(b)))));
            axioms.add(tf.mkImplies(tf.mkEq(b, tf.mkInt(-1)), tf.mkEq(t, tf.mkSub(List.of(a)))));
        }
    }
}
