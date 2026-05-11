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
                // x * x ≥ 0
                axioms.add(tf.mkGe(t, tf.mkInt(0)));
                // x * x = 0 ⇒ x = 0  (one direction; the other is trivial).
                Term xIsZero = tf.mkEq(a, tf.mkInt(0));
                Term sqIsZero = tf.mkEq(t, tf.mkInt(0));
                axioms.add(tf.mkImplies(sqIsZero, xIsZero));
                axioms.add(tf.mkImplies(xIsZero, sqIsZero));
            }
        }
    }
}
