package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Minimal floating-point axiom layer. Resolves the predicates fp.isNaN, fp.isZero,
 * fp.isInfinite, fp.isPositive, fp.isNegative, fp.isNormal, fp.isSubnormal on FP literals
 * to true/false based on the literal's bit pattern. Variable FP terms are left opaque —
 * the solver will report unknown via "sat" if no constraint forces them.
 *
 * Full IEEE-754 arithmetic (fp.add, fp.mul, fp.div with rounding) is NOT implemented; those
 * stay as uninterpreted Apps. This covers the subset of FP-related JML asserts that
 * OpenJML's translation tends to emit — typically sign/zero/NaN checks on Java double/float.
 */
public final class FpAxioms {

    private final TermFactory tf;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seen = new HashSet<>();

    public FpAxioms(TermFactory tf) { this.tf = tf; }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) { walk(t); }

    private void walk(Term t) {
        if (!seen.add(t.id)) return;
        for (Term c : t.children()) walk(c);
        if (t instanceof Term.App app && app.args.size() == 1 && app.args.get(0) instanceof Term.FpConst lit) {
            Boolean known = predicateOn(app.symbol, lit);
            if (known != null) {
                axioms.add(tf.mkEq((Term) app, tf.mkBool(known)));
            }
        }
        // fp.eq on two literals.
        if (t instanceof Term.App app && app.symbol.equals("fp.eq") && app.args.size() == 2
                && app.args.get(0) instanceof Term.FpConst a && app.args.get(1) instanceof Term.FpConst b) {
            // NaN is never equal to anything (including itself) per IEEE-754.
            if (a.kind == Term.FpConst.Kind.NAN || b.kind == Term.FpConst.Kind.NAN) {
                axioms.add(tf.mkEq((Term) app, tf.mkBool(false)));
            } else if (a.kind == Term.FpConst.Kind.PLUS_ZERO || a.kind == Term.FpConst.Kind.MINUS_ZERO) {
                boolean bIsZero = b.kind == Term.FpConst.Kind.PLUS_ZERO || b.kind == Term.FpConst.Kind.MINUS_ZERO;
                axioms.add(tf.mkEq((Term) app, tf.mkBool(bIsZero)));
            } else if (b.kind == Term.FpConst.Kind.PLUS_ZERO || b.kind == Term.FpConst.Kind.MINUS_ZERO) {
                axioms.add(tf.mkEq((Term) app, tf.mkBool(false)));
            } else {
                // Same bit pattern, same value.
                boolean same = a.sign == b.sign && a.exp.equals(b.exp) && a.sig.equals(b.sig);
                axioms.add(tf.mkEq((Term) app, tf.mkBool(same)));
            }
        }
    }

    /** Evaluate predicate on a FP literal. Returns null if symbol isn't an FP predicate. */
    private Boolean predicateOn(String sym, Term.FpConst lit) {
        return switch (sym) {
            case "fp.isNaN"       -> lit.kind == Term.FpConst.Kind.NAN;
            case "fp.isInfinite"  -> lit.kind == Term.FpConst.Kind.PLUS_INF || lit.kind == Term.FpConst.Kind.MINUS_INF;
            case "fp.isZero"      -> lit.kind == Term.FpConst.Kind.PLUS_ZERO || lit.kind == Term.FpConst.Kind.MINUS_ZERO;
            case "fp.isPositive"  -> !lit.sign && lit.kind != Term.FpConst.Kind.NAN;
            case "fp.isNegative"  -> lit.sign && lit.kind != Term.FpConst.Kind.NAN;
            case "fp.isNormal"    -> lit.kind == Term.FpConst.Kind.NORMAL;
            case "fp.isSubnormal" -> lit.kind == Term.FpConst.Kind.NORMAL && lit.exp.signum() == 0;
            default -> null;
        };
    }
}
