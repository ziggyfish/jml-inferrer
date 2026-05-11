package com.z3x.theory;

import com.z3x.sat.TheoryHook;
import com.z3x.solver.Cnf;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Theory of Equality with Uninterpreted Functions, plugged into the SAT layer via {@link TheoryHook}.
 *
 * Each theory atom that the SAT layer knows about is one of:
 *   - (= s t) for arbitrary terms,
 *   - or any uninterpreted Boolean predicate p(args) — represented by introducing a fresh
 *     equality (= p(args) true_term) at registration.
 *
 * On each {@code assertLiteral(lit)} the theory pushes a new EGraph level and applies the literal:
 *   - positive (= s t) → assertEq
 *   - negative (= s t) → assertDiseq
 *   - positive predicate p(args) → assertEq(p(args), true)
 *   - negative predicate → assertDiseq(p(args), true)
 *
 * On {@code retractLiteral(lit)} the theory pops one level.
 */
public final class EufTheory implements TheoryHook {

    private final TermFactory tf;
    private final Cnf cnf;
    private final EGraph eg;

    /** A canonical "true" / "false" term used for predicate atoms. */
    private final Term trueT, falseT;

    /** Map var -> the term it represents (cached from CNF). */
    private final Map<Integer, Term> varToTerm = new HashMap<>();

    /** Stack of (var, polarity) pairs that we asserted, so we can rebuild reasons. */
    private final List<Integer> assertedStack = new ArrayList<>();

    public EufTheory(TermFactory tf, Cnf cnf) {
        this.tf = tf;
        this.cnf = cnf;
        this.eg = new EGraph(tf);
        this.trueT = tf.mkBool(true);
        this.falseT = tf.mkBool(false);
        // Force trueT and falseT to be distinct in the E-graph by registering and asserting diseq.
        eg.registerTerm(trueT);
        eg.registerTerm(falseT);
        eg.assertDiseq(trueT, falseT, 0);
    }

    @Override
    public void registerAtom(int var) {
        Term t = cnf.termForVar(var);
        if (t == null) return;
        varToTerm.put(var, t);
        if (t instanceof Term.App app && app.symbol.equals("=")) {
            eg.registerTerm(app.args.get(0));
            eg.registerTerm(app.args.get(1));
        } else {
            // Treat as predicate p(args) — register and link to true/false.
            eg.registerTerm(t);
        }
    }

    @Override
    public void assertLiteral(int lit) {
        int var = Math.abs(lit);
        boolean pos = lit > 0;
        Term t = varToTerm.get(var);
        if (t == null) return;
        eg.pushLevel();
        assertedStack.add(lit);
        if (t instanceof Term.App app && app.symbol.equals("=")) {
            if (pos) eg.assertEq(app.args.get(0), app.args.get(1), lit);
            else eg.assertDiseq(app.args.get(0), app.args.get(1), lit);
        } else {
            // predicate
            if (pos) eg.assertEq(t, trueT, lit);
            else eg.assertEq(t, falseT, lit);
        }
    }

    @Override
    public void retractLiteral(int lit) {
        eg.popLevel();
        if (!assertedStack.isEmpty()) assertedStack.remove(assertedStack.size() - 1);
    }

    @Override
    public int[] check() {
        int[] c = eg.lastConflict;
        eg.lastConflict = null;
        return c;
    }

    @Override
    public List<Integer> propagate() {
        // Lightweight T-prop: for any registered atom var whose underlying equality is now decided
        // by the E-graph but not yet assigned in SAT, propagate it.
        List<Integer> out = new ArrayList<>();
        for (Map.Entry<Integer, Term> e : varToTerm.entrySet()) {
            int v = e.getKey();
            Term t = e.getValue();
            if (t instanceof Term.App app && app.symbol.equals("=")) {
                if (eg.areEqual(app.args.get(0), app.args.get(1))) {
                    out.add(v);
                }
            }
        }
        return out;
    }

    /** Return a canonical representative for the equivalence class of {@code t}. */
    public Term canonicalOf(Term t) {
        try {
            int rep = eg.repOfTerm(t);
            // Walk back to find a Var or constant if available, else the term itself.
            // (EGraph doesn't expose class members directly; just return the rep's term.)
            return eg.termOfRep(rep);
        } catch (Exception e) {
            return t;
        }
    }

    @Override
    public int[] explain(int propagatedLit) {
        int var = Math.abs(propagatedLit);
        Term t = varToTerm.get(var);
        if (t instanceof Term.App app && app.symbol.equals("=")) {
            // Minimal cut: ask the E-graph for the proof-forest reasons that imply a == b.
            int[] reasons = eg.explainEqTerms(app.args.get(0), app.args.get(1));
            // Clause form: (¬r1 ∨ ¬r2 ∨ ... ∨ propagatedLit) so that asserting all reasons forces the propagation.
            int[] out = new int[reasons.length + 1];
            for (int i = 0; i < reasons.length; i++) out[i] = -reasons[i];
            out[out.length - 1] = propagatedLit;
            return out;
        }
        // Predicate atom: fall back to asserted stack (sound but coarse).
        int[] r = new int[assertedStack.size() + 1];
        for (int i = 0; i < assertedStack.size(); i++) r[i] = -assertedStack.get(i);
        r[r.length - 1] = propagatedLit;
        return r;
    }
}
