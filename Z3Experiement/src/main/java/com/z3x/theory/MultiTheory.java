package com.z3x.theory;

import com.z3x.sat.TheoryHook;

import java.util.ArrayList;
import java.util.List;

/**
 * Combine multiple theories. Each {@code assertLiteral} is fanned out to every sub-theory; each
 * {@code retractLiteral} likewise. {@code check} returns the first non-null conflict; {@code propagate}
 * concatenates implied literals; {@code explain} delegates to the theory that owns the literal.
 *
 * Nelson-Oppen combination requires propagating implied equalities of shared variables across
 * theories. We implement the lightweight version: each sub-theory's {@code propagate} may include
 * equality literals it has discovered, and the SAT layer (which sees them as ordinary literals)
 * will enqueue them so the OTHER theory will see them via {@code assertLiteral}. Convergence is
 * guaranteed because the SAT/theory loop iterates until no theory has new propagations and no
 * theory has a conflict.
 */
public final class MultiTheory implements TheoryHook {

    private final List<TheoryHook> theories;

    public MultiTheory(List<TheoryHook> theories) {
        this.theories = List.copyOf(theories);
    }

    public List<TheoryHook> theories() { return theories; }

    @Override public void registerAtom(int var) {
        for (TheoryHook t : theories) t.registerAtom(var);
    }

    @Override public void assertLiteral(int lit) {
        for (TheoryHook t : theories) t.assertLiteral(lit);
    }

    @Override public void retractLiteral(int lit) {
        for (TheoryHook t : theories) t.retractLiteral(lit);
    }

    @Override public int[] check() {
        for (TheoryHook t : theories) {
            int[] c = t.check();
            if (c != null) return c;
        }
        return null;
    }

    @Override public List<Integer> propagate() {
        List<Integer> out = new ArrayList<>();
        for (TheoryHook t : theories) out.addAll(t.propagate());
        return out;
    }

    @Override public int[] explain(int propagatedLit) {
        // Best-effort: ask each theory; first one with a non-trivial answer wins.
        for (TheoryHook t : theories) {
            int[] e = t.explain(propagatedLit);
            if (e != null && e.length > 0) return e;
        }
        return new int[] { propagatedLit };
    }
}
