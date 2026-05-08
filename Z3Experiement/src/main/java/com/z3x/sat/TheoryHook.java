package com.z3x.sat;

import java.util.List;

/**
 * Bridge between SAT core and theory layer. The SAT solver calls these hooks at well-defined
 * points so theories can detect inconsistency and propagate implications.
 *
 * Conflict-clauses are returned as plain int[] (DIMACS-style literals). They are added as
 * learned clauses by the SAT core, which then backjumps using its standard analysis.
 */
public interface TheoryHook {

    /** Called when SAT assigns a literal that corresponds to a theory atom. */
    void assertLiteral(int lit);

    /** Called when SAT backtracks past the level that asserted a literal. */
    void retractLiteral(int lit);

    /**
     * Run a full theory consistency check at the current decision level. Return null if consistent,
     * or a conflict clause (subset of currently-asserted theory literals, negated) if not.
     */
    int[] check();

    /**
     * Optional T-propagation: theory may return literals it has determined must be true given the
     * current partial assignment. Returned literals are added to the SAT trail with reason = TPROP.
     * For each propagated literal, the theory must be able to produce an explanation later.
     */
    List<Integer> propagate();

    /** Provide an explanation clause justifying a previously T-propagated literal. */
    int[] explain(int propagatedLit);

    /** Hook so theory can register an atom variable v with the term it represents. */
    default void registerAtom(int var) {}

    /** A no-op hook used when running pure SAT (no theory layer). */
    TheoryHook NONE = new TheoryHook() {
        @Override public void assertLiteral(int lit) {}
        @Override public void retractLiteral(int lit) {}
        @Override public int[] check() { return null; }
        @Override public List<Integer> propagate() { return List.of(); }
        @Override public int[] explain(int propagatedLit) { return new int[] { propagatedLit }; }
    };
}
