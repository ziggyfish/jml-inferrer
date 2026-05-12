package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Proof emission and tighter unsat-core extraction (Day 11). */
public class ProofTest extends TestHarness {

    public void testProofEmittedOnUnsat() {
        Solver s = new Solver();
        s.run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (> x 5))
                (assert (< x 3))
                (check-sat)
                """);
        String proof = s.lastProof();
        assertTrue(proof.startsWith("(proof"), "proof string should start with '(proof'");
        assertTrue(proof.contains("conflicts"), "proof should include conflict count");
    }

    public void testProofEmptyOnSat() {
        Solver s = new Solver();
        s.run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= x 0))
                (check-sat)
                """);
        assertEquals("", s.lastProof());
    }

    public void testTightUnsatCoreExcludesIrrelevant() {
        // Two unrelated assertions force UNSAT. A third unrelated assertion should NOT appear in the core.
        Solver s = new Solver();
        s.run("""
                (set-option :produce-unsat-cores true)
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (declare-const z Int)
                (assert (! (> x 10) :named c1))
                (assert (! (< x 5)  :named c2))
                (assert (! (= z 99) :named irrelevant))
                (check-sat)
                """);
        List<String> core = s.lastUnsatCore();
        assertTrue(core.contains("c1"), "core should contain c1");
        assertTrue(core.contains("c2"), "core should contain c2");
        assertFalse(core.contains("irrelevant"));
    }
}
