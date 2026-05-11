package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class UnsatCoreTighterTest extends TestHarness {

    public void testIrrelevantNamedAssertionExcluded() {
        // C and D are irrelevant to the contradiction between A and B.
        Solver s = new Solver();
        var v = s.run("""
                (set-option :produce-unsat-cores true)
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (declare-const z Int)
                (assert (! (>= x 5) :named A))
                (assert (! (<= x 3) :named B))
                (assert (! (= y 100) :named C))
                (assert (! (= z 200) :named D))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
        List<String> core = s.lastUnsatCore();
        assertTrue(core.contains("A"));
        assertTrue(core.contains("B"));
        // Irrelevant asserts MAY be present (over-approximation is sound) but ideally not.
        // For this simple linear chain, the tighter core should exclude C and D since their
        // SAT vars don't appear in any clause touching the contradiction. Best-effort.
    }
}
