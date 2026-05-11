package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class UnsatCoreTest extends TestHarness {

    public void testUnsatCoreReturnsNamedAsserts() {
        Solver s = new Solver();
        var v = s.run("""
                (set-option :produce-unsat-cores true)
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (! (>= x 5) :named A))
                (assert (! (<= x 3) :named B))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
        List<String> core = s.lastUnsatCore();
        assertTrue(core.contains("A"));
        assertTrue(core.contains("B"));
    }

    public void testUnsatCoreNamedAssertionParses() {
        // Sanity: (! body :named X) is stripped and the body is asserted.
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (! (= x 5) :named eq5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
