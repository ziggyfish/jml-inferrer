package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Day-5 best-effort NLA — x*x >= 0 and friends. */
public class NlaTest extends TestHarness {

    public void testSquareNonNegativeSat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (assert (>= (* x x) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSquareNegativeUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (assert (< (* x x) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSquareZeroImpliesZeroUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (assert (= (* x x) 0))
                (assert (not (= x 0)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testZeroImpliesSquareZeroUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (assert (= x 0))
                (assert (not (= (* x x) 0)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
