package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Day 12 NLA upgrades: distributivity over sums when a constant factor is present. */
public class NlaDistributeTest extends TestHarness {

    public void testDistributeConstantOverSum() {
        // 3 * (x + y) = 3x + 3y. Asserting otherwise is UNSAT.
        var v = new Solver().run("""
                (set-logic QF_NIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (not (= (* 3 (+ x y)) (+ (* 3 x) (* 3 y)))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testDistributeConstantWithKnownValues() {
        var v = new Solver().run("""
                (set-logic QF_NIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= x 4))
                (assert (= y 5))
                (assert (not (= (* 2 (+ x y)) 18)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testDistributeReverseOrder() {
        // (x + y) * 3 = 3x + 3y.
        var v = new Solver().run("""
                (set-logic QF_NIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (not (= (* (+ x y) 3) (+ (* 3 x) (* 3 y)))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
