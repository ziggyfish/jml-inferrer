package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** NLA sign + interval propagation. */
public class NlaIntervalTest extends TestHarness {

    public void testProductOfNonNegIsNonNeg() {
        // x ≥ 0 ∧ y ≥ 0 ⇒ x*y ≥ 0. Asserting x*y < 0 should be unsat.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (declare-const y Int)
                (assert (>= x 0))
                (assert (>= y 0))
                (assert (< (* x y) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testProductOfNegativesIsNonNeg() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (declare-const y Int)
                (assert (<= x 0))
                (assert (<= y 0))
                (assert (< (* x y) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testProductOfMixedSignIsNonPos() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (declare-const y Int)
                (assert (>= x 0))
                (assert (<= y 0))
                (assert (> (* x y) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testMulByOne() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= x 1))
                (assert (= y 7))
                (assert (not (= (* x y) 7)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testMulByZero() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= x 0))
                (assert (not (= (* x y) 0)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
