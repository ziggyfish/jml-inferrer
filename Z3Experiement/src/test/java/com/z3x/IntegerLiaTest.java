package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Integer-specific LIA tests: cases where the rational solution exists but the integer one doesn't (or vice versa). */
public class IntegerLiaTest extends TestHarness {

    public void testTwoXEqualsOneUnsatInt() {
        // 2x = 1 → x = 0.5. UNSAT for Int, SAT for Real.
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= (* 2 x) 1))
                (assert (<= (* 2 x) 1))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testTwoXEqualsOneSatReal() {
        var v = new Solver().run("""
                (set-logic QF_LRA)
                (declare-const x Real)
                (assert (>= (* 2 x) 1))
                (assert (<= (* 2 x) 1))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testThreeXEqualsTwoUnsatInt() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= (* 3 x) 2))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testIntInRangeSat() {
        // x must be 5 — bounds force it.
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= x 5))
                (assert (<= x 5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testIntegerRangeSat() {
        // x is in [3, 7] — many integer solutions.
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= x 3))
                (assert (<= x 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
