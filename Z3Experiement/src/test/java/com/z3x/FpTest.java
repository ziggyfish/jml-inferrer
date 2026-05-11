package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Minimal floating-point: parse + predicates on literals. */
public class FpTest extends TestHarness {

    public void testNaNIsNan() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (_ NaN 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testNaNIsNotZero() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isZero (_ NaN 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testPlusZeroIsZero() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isZero (_ +zero 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testMinusZeroIsNegative() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNegative (_ -zero 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testPlusInfIsInfinite() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isInfinite (_ +oo 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testNanFpEqIsFalse() {
        // IEEE-754: NaN != NaN.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (_ NaN 8 24) (_ NaN 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testPlusMinusZeroFpEq() {
        // IEEE-754: +0 == -0 under fp.eq.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (_ +zero 8 24) (_ -zero 8 24)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
