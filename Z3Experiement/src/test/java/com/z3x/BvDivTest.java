package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Day-4 BV division: bvudiv, bvurem, bvsdiv, bvsrem, bvsmod. */
public class BvDivTest extends TestHarness {

    public void testBvUdivSimple() {
        // 4-bit: 0110 / 0010 = 0011 (6 / 2 = 3)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvudiv #b0110 #b0010) #b0011))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvUdivWrongUnsat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvudiv #b0110 #b0010) #b0010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testBvUdivByZero() {
        // SMT-LIB: bvudiv x 0 = all-ones
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvudiv #b0011 #b0000) #b1111))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvUremSimple() {
        // 4-bit: 0111 % 0010 = 0001 (7 % 2 = 1)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvurem #b0111 #b0010) #b0001))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvUremByZero() {
        // SMT-LIB: bvurem x 0 = x
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvurem #b0101 #b0000) #b0101))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvSdivPositive() {
        // 4-bit signed: 0110 / 0010 = 0011 (+6 / +2 = +3)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvsdiv #b0110 #b0010) #b0011))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvSdivNegativeDividend() {
        // 4-bit: 1010 (-6) / 0010 (+2) = 1101 (-3)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvsdiv #b1010 #b0010) #b1101))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvSremPositive() {
        // 7 % 2 = 1 (signed)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvsrem #b0111 #b0010) #b0001))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvSremFollowsDividendSign() {
        // (-7) srem (+2) = -1 (sign of dividend) = 1111
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvsrem #b1001 #b0010) #b1111))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvSmodFollowsDivisorSign() {
        // (-7) smod (+2) = +1 (sign of divisor)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvsmod #b1001 #b0010) #b0001))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
