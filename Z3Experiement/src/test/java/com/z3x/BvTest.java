package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class BvTest extends TestHarness {

    public void testBvLiteralEqualSat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= #b1010 #b1010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvLiteralUnequalUnsat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= #b1010 #b0101))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testBvAddSat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvadd #b0001 #b0001) #b0010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvAddOverflowSat() {
        // 4-bit BV: 0xF + 1 = 0x0
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvadd #b1111 #b0001) #b0000))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvAddWrongUnsat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvadd #b0001 #b0001) #b0011))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testBvAndOrXor() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvand #b1100 #b1010) #b1000))
                (assert (= (bvor  #b1100 #b1010) #b1110))
                (assert (= (bvxor #b1100 #b1010) #b0110))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvNotNeg() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvnot #b0011) #b1100))
                (assert (= (bvneg #b0001) #b1111))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvUltSat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (bvult #b0001 #b0010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvSltSignedSat() {
        // 4-bit signed: 1111 = -1, 0001 = +1, so -1 < 1 holds.
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (bvslt #b1111 #b0001))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvVarConstraint() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (declare-const x (_ BitVec 4))
                (assert (= (bvadd x #b0001) #b0011))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvVarContradictionUnsat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (declare-const x (_ BitVec 4))
                (assert (= x #b0010))
                (assert (= x #b0100))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
