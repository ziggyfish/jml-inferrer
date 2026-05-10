package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Tests for the Day-3 BV arithmetic extensions: bvmul, bvshl, bvlshr, bvashr. */
public class BvArithTest extends TestHarness {

    public void testBvMulSmallSat() {
        // 4-bit: 0011 * 0010 = 0110 (3 * 2 = 6)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvmul #b0011 #b0010) #b0110))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvMulOverflowTruncates() {
        // 4-bit: 0101 * 0101 = 25 = 0001 1001 → low 4 bits = 1001
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvmul #b0101 #b0101) #b1001))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvMulWrongUnsat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvmul #b0011 #b0010) #b0111))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testBvMulByZero() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (declare-const x (_ BitVec 4))
                (assert (= (bvmul x #b0000) #b0000))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvShlByOne() {
        // 0010 << 1 = 0100
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvshl #b0010 #b0001) #b0100))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvShlByThree() {
        // 0001 << 3 = 1000
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvshl #b0001 #b0011) #b1000))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvShlOverflow() {
        // 1000 << 1 = 0000 (top bit shifted off in 4-bit)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvshl #b1000 #b0001) #b0000))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvLshrByOne() {
        // 1000 lshr 1 = 0100
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvlshr #b1000 #b0001) #b0100))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvLshrFillsZero() {
        // High bits fill with 0 (logical): 1111 lshr 1 = 0111
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvlshr #b1111 #b0001) #b0111))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvAshrFillsSign() {
        // Arithmetic: 1111 ashr 1 = 1111 (sign extends)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvashr #b1111 #b0001) #b1111))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testBvAshrPositive() {
        // 0100 ashr 1 = 0010 (high bit 0, fills with 0)
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (bvashr #b0100 #b0001) #b0010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
