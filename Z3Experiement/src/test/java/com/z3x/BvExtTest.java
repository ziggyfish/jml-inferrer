package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Extended BV ops: extract, concat, zero_extend, sign_extend, rotate, repeat. */
public class BvExtTest extends TestHarness {

    public void testExtract() {
        // (_ extract 3 2) on 8-bit 0b00001100 → 0b11.
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ extract 3 2) #b00001100) #b11))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testExtractLowBits() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ extract 1 0) #b00001100) #b00))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testConcat() {
        // concat #b1010 #b0011 = #b10100011 (left arg = MSB).
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= (concat #b1010 #b0011) #b10100011))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testZeroExtend() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ zero_extend 4) #b1010) #b00001010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSignExtend() {
        // Negative sign extends with 1s.
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ sign_extend 4) #b1010) #b11111010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSignExtendPositive() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ sign_extend 4) #b0101) #b00000101))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRotateLeft() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ rotate_left 1) #b1010) #b0101))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRotateRight() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ rotate_right 1) #b1010) #b0101))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRepeat() {
        var v = new Solver().run("""
                (set-logic QF_BV)
                (assert (= ((_ repeat 3) #b10) #b101010))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
