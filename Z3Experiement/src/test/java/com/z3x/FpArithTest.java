package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** IEEE-754 arithmetic on FP literals + symbolic axioms for variable operands. */
public class FpArithTest extends TestHarness {

    // ---------- fp.add ----------

    public void testFpAddTwoFiniteLiteralsRneFloat32() {
        // 1.0 + 2.0 = 3.0. In Float32 (eb=8, sb=24): 1.0 = 0x3F800000, 2.0 = 0x40000000, 3.0 = 0x40400000.
        // We assert (= (fp.add RNE 1.0 2.0) 3.0) and expect SAT.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.add RNE
                    (fp #b0 #b01111111 #b00000000000000000000000)
                    (fp #b0 #b10000000 #b00000000000000000000000))
                    (fp #b0 #b10000000 #b10000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpAddWrongResultUnsat() {
        // 1.0 + 1.0 = 2.0; assert it equals 3.0, expect UNSAT.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.add RNE
                    (fp #b0 #b01111111 #b00000000000000000000000)
                    (fp #b0 #b01111111 #b00000000000000000000000))
                    (fp #b0 #b10000000 #b10000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testFpAddInfPlusInfPositive() {
        // +inf + +inf = +inf
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isInfinite (fp.add RNE (_ +oo 8 24) (_ +oo 8 24))))
                (assert (fp.isPositive  (fp.add RNE (_ +oo 8 24) (_ +oo 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpAddInfPlusNegInfIsNan() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (fp.add RNE (_ +oo 8 24) (_ -oo 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.sub ----------

    public void testFpSubTwoLiterals() {
        // 3.0 - 1.0 = 2.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.sub RNE
                    (fp #b0 #b10000000 #b10000000000000000000000)
                    (fp #b0 #b01111111 #b00000000000000000000000))
                    (fp #b0 #b10000000 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpSubInfMinusInfIsNan() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (fp.sub RNE (_ +oo 8 24) (_ +oo 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.mul ----------

    public void testFpMulTwoLiterals() {
        // 2.0 * 3.0 = 6.0. 6.0 = 0x40C00000 = sign 0, exp 10000001 (=128, bias 127 → unbiased 1), sig 10000000000000000000000.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.mul RNE
                    (fp #b0 #b10000000 #b00000000000000000000000)
                    (fp #b0 #b10000000 #b10000000000000000000000))
                    (fp #b0 #b10000001 #b10000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpMulZeroTimesInfIsNan() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (fp.mul RNE (_ +zero 8 24) (_ +oo 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpMulInfTimesFiniteIsInf() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isInfinite (fp.mul RNE (_ +oo 8 24)
                    (fp #b0 #b10000000 #b00000000000000000000000))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.div ----------

    public void testFpDivTwoLiterals() {
        // 6.0 / 2.0 = 3.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.div RNE
                    (fp #b0 #b10000001 #b10000000000000000000000)
                    (fp #b0 #b10000000 #b00000000000000000000000))
                    (fp #b0 #b10000000 #b10000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpDivByZeroIsInf() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isInfinite (fp.div RNE
                    (fp #b0 #b01111111 #b00000000000000000000000)
                    (_ +zero 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpDivZeroByZeroIsNan() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (fp.div RNE (_ +zero 8 24) (_ +zero 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpDivInfByInfIsNan() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (fp.div RNE (_ +oo 8 24) (_ +oo 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.fma ----------

    public void testFpFmaThreeOperands() {
        // 2.0 * 3.0 + 1.0 = 7.0. 7.0 = 0x40E00000 = exp 10000001, sig 11000000000000000000000.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.fma RNE
                    (fp #b0 #b10000000 #b00000000000000000000000)
                    (fp #b0 #b10000000 #b10000000000000000000000)
                    (fp #b0 #b01111111 #b00000000000000000000000))
                    (fp #b0 #b10000001 #b11000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.sqrt ----------

    public void testFpSqrtFour() {
        // sqrt(4.0) = 2.0. 4.0 = exp 10000001, sig 0; 2.0 = exp 10000000, sig 0.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.sqrt RNE
                    (fp #b0 #b10000001 #b00000000000000000000000))
                    (fp #b0 #b10000000 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpSqrtNegativeIsNan() {
        // sqrt(-1.0) = NaN
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isNaN (fp.sqrt RNE
                    (fp #b1 #b01111111 #b00000000000000000000000))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpSqrtZero() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isZero (fp.sqrt RNE (_ +zero 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.abs / fp.neg ----------

    public void testFpAbsNegative() {
        // abs(-1.0) = 1.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.abs (fp #b1 #b01111111 #b00000000000000000000000))
                               (fp #b0 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpNegPositive() {
        // -(1.0) = -1.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.neg (fp #b0 #b01111111 #b00000000000000000000000))
                               (fp #b1 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpAbsZeroIsPositive() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.isPositive (fp.abs (_ -zero 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.min / fp.max ----------

    public void testFpMinPicksSmaller() {
        // min(1.0, 2.0) = 1.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.min
                    (fp #b0 #b01111111 #b00000000000000000000000)
                    (fp #b0 #b10000000 #b00000000000000000000000))
                    (fp #b0 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpMaxPicksLarger() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq (fp.max
                    (fp #b0 #b01111111 #b00000000000000000000000)
                    (fp #b0 #b10000000 #b00000000000000000000000))
                    (fp #b0 #b10000000 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- fp.lt / fp.leq / fp.gt / fp.geq ----------

    public void testFpLtTrue() {
        // 1.0 < 2.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.lt (fp #b0 #b01111111 #b00000000000000000000000)
                               (fp #b0 #b10000000 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpLeqEqual() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.leq (fp #b0 #b01111111 #b00000000000000000000000)
                                (fp #b0 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpGtFalseOnEq() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.gt (fp #b0 #b01111111 #b00000000000000000000000)
                               (fp #b0 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testFpLtNanIsFalse() {
        // (fp.lt NaN 1.0) should be false → UNSAT to assert it.
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.lt (_ NaN 8 24) (fp #b0 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    // ---------- conversions ----------

    public void testToFpFromInt() {
        // (_ to_fp 8 24) RNE 1 = 1.0
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (fp.eq ((_ to_fp 8 24) RNE 1)
                               (fp #b0 #b01111111 #b00000000000000000000000)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpToRealOfOne() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (= (fp.to_real (fp #b0 #b01111111 #b00000000000000000000000)) 1.0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    // ---------- symbolic identities ----------

    public void testFpAddZeroIdentitySymbolic() {
        // declare-const x : Float32, assert (fp.eq (fp.add RNE x +0) x)
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Float32)
                (assert (= (fp.add RNE x (_ +zero 8 24)) x))
                (check-sat)
                """);
        // The identity axiom forces the equality to hold; should be SAT.
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpMulOneIdentitySymbolic() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Float32)
                (assert (= (fp.mul RNE x (fp #b0 #b01111111 #b00000000000000000000000)) x))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpNegInvolutiveSymbolic() {
        // fp.neg(fp.neg(x)) = x
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Float32)
                (assert (= (fp.neg (fp.neg x)) x))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testFpAddNanPropagatesSymbolic() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Float32)
                (assert (fp.isNaN (fp.add RNE x (_ NaN 8 24))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
