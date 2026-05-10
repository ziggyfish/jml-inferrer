package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Array extensionality (Day-3): distinct array names with identical contents are provably equal. */
public class ArrayExtTest extends TestHarness {

    public void testExtensionalEqualitySat() {
        // a and b agree on every index → SAT under extensional equality.
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const b (Array Int Int))
                (assert (= a b))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testExtensionalDisagreementUnsat() {
        // a = b but a[0] = 1 and b[0] = 2 → UNSAT.
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const b (Array Int Int))
                (assert (= a b))
                (assert (= (select a 0) 1))
                (assert (= (select b 0) 2))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testExtensionalDistinctSatWithWitness() {
        // a != b → exists some index where they differ. SAT when nothing pins them.
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const b (Array Int Int))
                (assert (not (= a b)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testExtensionalAgreementOnAllGroundsUnsat() {
        // (= a b) is at positive polarity → forall k. a[k] = b[k] gets instantiated over ground
        // ints. With select(a, 0)=1 and select(b, 0)=2 the instance at k=0 yields 1=2, UNSAT.
        // Already covered by testExtensionalDisagreementUnsat; this is the multi-index version.
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const b (Array Int Int))
                (assert (= a b))
                (assert (= (select a 0) 1))
                (assert (= (select b 0) 1))
                (assert (= (select a 1) 5))
                (assert (= (select b 1) 6))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
