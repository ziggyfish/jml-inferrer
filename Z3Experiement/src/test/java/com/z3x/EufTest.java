package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class EufTest extends TestHarness {

    public void testCongruenceUnsat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun f (U) U)
                (declare-const a U)
                (declare-const b U)
                (assert (= a b))
                (assert (not (= (f a) (f b))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testChainEqualityUnsat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-const a U)
                (declare-const b U)
                (declare-const c U)
                (assert (= a b))
                (assert (= b c))
                (assert (not (= a c)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testDistinctSat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-const a U)
                (declare-const b U)
                (assert (distinct a b))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testDeepCongruenceUnsat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun f (U U) U)
                (declare-const a U)
                (declare-const b U)
                (declare-const c U)
                (declare-const d U)
                (assert (= a b))
                (assert (= c d))
                (assert (not (= (f a c) (f b d))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testEquivalenceClassesSat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun f (U) U)
                (declare-const a U)
                (declare-const b U)
                (assert (= a b))
                (assert (= (f a) (f b)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testTransitivityWithFunction() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun f (U) U)
                (declare-const a U)
                (declare-const b U)
                (declare-const c U)
                (assert (= (f a) b))
                (assert (= b c))
                (assert (not (= (f a) c)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
