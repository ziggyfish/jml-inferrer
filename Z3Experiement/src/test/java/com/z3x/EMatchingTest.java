package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Tests for trigger-based E-matching (Day-5). */
public class EMatchingTest extends TestHarness {

    public void testTriggerSingleVarUnsat() {
        // (forall ((x U)) (p x)) with (not (p a)) → trigger p(x), match against ground p(a) ... wait,
        // we don't have ground p(a). Need: assert (not (p a)) which creates ground p(a).
        var v = new Solver().run("""
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun p (U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((x U)) (p x)))
                (assert (not (p a)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testTriggerSingleVarSat() {
        var v = new Solver().run("""
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun p (U) Bool)
                (declare-const a U)
                (assert (forall ((x U)) (p x)))
                (assert (p a))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testTriggerMultiVarUnsat() {
        // (forall ((x U) (y U)) (q x y)) → trigger q(x, y). Match against q(a, b).
        var v = new Solver().run("""
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun q (U U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((x U) (y U)) (q x y)))
                (assert (not (q a b)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testTriggerNestedAppUnsat() {
        // (forall ((x U)) (p (f x))) — trigger p(f(x)). Match against ground p(f(a)).
        var v = new Solver().run("""
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun f (U) U)
                (declare-fun p (U) Bool)
                (declare-const a U)
                (assert (forall ((x U)) (p (f x))))
                (assert (not (p (f a))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
