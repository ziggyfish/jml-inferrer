package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class QuantifierTest extends TestHarness {

    public void testGroundForallTrueSat() {
        var v = new Solver().run("""
                (set-logic UFLIA)
                (declare-const a Int)
                (assert (forall ((x Int)) (=> (= x a) (>= x 0))))
                (assert (= a 5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testGroundForallFalseUnsat() {
        var v = new Solver().run("""
                (set-logic UFLIA)
                (declare-const a Int)
                (assert (forall ((x Int)) (=> (= x a) (>= x 0))))
                (assert (= a 5))
                (assert (< a 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testTrivialUnsatFromForall() {
        var v = new Solver().run("""
                (set-logic UFLIA)
                (declare-const a Int)
                (declare-const b Int)
                (assert (forall ((x Int)) (=> (= x a) (= x b))))
                (assert (= a 3))
                (assert (= b 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testExistentialSkolemiseSat() {
        var v = new Solver().run("""
                (set-logic UFLIA)
                (assert (exists ((x Int)) (= x 0)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testExistentialOverConstraintUnsat() {
        var v = new Solver().run("""
                (set-logic UFLIA)
                (assert (not (exists ((x Int)) (and (>= x 0) (<= x 0) (= x 5)))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testForallOverPredicate() {
        var v = new Solver().run("""
                (set-logic QF_UF)
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
}
