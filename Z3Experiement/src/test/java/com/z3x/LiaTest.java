package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class LiaTest extends TestHarness {

    public void testSimpleSat() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (<= x 5))
                (assert (>= y x))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testContradictoryBoundsUnsat() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (<= x 3))
                (assert (>= x 5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSimpleEquality() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= x 3))
                (assert (= y 4))
                (assert (<= (+ x y) 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSumExceedsBoundUnsat() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (>= x 5))
                (assert (>= y 5))
                (assert (<= (+ x y) 8))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testRealLowerBoundOnlySat() {
        var v = new Solver().run("""
                (set-logic QF_LRA)
                (declare-const x Real)
                (assert (>= x 0.0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testCoefficientUnsat() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (<= (+ (* 2 x) y) 4))
                (assert (>= x 3))
                (assert (>= y 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testTransitiveBoundsSat() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (declare-const z Int)
                (assert (<= x y))
                (assert (<= y z))
                (assert (<= z 10))
                (assert (>= x 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
