package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/**
 * Tests for JML's bounded aggregates encoded via define-fun-rec:
 *   \sum    — additive accumulator over [lo, hi)
 *   \product — multiplicative accumulator
 *   \num_of  — count of indices where a predicate holds
 *
 * The encoding matches what the patched OpenJML fork emits.
 */
public class AggregateTest extends TestHarness {

    public void testSumConstSat() {
        // jsum arr 0 3 = arr[0]+arr[1]+arr[2]. With each element = 1, sum = 3.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (define-fun-rec jsum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0 (+ (select a lo) (jsum a (+ lo 1) hi))))
                (assert (= (select arr 0) 1))
                (assert (= (select arr 1) 1))
                (assert (= (select arr 2) 1))
                (assert (= (jsum arr 0 3) 3))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSumConstUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (define-fun-rec jsum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0 (+ (select a lo) (jsum a (+ lo 1) hi))))
                (assert (= (select arr 0) 1))
                (assert (= (select arr 1) 1))
                (assert (= (select arr 2) 1))
                (assert (= (jsum arr 0 3) 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testProductConstSat() {
        // jprod arr 0 4 = arr[0]*arr[1]*arr[2]*arr[3]. With 2,3,5,7 → 210.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (define-fun-rec jprod ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 1 (* (select a lo) (jprod a (+ lo 1) hi))))
                (assert (= (select arr 0) 2))
                (assert (= (select arr 1) 3))
                (assert (= (select arr 2) 5))
                (assert (= (select arr 3) 7))
                (assert (= (jprod arr 0 4) 210))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testProductConstUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (define-fun-rec jprod ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 1 (* (select a lo) (jprod a (+ lo 1) hi))))
                (assert (= (select arr 0) 2))
                (assert (= (select arr 1) 3))
                (assert (= (select arr 2) 5))
                (assert (= (jprod arr 0 3) 31))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testNumOfConstSat() {
        // jnum counts indices in [lo, hi) where arr[i] > 0.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (define-fun-rec jnum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0
                       (+ (ite (> (select a lo) 0) 1 0)
                          (jnum a (+ lo 1) hi))))
                (assert (= (select arr 0) 5))
                (assert (= (select arr 1) -3))
                (assert (= (select arr 2) 7))
                (assert (= (select arr 3) 0))
                (assert (= (jnum arr 0 4) 2))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testNumOfConstUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (define-fun-rec jnum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0
                       (+ (ite (> (select a lo) 0) 1 0)
                          (jnum a (+ lo 1) hi))))
                (assert (= (select arr 0) 5))
                (assert (= (select arr 1) -3))
                (assert (= (select arr 2) 7))
                (assert (= (jnum arr 0 3) 3))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testNonRecursiveDefineFunSat() {
        // define-fun: simple substitution, must also unfold.
        var v = new Solver().run("""
                (set-logic ALL)
                (define-fun sq ((x Int)) Int (* x x))
                (declare-const y Int)
                (assert (= y 4))
                (assert (= (sq y) 16))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testNonRecursiveDefineFunUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (define-fun sq ((x Int)) Int (* x x))
                (declare-const y Int)
                (assert (= y 4))
                (assert (= (sq y) 15))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSumWithLoopInvariantPattern() {
        // The shape an inferred JML loop invariant would take:
        //   (\sum int k; 0 <= k < i; arr[k]) = s
        // Encoded as jsum arr 0 i = s. With i=3 and known arr values, check the invariant.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (declare-const s Int)
                (declare-const i Int)
                (define-fun-rec jsum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0 (+ (select a lo) (jsum a (+ lo 1) hi))))
                (assert (= (select arr 0) 10))
                (assert (= (select arr 1) 20))
                (assert (= (select arr 2) 30))
                (assert (= i 3))
                (assert (= s (jsum arr 0 i)))
                (assert (= s 60))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSumWithLoopInvariantPatternUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (declare-const s Int)
                (declare-const i Int)
                (define-fun-rec jsum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0 (+ (select a lo) (jsum a (+ lo 1) hi))))
                (assert (= (select arr 0) 10))
                (assert (= (select arr 1) 20))
                (assert (= (select arr 2) 30))
                (assert (= i 3))
                (assert (= s (jsum arr 0 i)))
                (assert (not (= s 60)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
