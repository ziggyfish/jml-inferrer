package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Tests targeting the JML-Inferrer spec-pattern shape: forall k in [lo, hi). P(arr[k]). */
public class SpecPatternTest extends TestHarness {

    public void testRangedForallAllPositive() {
        // forall k in [0, 4). arr[k] >= 0; arr[2] = -1 contradicts.
        var v = new Solver().run("""
                (set-logic AUFLIA)
                (declare-const arr (Array Int Int))
                (assert (forall ((k Int))
                  (=> (and (<= 0 k) (< k 4)) (>= (select arr k) 0))))
                (assert (= (select arr 2) (- 1)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testRangedForallPositiveSat() {
        var v = new Solver().run("""
                (set-logic AUFLIA)
                (declare-const arr (Array Int Int))
                (assert (forall ((k Int))
                  (=> (and (<= 0 k) (< k 4)) (>= (select arr k) 0))))
                (assert (= (select arr 0) 1))
                (assert (= (select arr 1) 2))
                (assert (= (select arr 2) 3))
                (assert (= (select arr 3) 4))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRangedForallSkipsOutOfRange() {
        // forall k in [0, 2). arr[k] = 0; arr[5] = 99 should not contradict.
        var v = new Solver().run("""
                (set-logic AUFLIA)
                (declare-const arr (Array Int Int))
                (assert (forall ((k Int))
                  (=> (and (<= 0 k) (< k 2)) (= (select arr k) 0))))
                (assert (= (select arr 5) 99))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRangedForallSymbolicBoundsSat() {
        var v = new Solver().run("""
                (set-logic AUFLIA)
                (declare-const arr (Array Int Int))
                (declare-const lo Int)
                (declare-const hi Int)
                (assert (= lo 0))
                (assert (= hi 3))
                (assert (forall ((k Int))
                  (=> (and (<= lo k) (< k hi)) (>= (select arr k) 0))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
