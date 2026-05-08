package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class ArrayTest extends TestHarness {

    public void testSelectStoreSameSat() {
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const i Int)
                (declare-const v Int)
                (assert (= (select (store a i v) i) v))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSelectStoreSameContradictionUnsat() {
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const i Int)
                (declare-const v Int)
                (assert (not (= (select (store a i v) i) v)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSelectStoreDifferentIndexSat() {
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const i Int)
                (declare-const j Int)
                (declare-const v Int)
                (assert (not (= i j)))
                (assert (= (select (store a i v) j) (select a j)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSelectStoreDifferentIndexContradictionUnsat() {
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const i Int)
                (declare-const j Int)
                (declare-const v Int)
                (assert (not (= i j)))
                (assert (not (= (select (store a i v) j) (select a j))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testNestedStoresUnsat() {
        var v = new Solver().run("""
                (set-logic QF_AUFLIA)
                (declare-const a (Array Int Int))
                (declare-const i Int)
                (declare-const j Int)
                (declare-const v Int)
                (declare-const w Int)
                (assert (= i j))
                (assert (not (= (select (store (store a i v) j w) i) w)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
