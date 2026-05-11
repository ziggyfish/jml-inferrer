package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Day-5 datatypes: constructors, selectors, testers, disjointness. */
public class DatatypeTest extends TestHarness {

    public void testPairSelectorSat() {
        var v = new Solver().run("""
                (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
                (declare-const p Pair)
                (assert (= p (mk-pair 3 5)))
                (assert (= (fst p) 3))
                (assert (= (snd p) 5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testPairSelectorUnsat() {
        var v = new Solver().run("""
                (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
                (declare-const p Pair)
                (assert (= p (mk-pair 3 5)))
                (assert (= (fst p) 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testConstructorDisjointness() {
        // Different ctors of the same datatype are unequal.
        var v = new Solver().run("""
                (declare-datatype Op ((Plus) (Minus) (Times)))
                (declare-const x Op)
                (declare-const y Op)
                (assert (= x Plus))
                (assert (= y Minus))
                (assert (= x y))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testTesterSat() {
        var v = new Solver().run("""
                (declare-datatype Op ((Plus) (Minus)))
                (declare-const x Op)
                (assert (= x Plus))
                (assert (is-Plus x))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testTesterUnsat() {
        var v = new Solver().run("""
                (declare-datatype Op ((Plus) (Minus)))
                (declare-const x Op)
                (assert (= x Plus))
                (assert (is-Minus x))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
