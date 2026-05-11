package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Day-5 strings: literals, str.len, str.++. */
public class StringTest extends TestHarness {

    public void testLengthOfLiteralSat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (= (str.len "hello") 5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testLengthOfLiteralUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (= (str.len "hello") 3))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testConcatLengthSat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const a String)
                (declare-const b String)
                (assert (= (str.len a) 3))
                (assert (= (str.len b) 4))
                (assert (= (str.len (str.++ a b)) 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testConcatLengthUnsat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const a String)
                (declare-const b String)
                (assert (= (str.len a) 3))
                (assert (= (str.len b) 4))
                (assert (= (str.len (str.++ a b)) 10))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testLengthNonNegative() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const a String)
                (assert (< (str.len a) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
