package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Extended string ops: str.at, str.substr, str.contains, str.prefixof, str.suffixof, str.indexof. */
public class StringExtTest extends TestHarness {

    public void testStrAtInBounds() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s String)
                (assert (= (str.len s) 5))
                (assert (= (str.len (str.at s 2)) 1))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testStrAtOutOfBoundsLengthZero() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s String)
                (assert (= (str.len s) 3))
                (assert (= (str.len (str.at s 10)) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testStrSubstrLength() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s String)
                (assert (= (str.len s) 10))
                (assert (= (str.len (str.substr s 2 3)) 3))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testStrContainsLengthBound() {
        // (str.contains s sub) ⇒ len(sub) ≤ len(s). With len(s)=3 and len(sub)=10, contains can't hold.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s String)
                (declare-const sub String)
                (assert (= (str.len s) 3))
                (assert (= (str.len sub) 10))
                (assert (str.contains s sub))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testStrPrefixofLengthBound() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const pre String)
                (declare-const s String)
                (assert (= (str.len pre) 7))
                (assert (= (str.len s) 3))
                (assert (str.prefixof pre s))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testStrSuffixofLengthBound() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const suf String)
                (declare-const s String)
                (assert (= (str.len suf) 8))
                (assert (= (str.len s) 3))
                (assert (str.suffixof suf s))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
