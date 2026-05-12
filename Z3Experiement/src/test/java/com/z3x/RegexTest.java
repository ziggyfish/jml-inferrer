package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Regex membership for literal strings via Brzozowski-style derivative evaluation. */
public class RegexTest extends TestHarness {

    public void testLiteralMatch() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "abc" (str.to_re "abc")))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testLiteralMismatch() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "xyz" (str.to_re "abc")))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testConcatenation() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "abcdef" (re.++ (str.to_re "abc") (str.to_re "def"))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testUnion() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "yes" (re.union (str.to_re "yes") (str.to_re "no"))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testStar() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "ababab" (re.* (str.to_re "ab"))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testStarMatchesEmpty() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "" (re.* (str.to_re "a"))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRangeChar() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "m" (re.range "a" "z")))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testRangeOutOfRange() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "0" (re.range "a" "z")))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testPlus() {
        // "aaa" matches re.+ "a" but not "" against re.+ "a".
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "aaa" (re.+ (str.to_re "a"))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testPlusEmptyFails() {
        var v = new Solver().run("""
                (set-logic ALL)
                (assert (str.in_re "" (re.+ (str.to_re "a"))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
