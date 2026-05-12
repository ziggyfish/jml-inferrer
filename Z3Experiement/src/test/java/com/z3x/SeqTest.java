package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** SMT-LIB Sequences theory: length, concatenation, contains, etc. */
public class SeqTest extends TestHarness {

    public void testSeqLenNonNegative() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s (Seq Int))
                (assert (< (seq.len s) 0))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSeqConcatLengthAdds() {
        // |a|=3, |b|=5; ensure |a++b| >= 8 holds (concat length axiom).
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const a (Seq Int))
                (declare-const b (Seq Int))
                (assert (= (seq.len a) 3))
                (assert (= (seq.len b) 5))
                (assert (< (seq.len (seq.++ a b)) 8))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSeqUnitLengthOne() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const x Int)
                (assert (not (= (seq.len (seq.unit x)) 1)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSeqContainsLengthBoundUnsat() {
        // If b contains a, then |a| <= |b|. Asserting otherwise should be UNSAT.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const a (Seq Int))
                (declare-const b (Seq Int))
                (assert (seq.contains b a))
                (assert (= (seq.len a) 10))
                (assert (= (seq.len b) 5))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSeqContainsSat() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const a (Seq Int))
                (declare-const b (Seq Int))
                (assert (seq.contains b a))
                (assert (= (seq.len a) 3))
                (assert (= (seq.len b) 10))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSeqAtInBoundsLengthOne() {
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s (Seq Int))
                (assert (= (seq.len s) 5))
                (assert (= (seq.len (seq.at s 2)) 1))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testSeqAtOutOfBoundsLengthZero() {
        // index 7 out-of-bounds in length-5 seq: seq.at returns empty (length 0). Asserting
        // length >= 1 must therefore be UNSAT.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s (Seq Int))
                (assert (= (seq.len s) 5))
                (assert (>= (seq.len (seq.at s 7)) 1))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSeqIndexofBound() {
        // indexof returns -1 or in [0, len(s)). Assert it's >= len(s) and not -1 → UNSAT.
        var v = new Solver().run("""
                (set-logic ALL)
                (declare-const s (Seq Int))
                (declare-const sub (Seq Int))
                (assert (= (seq.len s) 4))
                (assert (>= (seq.indexof s sub 0) 4))
                (assert (not (= (seq.indexof s sub 0) (- 1))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
