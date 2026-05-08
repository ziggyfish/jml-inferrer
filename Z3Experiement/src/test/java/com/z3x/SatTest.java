package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

public class SatTest extends TestHarness {

    public void testTrivialOr() {
        var v = new Solver().run("""
                (declare-const p Bool)
                (declare-const q Bool)
                (assert (or p q))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testTrivialContradiction() {
        var v = new Solver().run("""
                (declare-const p Bool)
                (assert p)
                (assert (not p))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testModusPonens() {
        var v = new Solver().run("""
                (declare-const p Bool)
                (declare-const q Bool)
                (assert p)
                (assert (=> p q))
                (assert (not q))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testPigeonhole32() {
        var v = new Solver().run("""
                (declare-const p1h1 Bool) (declare-const p1h2 Bool)
                (declare-const p2h1 Bool) (declare-const p2h2 Bool)
                (declare-const p3h1 Bool) (declare-const p3h2 Bool)
                (assert (or p1h1 p1h2))
                (assert (or p2h1 p2h2))
                (assert (or p3h1 p3h2))
                (assert (not (and p1h1 p2h1)))
                (assert (not (and p1h1 p3h1)))
                (assert (not (and p2h1 p3h1)))
                (assert (not (and p1h2 p2h2)))
                (assert (not (and p1h2 p3h2)))
                (assert (not (and p2h2 p3h2)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testSimpleSatAssignment() {
        var v = new Solver().run("""
                (declare-const a Bool)
                (declare-const b Bool)
                (declare-const c Bool)
                (assert (or a b c))
                (assert (or (not a) (not b)))
                (assert (or (not b) (not c)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testNestedImplications() {
        var v = new Solver().run("""
                (declare-const p Bool)
                (declare-const q Bool)
                (declare-const r Bool)
                (assert (=> p q))
                (assert (=> q r))
                (assert p)
                (assert (not r))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testIte() {
        var v = new Solver().run("""
                (declare-const c Bool)
                (declare-const a Bool)
                (declare-const b Bool)
                (assert (ite c a b))
                (assert c)
                (assert (not a))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
