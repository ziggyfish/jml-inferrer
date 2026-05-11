package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** push/pop is supported at the protocol level (re-solves each check-sat). */
public class PushPopTest extends TestHarness {

    public void testPushPopBasicSat() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= x 0))
                (push 1)
                (assert (<= x 5))
                (check-sat)
                (pop 1)
                (assert (<= x -1))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT, Solver.Verdict.UNSAT), v);
    }

    public void testNestedPush() {
        var v = new Solver().run("""
                (set-logic QF_LIA)
                (declare-const x Int)
                (push 1)
                (assert (>= x 10))
                (push 1)
                (assert (<= x 5))
                (check-sat)
                (pop 1)
                (assert (<= x 20))
                (check-sat)
                (pop 1)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT, Solver.Verdict.SAT), v);
    }
}
