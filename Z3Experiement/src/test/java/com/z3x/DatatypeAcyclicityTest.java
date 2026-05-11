package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Acyclicity for recursive datatypes. */
public class DatatypeAcyclicityTest extends TestHarness {

    public void testListAcyclicity1Step() {
        // Cons(h, t) = t is impossible. Asserting it should be UNSAT.
        var v = new Solver().run("""
                (declare-datatype List ((nil) (cons (head Int) (tail List))))
                (declare-const x List)
                (declare-const h Int)
                (assert (= x (cons h x)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testListSelfReferenceFine() {
        // Without the cycle assertion: SAT.
        var v = new Solver().run("""
                (declare-datatype List ((nil) (cons (head Int) (tail List))))
                (declare-const x List)
                (assert (= x nil))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }
}
