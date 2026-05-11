package com.z3x;

import com.z3x.solver.Solver;
import com.z3x.term.Term;

import java.util.List;
import java.util.Map;

public class ModelTest extends TestHarness {

    public void testIntModelSat() {
        Solver s = new Solver();
        var v = s.run("""
                (set-option :produce-models true)
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= x 5))
                (assert (= y (+ x 3)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
        Map<String, Term> model = s.lastModel();
        assertTrue(model.containsKey("x"), "model should contain x");
        assertTrue(model.containsKey("y"), "model should contain y");
        assertEquals("5", model.get("x").toString());
        assertEquals("8", model.get("y").toString());
    }

    public void testBoolModelSat() {
        Solver s = new Solver();
        var v = s.run("""
                (set-option :produce-models true)
                (declare-const p Bool)
                (declare-const q Bool)
                (assert p)
                (assert (not q))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
        Map<String, Term> model = s.lastModel();
        assertEquals("true", model.get("p").toString());
        assertEquals("false", model.get("q").toString());
    }
}
