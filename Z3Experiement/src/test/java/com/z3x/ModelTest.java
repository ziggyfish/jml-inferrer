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

    public void testArrayModelSat() {
        Solver s = new Solver();
        var v = s.run("""
                (set-option :produce-models true)
                (set-logic AUFLIA)
                (declare-const a (Array Int Int))
                (assert (= (select a 0) 7))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
        Map<String, Term> model = s.lastModel();
        assertTrue(model.containsKey("a"), "model should contain a");
    }

    public void testDatatypeModelSat() {
        Solver s = new Solver();
        var v = s.run("""
                (set-option :produce-models true)
                (set-logic ALL)
                (declare-datatype Color ((Red) (Green) (Blue)))
                (declare-const c Color)
                (assert (= c Red))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
        Map<String, Term> model = s.lastModel();
        assertTrue(model.containsKey("c"), "model should contain c");
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
