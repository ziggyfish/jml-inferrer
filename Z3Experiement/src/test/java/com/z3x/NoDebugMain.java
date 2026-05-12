package com.z3x;

import com.z3x.solver.Solver;

/** Targeted debug runner for the testForcedDisagreementUnsat case. */
public class NoDebugMain {
    public static void main(String[] args) {
        Solver s = new Solver();
        var v = s.run("""
                (set-logic QF_NIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (= x 4))
                (assert (= y 5))
                (assert (not (= (* 2 (+ x y)) 18)))
                (check-sat)
                """);
        System.out.println("Result: " + v);
    }
}
