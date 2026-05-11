package com.z3x;

import com.z3x.solver.Solver;
import java.util.List;

/** Standalone runner for one specific failing case — useful for instrumenting. */
public class DebugSolver {
    public static void main(String[] args) {
        String src = """
                (set-logic ALL)
                (declare-const arr (Array Int Int))
                (declare-const s Int)
                (declare-const i Int)
                (define-fun-rec jsum ((a (Array Int Int)) (lo Int) (hi Int)) Int
                  (ite (>= lo hi) 0 (+ (select a lo) (jsum a (+ lo 1) hi))))
                (assert (= (select arr 0) 10))
                (assert (= (select arr 1) 20))
                (assert (= (select arr 2) 30))
                (assert (= i 3))
                (assert (= s (jsum arr 0 i)))
                (assert (not (= s 60)))
                (check-sat)
                """;
        List<Solver.Verdict> v = new Solver().run(src);
        System.out.println("verdict: " + v);
    }
}
