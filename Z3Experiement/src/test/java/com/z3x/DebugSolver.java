package com.z3x;

import com.z3x.solver.Solver;
import java.util.List;

/** Standalone runner for one specific failing case — useful for instrumenting. */
public class DebugSolver {
    public static void main(String[] args) {
        String src = """
                (set-logic UFLIA)
                (declare-fun p (Int Int) Bool)
                (declare-const a Int)
                (declare-const b Int)
                (assert (= a 1))
                (assert (= b 2))
                (assert (p 1 2))
                (assert (p a b))
                (assert (or (not (and (= b a) (= a b))) (p b a)))
                (check-sat)
                """;
        List<Solver.Verdict> v = new Solver().run(src);
        System.out.println("verdict: " + v);
    }
}
