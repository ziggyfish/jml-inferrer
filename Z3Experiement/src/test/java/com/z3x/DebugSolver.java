package com.z3x;

import com.z3x.solver.Solver;
import java.util.List;

/** Standalone runner for one specific failing case — useful for instrumenting. */
public class DebugSolver {
    public static void main(String[] args) {
        String src = """
                (set-logic ALL)
                (declare-const a String)
                (assert (< (str.len a) 0))
                (check-sat)
                """;
        List<Solver.Verdict> v = new Solver().run(src);
        System.out.println("verdict: " + v);
    }
}
