package com.z3x;

/**
 * Smoke test for the Portfolio runner. The external z3 binary is assumed unavailable in CI;
 * we set z3Bin to a non-existent path so the only winner can be the in-process Z3Experiement.
 */
public class PortfolioTest extends TestHarness {

    public void testPortfolioWithoutZ3Falls() {
        String src = """
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= x 0))
                (assert (<= x 0))
                (check-sat)
                """;
        Portfolio.Result r = Portfolio.race(src, "definitely-not-z3-binary-xyzzy", 5_000);
        assertEquals("sat", r.verdict());
        assertEquals("z3experiement", r.winner());
    }

    public void testPortfolioUnsat() {
        String src = """
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (>= x 1))
                (assert (<= x 0))
                (check-sat)
                """;
        Portfolio.Result r = Portfolio.race(src, "definitely-not-z3-binary-xyzzy", 5_000);
        assertEquals("unsat", r.verdict());
    }
}
