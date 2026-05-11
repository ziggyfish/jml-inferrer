package com.z3x;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Random;

/**
 * Generate a corpus of JML-shape benchmarks: ranged-∀ over arrays + linear bounds.
 * This is the formula shape OpenJML emits for typical method VCs, so it's a realistic
 * stress test for the JML verification workload.
 *
 * Usage: java -cp out com.z3x.GenerateBench <output-dir> <count>
 */
public final class GenerateBench {

    public static void main(String[] args) throws Exception {
        Path out = Path.of(args.length >= 1 ? args[0] : "benchmarks/jml_shape");
        int count = args.length >= 2 ? Integer.parseInt(args[1]) : 50;
        Files.createDirectories(out);
        Random r = new Random(0);
        int generated = 0;
        for (int i = 0; i < count; i++) {
            String body;
            String expected;
            switch (i % 4) {
                case 0 -> { body = arrayAllPositiveUnsat(r, i); expected = "unsat"; }
                case 1 -> { body = arrayAllPositiveSat(r, i); expected = "sat"; }
                case 2 -> { body = linearChain(r, i); expected = i % 8 < 4 ? "unsat" : "sat"; }
                default -> { body = boundedSumUnsat(r, i); expected = "unsat"; }
            }
            String content = "(set-info :status " + expected + ")\n" + body;
            Files.writeString(out.resolve(String.format("jml_%03d.smt2", i)), content);
            generated++;
        }
        System.out.println("Generated " + generated + " files in " + out);
    }

    private static String arrayAllPositiveUnsat(Random r, int seed) {
        int n = 5 + r.nextInt(15);
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_AUFLIA)\n");
        sb.append("(declare-const arr (Array Int Int))\n");
        for (int i = 0; i < n; i++) {
            sb.append("(assert (>= (select arr ").append(i).append(") 0))\n");
        }
        // Force one of them negative — contradiction.
        int violateIdx = r.nextInt(n);
        sb.append("(assert (< (select arr ").append(violateIdx).append(") 0))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String arrayAllPositiveSat(Random r, int seed) {
        int n = 5 + r.nextInt(15);
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_AUFLIA)\n");
        sb.append("(declare-const arr (Array Int Int))\n");
        for (int i = 0; i < n; i++) {
            sb.append("(assert (>= (select arr ").append(i).append(") 0))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String linearChain(Random r, int seed) {
        int n = 4 + r.nextInt(8);
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_LIA)\n");
        for (int i = 0; i < n; i++) sb.append("(declare-const x").append(i).append(" Int)\n");
        for (int i = 0; i < n - 1; i++) {
            sb.append("(assert (<= x").append(i).append(" x").append(i + 1).append("))\n");
        }
        if (seed % 8 < 4) {
            sb.append("(assert (< x").append(n - 1).append(" x0))\n");
        } else {
            sb.append("(assert (>= x").append(n - 1).append(" x0))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String boundedSumUnsat(Random r, int seed) {
        int n = 3 + r.nextInt(5);
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_LIA)\n");
        for (int i = 0; i < n; i++) sb.append("(declare-const x").append(i).append(" Int)\n");
        for (int i = 0; i < n; i++) sb.append("(assert (>= x").append(i).append(" 1))\n");
        sb.append("(assert (<= (+");
        for (int i = 0; i < n; i++) sb.append(" x").append(i);
        sb.append(") ").append(n - 1).append("))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    /** Larger linear systems — N variables, M random constraints. Stresses Simplex. */
    public static String largeLia(Random r, int n, int m, boolean wantSat) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_LIA)\n");
        for (int i = 0; i < n; i++) sb.append("(declare-const x").append(i).append(" Int)\n");
        // Bounds.
        for (int i = 0; i < n; i++) {
            sb.append("(assert (>= x").append(i).append(" 0))\n");
            sb.append("(assert (<= x").append(i).append(" 100))\n");
        }
        // Random linear constraints.
        for (int j = 0; j < m; j++) {
            sb.append("(assert (<= (+ ");
            int terms = 2 + r.nextInt(4);
            for (int t = 0; t < terms; t++) {
                int coef = 1 + r.nextInt(5);
                int v = r.nextInt(n);
                if (t > 0) sb.append(' ');
                sb.append("(* ").append(coef).append(" x").append(v).append(")");
            }
            sb.append(") ").append(20 + r.nextInt(80)).append("))\n");
        }
        if (!wantSat) {
            // Force a contradiction by demanding the sum exceed a bound that the constraints rule out.
            sb.append("(assert (>= (+ ");
            for (int i = 0; i < n; i++) {
                if (i > 0) sb.append(' ');
                sb.append("x").append(i);
            }
            sb.append(") ").append(n * 200).append("))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    /** Big EUF problem: chain of N equalities + a contradicting disequality.
     *  Stresses E-graph union-find depth. */
    public static String chainEuf(int n, boolean unsat) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_UF)\n");
        sb.append("(declare-sort U 0)\n");
        for (int i = 0; i <= n; i++) sb.append("(declare-const a").append(i).append(" U)\n");
        for (int i = 0; i < n; i++) {
            sb.append("(assert (= a").append(i).append(" a").append(i + 1).append("))\n");
        }
        if (unsat) sb.append("(assert (not (= a0 a").append(n).append(")))\n");
        else sb.append("(assert (= a0 a").append(n).append("))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }
}
