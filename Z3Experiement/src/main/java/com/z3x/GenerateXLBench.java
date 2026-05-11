package com.z3x;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Random;

/** Extra-large benchmarks where actual solving time dominates everything else. */
public final class GenerateXLBench {

    public static void main(String[] args) throws Exception {
        Path out = Path.of(args.length >= 1 ? args[0] : "benchmarks/xl");
        int count = args.length >= 2 ? Integer.parseInt(args[1]) : 10;
        Files.createDirectories(out);
        Random r = new Random(99);
        for (int i = 0; i < count; i++) {
            String body;
            String exp;
            if (i % 3 == 0) {
                int n = 500 + r.nextInt(500);
                body = denseLia(r, n, n * 6, true);
                exp = "sat";
            } else if (i % 3 == 1) {
                int n = 400 + r.nextInt(400);
                body = denseLia(r, n, n * 8, false);
                exp = "unsat";
            } else {
                int n = 1000 + r.nextInt(1000);
                body = bigEufChain(n);
                exp = "unsat";
            }
            String content = "(set-info :status " + exp + ")\n" + body;
            Files.writeString(out.resolve(String.format("xl_%03d.smt2", i)), content);
        }
        System.out.println("Generated " + count + " XL files in " + out);
    }

    private static String denseLia(Random r, int n, int m, boolean wantSat) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_LIA)\n");
        for (int i = 0; i < n; i++) sb.append("(declare-const x").append(i).append(" Int)\n");
        for (int i = 0; i < n; i++) {
            sb.append("(assert (>= x").append(i).append(' ').append(-1000 + r.nextInt(2000)).append("))\n");
            sb.append("(assert (<= x").append(i).append(' ').append(1000 + r.nextInt(2000)).append("))\n");
        }
        for (int j = 0; j < m; j++) {
            sb.append("(assert (<= (+ ");
            int terms = 5 + r.nextInt(10);
            for (int t = 0; t < terms; t++) {
                int coef = 1 + r.nextInt(20);
                int v = r.nextInt(n);
                if (t > 0) sb.append(' ');
                if (coef == 1) sb.append("x").append(v);
                else sb.append("(* ").append(coef).append(" x").append(v).append(")");
            }
            sb.append(") ").append(100 + r.nextInt(5000)).append("))\n");
        }
        if (!wantSat) {
            sb.append("(assert (>= (+ ");
            for (int i = 0; i < n; i++) {
                if (i > 0) sb.append(' ');
                sb.append("x").append(i);
            }
            sb.append(") ").append(n * 100000).append("))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String bigEufChain(int n) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_UF)\n");
        sb.append("(declare-sort U 0)\n");
        for (int i = 0; i <= n; i++) sb.append("(declare-const a").append(i).append(" U)\n");
        for (int i = 0; i < n; i++) {
            sb.append("(assert (= a").append(i).append(" a").append(i + 1).append("))\n");
        }
        sb.append("(assert (not (= a0 a").append(n).append(")))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }
}
