package com.z3x;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Random;

/** Heavy benchmarks designed to take 50-500ms each. Stresses theory work, not startup. */
public final class GenerateHeavyBench {

    public static void main(String[] args) throws Exception {
        Path out = Path.of(args.length >= 1 ? args[0] : "benchmarks/heavy");
        int count = args.length >= 2 ? Integer.parseInt(args[1]) : 20;
        Files.createDirectories(out);
        Random r = new Random(7);
        for (int i = 0; i < count; i++) {
            String body;
            String exp;
            int kind = i % 4;
            if (kind == 0) {
                int n = 100 + r.nextInt(200);
                body = bigLia(r, n, n * 4, true);
                exp = "sat";
            } else if (kind == 1) {
                int n = 80 + r.nextInt(150);
                body = bigLia(r, n, n * 5, false);
                exp = "unsat";
            } else if (kind == 2) {
                int n = 400 + r.nextInt(300);
                body = GenerateBench.chainEuf(n, i % 8 < 4);
                exp = (i % 8 < 4) ? "unsat" : "sat";
            } else {
                int n = 60 + r.nextInt(80);
                body = clauseSpaghetti(r, n, n * 2);
                exp = i % 2 == 0 ? "sat" : "unsat";
            }
            String content = "(set-info :status " + exp + ")\n" + body;
            Files.writeString(out.resolve(String.format("heavy_%03d.smt2", i)), content);
        }
        System.out.println("Generated " + count + " heavy files in " + out);
    }

    private static String bigLia(Random r, int n, int m, boolean wantSat) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_LIA)\n");
        for (int i = 0; i < n; i++) sb.append("(declare-const x").append(i).append(" Int)\n");
        for (int i = 0; i < n; i++) {
            sb.append("(assert (>= x").append(i).append(' ').append(-50 + r.nextInt(100)).append("))\n");
            sb.append("(assert (<= x").append(i).append(' ').append(50 + r.nextInt(100)).append("))\n");
        }
        for (int j = 0; j < m; j++) {
            sb.append("(assert (<= (+ ");
            int terms = 3 + r.nextInt(5);
            for (int t = 0; t < terms; t++) {
                int coef = 1 + r.nextInt(10);
                int v = r.nextInt(n);
                if (t > 0) sb.append(' ');
                if (coef == 1) sb.append("x").append(v);
                else sb.append("(* ").append(coef).append(" x").append(v).append(")");
            }
            sb.append(") ").append(20 + r.nextInt(200)).append("))\n");
        }
        if (!wantSat) {
            // Force contradiction.
            sb.append("(assert (>= (+ ");
            for (int i = 0; i < n; i++) {
                if (i > 0) sb.append(' ');
                sb.append("x").append(i);
            }
            sb.append(") ").append(n * 1000).append("))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String clauseSpaghetti(Random r, int n, int m) {
        // Many propositional clauses with random literals (SAT stress).
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_UF)\n");
        for (int i = 0; i < n; i++) sb.append("(declare-const p").append(i).append(" Bool)\n");
        for (int j = 0; j < m; j++) {
            sb.append("(assert (or");
            int terms = 3 + r.nextInt(3);
            for (int t = 0; t < terms; t++) {
                boolean neg = r.nextBoolean();
                int v = r.nextInt(n);
                sb.append(' ');
                if (neg) sb.append("(not p").append(v).append(")"); else sb.append("p").append(v);
            }
            sb.append("))\n");
        }
        sb.append("(check-sat)\n");
        return sb.toString();
    }
}
