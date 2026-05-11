package com.z3x;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Random;

/** Generate benchmarks using define-fun-rec for \sum / \product / \num_of patterns. */
public final class GenerateAggBench {

    public static void main(String[] args) throws Exception {
        Path out = Path.of(args.length >= 1 ? args[0] : "benchmarks/agg");
        int count = args.length >= 2 ? Integer.parseInt(args[1]) : 30;
        Files.createDirectories(out);
        Random r = new Random(11);
        for (int i = 0; i < count; i++) {
            int n = 3 + r.nextInt(10);
            String op = i % 3 == 0 ? "sum" : i % 3 == 1 ? "product" : "numof";
            String body;
            int expected;
            switch (op) {
                case "sum" -> {
                    int[] vals = new int[n];
                    int total = 0;
                    for (int k = 0; k < n; k++) { vals[k] = r.nextInt(20); total += vals[k]; }
                    boolean wantSat = i % 2 == 0;
                    body = makeSum(n, vals, wantSat ? total : total + 1);
                    expected = wantSat ? 0 : 1;
                }
                case "product" -> {
                    int[] vals = new int[Math.min(n, 5)]; // keep product bounded
                    int total = 1;
                    for (int k = 0; k < vals.length; k++) { vals[k] = 1 + r.nextInt(4); total *= vals[k]; }
                    boolean wantSat = i % 2 == 0;
                    body = makeProduct(vals.length, vals, wantSat ? total : total + 1);
                    expected = wantSat ? 0 : 1;
                }
                default -> {
                    int[] vals = new int[n];
                    int count2 = 0;
                    for (int k = 0; k < n; k++) {
                        vals[k] = r.nextInt(21) - 10;
                        if (vals[k] > 0) count2++;
                    }
                    boolean wantSat = i % 2 == 0;
                    body = makeNumOf(n, vals, wantSat ? count2 : count2 + 1);
                    expected = wantSat ? 0 : 1;
                }
            }
            String content = "(set-info :status " + (expected == 0 ? "sat" : "unsat") + ")\n" + body;
            Files.writeString(out.resolve(String.format("agg_%03d.smt2", i)), content);
        }
        System.out.println("Generated " + count + " aggregate files in " + out);
    }

    private static String makeSum(int n, int[] vals, int expectedSum) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic ALL)\n");
        sb.append("(declare-const arr (Array Int Int))\n");
        sb.append("(define-fun-rec jsum ((a (Array Int Int)) (lo Int) (hi Int)) Int\n");
        sb.append("  (ite (>= lo hi) 0 (+ (select a lo) (jsum a (+ lo 1) hi))))\n");
        for (int i = 0; i < n; i++) sb.append("(assert (= (select arr ").append(i).append(") ").append(vals[i]).append("))\n");
        sb.append("(assert (= (jsum arr 0 ").append(n).append(") ").append(expectedSum).append("))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String makeProduct(int n, int[] vals, int expectedProd) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic ALL)\n");
        sb.append("(declare-const arr (Array Int Int))\n");
        sb.append("(define-fun-rec jprod ((a (Array Int Int)) (lo Int) (hi Int)) Int\n");
        sb.append("  (ite (>= lo hi) 1 (* (select a lo) (jprod a (+ lo 1) hi))))\n");
        for (int i = 0; i < n; i++) sb.append("(assert (= (select arr ").append(i).append(") ").append(vals[i]).append("))\n");
        sb.append("(assert (= (jprod arr 0 ").append(n).append(") ").append(expectedProd).append("))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }

    private static String makeNumOf(int n, int[] vals, int expectedCount) {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic ALL)\n");
        sb.append("(declare-const arr (Array Int Int))\n");
        sb.append("(define-fun-rec jnum ((a (Array Int Int)) (lo Int) (hi Int)) Int\n");
        sb.append("  (ite (>= lo hi) 0 (+ (ite (> (select a lo) 0) 1 0) (jnum a (+ lo 1) hi))))\n");
        for (int i = 0; i < n; i++) sb.append("(assert (= (select arr ").append(i).append(") ").append(vals[i]).append("))\n");
        sb.append("(assert (= (jnum arr 0 ").append(n).append(") ").append(expectedCount).append("))\n");
        sb.append("(check-sat)\n");
        return sb.toString();
    }
}
