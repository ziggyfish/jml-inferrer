package com.z3x;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Random;

/** Harder benchmarks: large linear systems and deep equality chains. */
public final class GenerateHardBench {

    public static void main(String[] args) throws Exception {
        Path out = Path.of(args.length >= 1 ? args[0] : "benchmarks/hard");
        int count = args.length >= 2 ? Integer.parseInt(args[1]) : 30;
        Files.createDirectories(out);
        Random r = new Random(42);
        for (int i = 0; i < count; i++) {
            String body;
            String exp;
            if (i % 3 == 0) {
                int n = 30 + r.nextInt(40);
                body = GenerateBench.largeLia(r, n, n * 2, true);
                exp = "sat";
            } else if (i % 3 == 1) {
                int n = 20 + r.nextInt(30);
                body = GenerateBench.largeLia(r, n, n * 3, false);
                exp = "unsat";
            } else {
                int n = 50 + r.nextInt(100);
                body = GenerateBench.chainEuf(n, i % 6 < 3);
                exp = (i % 6 < 3) ? "unsat" : "sat";
            }
            String content = "(set-info :status " + exp + ")\n" + body;
            Files.writeString(out.resolve(String.format("hard_%03d.smt2", i)), content);
        }
        System.out.println("Generated " + count + " hard files in " + out);
    }
}
