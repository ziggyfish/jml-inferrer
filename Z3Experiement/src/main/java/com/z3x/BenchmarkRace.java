package com.z3x;

import com.z3x.solver.Solver;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

/**
 * Race Z3Experiement against z3 on every .smt2 file under a directory. Prints a per-file
 * comparison and overall totals.
 *
 * Usage: java -cp out com.z3x.BenchmarkRace &lt;dir&gt; &lt;z3-binary&gt; [timeout-ms]
 */
public final class BenchmarkRace {

    public static void main(String[] args) throws Exception {
        if (args.length < 2) {
            System.err.println("usage: BenchmarkRace <dir> <z3-binary> [<timeout-ms>]");
            System.exit(64);
        }
        Path root = Path.of(args[0]);
        String z3Bin = args[1];
        long timeoutMs = args.length >= 3 ? Long.parseLong(args[2]) : 10_000;
        List<Path> files = new ArrayList<>();
        try (Stream<Path> stream = Files.walk(root)) {
            stream.filter(p -> p.toString().endsWith(".smt2"))
                    .sorted(Comparator.naturalOrder()).forEach(files::add);
        }
        System.out.printf("%-55s  %12s  %12s  %s%n", "file", "Z3Exp(ms)", "z3(ms)", "ratio");
        System.out.println("-".repeat(95));
        long totalOwnNs = 0, totalZ3Ns = 0;
        int ownWins = 0, z3Wins = 0, ties = 0, agreed = 0, disagreed = 0;
        for (Path p : files) {
            String src = Files.readString(p);
            long t0 = System.nanoTime();
            String ownV = runOwn(src);
            long ownNs = System.nanoTime() - t0;
            long t1 = System.nanoTime();
            String z3V = runZ3(z3Bin, src, timeoutMs);
            long z3Ns = System.nanoTime() - t1;
            totalOwnNs += ownNs;
            totalZ3Ns += z3Ns;
            boolean agree = ownV.equals(z3V);
            if (agree) agreed++; else disagreed++;
            double ownMs = ownNs / 1e6;
            double z3Ms = z3Ns / 1e6;
            String marker = agree ? "" : " DISAGREE(" + ownV + "/" + z3V + ")";
            double ratio = z3Ms == 0 ? Double.NaN : ownMs / z3Ms;
            if (ownMs < z3Ms) ownWins++;
            else if (z3Ms < ownMs) z3Wins++;
            else ties++;
            System.out.printf("%-55s  %12.2f  %12.2f  %6.2fx%s%n",
                    p.getFileName(), ownMs, z3Ms, ratio, marker);
        }
        System.out.println("-".repeat(95));
        System.out.printf("Totals: Z3Exp %.1f ms, z3 %.1f ms, ratio %.2fx (lower is better for Z3Exp)%n",
                totalOwnNs / 1e6, totalZ3Ns / 1e6, (double) totalOwnNs / totalZ3Ns);
        System.out.printf("Per-file wins: Z3Exp %d, z3 %d, ties %d%n", ownWins, z3Wins, ties);
        System.out.printf("Verdicts: %d agreed, %d disagreed%n", agreed, disagreed);
    }

    private static String runOwn(String src) {
        try {
            List<Solver.Verdict> v = new Solver().run(src);
            if (v.isEmpty()) return "unknown";
            return switch (v.get(v.size() - 1)) {
                case SAT -> "sat";
                case UNSAT -> "unsat";
                case UNKNOWN -> "unknown";
            };
        } catch (Exception e) { return "error"; }
    }

    private static String runZ3(String bin, String src, long timeoutMs) {
        try {
            ProcessBuilder pb = new ProcessBuilder(bin, "-in");
            pb.redirectErrorStream(true);
            Process p = pb.start();
            try (OutputStream stdin = p.getOutputStream()) {
                stdin.write(src.getBytes(StandardCharsets.UTF_8));
                stdin.flush();
            }
            String output = new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
            if (!p.waitFor(timeoutMs, TimeUnit.MILLISECONDS)) { p.destroyForcibly(); return "timeout"; }
            String[] lines = output.trim().split("\\R");
            for (int i = lines.length - 1; i >= 0; i--) {
                String l = lines[i].trim();
                if (l.equals("sat") || l.equals("unsat") || l.equals("unknown")) return l;
            }
            return "error";
        } catch (IOException | InterruptedException e) {
            return "error";
        }
    }
}
