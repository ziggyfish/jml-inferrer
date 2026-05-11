package com.z3x;

import com.z3x.solver.Solver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;

/**
 * Fair race: persistent z3 (one process, fed many problems over stdin) vs. persistent Z3Experiement
 * (one JVM, fresh Solver per file). Both pay startup once; the comparison is solver work only.
 *
 * z3 protocol: between problems we issue (reset) so declarations don't leak. Z3Experiement: a
 * fresh com.z3x.Solver per file (the JVM and JIT-warm classes are shared).
 *
 * The first 5 files of each side are treated as warmup and excluded from the timing total.
 *
 * Usage: java -cp out com.z3x.PersistentRace &lt;dir&gt; &lt;z3-binary&gt;
 */
public final class PersistentRace {

    private static final int WARMUP = 5;

    public static void main(String[] args) throws Exception {
        Path root = Path.of(args[0]);
        String z3Bin = args[1];
        boolean coldZ3 = args.length > 2 && args[2].equals("cold");
        List<Path> files = new ArrayList<>();
        try (Stream<Path> stream = Files.walk(root)) {
            stream.filter(p -> p.toString().endsWith(".smt2"))
                    .sorted(Comparator.naturalOrder()).forEach(files::add);
        }
        // Phase 1: warmup + measure Z3Experiement, persistent JVM (fresh Solver per file).
        long ownTotalNs = 0;
        int ownTimed = 0;
        List<String> ownVerdicts = new ArrayList<>(files.size());
        long[] perFileOwn = new long[files.size()];
        for (int i = 0; i < files.size(); i++) {
            String src = Files.readString(files.get(i));
            long t0 = System.nanoTime();
            String v = runOwn(src);
            long dur = System.nanoTime() - t0;
            perFileOwn[i] = dur;
            ownVerdicts.add(v);
            if (i >= WARMUP) { ownTotalNs += dur; ownTimed++; }
        }
        // Phase 2: z3 — cold (spawn per query) or persistent (reset between).
        long z3TotalNs = 0;
        int z3Timed = 0;
        List<String> z3Verdicts = new ArrayList<>(files.size());
        long[] perFileZ3Cold = new long[files.size()];
        if (coldZ3) {
            for (int i = 0; i < files.size(); i++) {
                String src = Files.readString(files.get(i));
                long t0 = System.nanoTime();
                String verdict = runColdZ3(z3Bin, src);
                long dur = System.nanoTime() - t0;
                perFileZ3Cold[i] = dur;
                z3Verdicts.add(verdict);
                if (i >= WARMUP) { z3TotalNs += dur; z3Timed++; }
            }
        } else {
        ProcessBuilder pb = new ProcessBuilder(z3Bin, "-in");
        pb.redirectErrorStream(true);
        Process p = pb.start();
        try (BufferedWriter w = new BufferedWriter(new OutputStreamWriter(p.getOutputStream(), StandardCharsets.UTF_8));
             BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8))) {
            long[] perFileZ3 = new long[files.size()];
            for (int i = 0; i < files.size(); i++) {
                String src = Files.readString(files.get(i));
                long t0 = System.nanoTime();
                w.write("(reset)\n");
                w.write(src);
                w.flush();
                // Read until we see a sat/unsat/unknown line.
                String verdict = "error";
                String line;
                while ((line = r.readLine()) != null) {
                    line = line.trim();
                    if (line.equals("sat") || line.equals("unsat") || line.equals("unknown")) {
                        verdict = line;
                        break;
                    }
                }
                long dur = System.nanoTime() - t0;
                perFileZ3[i] = dur;
                z3Verdicts.add(verdict);
                if (i >= WARMUP) { z3TotalNs += dur; z3Timed++; }
            }
            // Per-file detail (post warmup): side-by-side
            for (int i = WARMUP; i < files.size(); i++) {
                System.out.printf("  %-30s Z3Exp %8.1fms  z3 %8.1fms  ratio %5.2fx%n",
                        files.get(i).getFileName(),
                        perFileOwn[i] / 1e6, perFileZ3[i] / 1e6,
                        (double) perFileOwn[i] / Math.max(1, perFileZ3[i]));
            }
            w.write("(exit)\n");
            w.flush();
        }
        p.waitFor();
        }

        // Verdict agreement
        int agreed = 0, disagreed = 0;
        for (int i = 0; i < files.size(); i++) {
            if (ownVerdicts.get(i).equals(z3Verdicts.get(i))) agreed++;
            else {
                disagreed++;
                System.out.printf("  DISAGREE %s: Z3Exp=%s z3=%s%n",
                        files.get(i).getFileName(), ownVerdicts.get(i), z3Verdicts.get(i));
            }
        }

        System.out.println("Persistent-mode race (warmup " + WARMUP + " files excluded):");
        System.out.printf("  files: %d (timed: %d)%n", files.size(), ownTimed);
        System.out.printf("  Z3Exp: %.1f ms total, %.3f ms/file%n",
                ownTotalNs / 1e6, ownTotalNs / 1e6 / Math.max(1, ownTimed));
        System.out.printf("  z3:    %.1f ms total, %.3f ms/file%n",
                z3TotalNs / 1e6, z3TotalNs / 1e6 / Math.max(1, z3Timed));
        System.out.printf("  ratio: %.2fx (Z3Exp/z3, lower = Z3Exp faster)%n",
                (double) ownTotalNs / Math.max(1, z3TotalNs));
        System.out.printf("  verdicts: %d agreed, %d disagreed%n", agreed, disagreed);
    }

    private static String runColdZ3(String bin, String src) {
        try {
            ProcessBuilder pb = new ProcessBuilder(bin, "-in");
            pb.redirectErrorStream(true);
            Process p = pb.start();
            try (java.io.OutputStream stdin = p.getOutputStream()) {
                stdin.write(src.getBytes(StandardCharsets.UTF_8));
                stdin.flush();
            }
            String out = new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
            if (!p.waitFor(30, java.util.concurrent.TimeUnit.SECONDS)) { p.destroyForcibly(); return "timeout"; }
            String[] lines = out.trim().split("\\R");
            for (int i = lines.length - 1; i >= 0; i--) {
                String l = lines[i].trim();
                if (l.equals("sat") || l.equals("unsat") || l.equals("unknown")) return l;
            }
            return "error";
        } catch (Exception e) { return "error"; }
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
        } catch (Exception e) { return "error:" + e.getClass().getSimpleName(); }
    }
}
