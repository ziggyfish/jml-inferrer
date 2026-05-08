package com.z3x;

import com.z3x.solver.Solver;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.stream.Stream;

/**
 * Run every .smt2 file under a directory and compare each verdict to the file's declared status
 * (from (set-info :status sat|unsat|unknown)). Emits a per-file line and a final summary; timeouts
 * are surfaced too.
 *
 * Usage:
 *   java -cp out com.z3x.BenchmarkRunner &lt;dir&gt; [&lt;timeout_ms&gt;]
 */
public final class BenchmarkRunner {

    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("usage: BenchmarkRunner <dir> [timeout_ms]");
            System.exit(64);
        }
        Path root = Path.of(args[0]);
        long timeoutMs = args.length >= 2 ? Long.parseLong(args[1]) : 5_000;
        List<Path> files = new ArrayList<>();
        try (Stream<Path> stream = Files.walk(root)) {
            stream.filter(p -> p.toString().endsWith(".smt2")).sorted(Comparator.naturalOrder()).forEach(files::add);
        }
        int pass = 0, fail = 0, timeout = 0, error = 0, unknown = 0;
        ExecutorService exec = Executors.newSingleThreadExecutor();
        long t0 = System.nanoTime();
        for (Path p : files) {
            String src;
            try { src = Files.readString(p); }
            catch (IOException e) { System.out.printf("ERR    %s (read failed)%n", p); error++; continue; }
            Future<Outcome> fut = exec.submit(() -> runOne(src));
            try {
                Outcome o = fut.get(timeoutMs, TimeUnit.MILLISECONDS);
                String marker;
                if (o.expected.isEmpty() || o.expected.equals("unknown")) {
                    marker = "?";
                    unknown++;
                } else if (o.actualMatchesExpected()) {
                    marker = "PASS";
                    pass++;
                } else {
                    marker = "FAIL";
                    fail++;
                }
                System.out.printf("%-5s %-8s exp=%-7s got=%-7s %.1fms %s%n",
                        marker, "", o.expected.isEmpty() ? "-" : o.expected,
                        o.actual.toString().toLowerCase(), o.timeMs, p);
            } catch (TimeoutException te) {
                fut.cancel(true);
                System.out.printf("TIMEOUT (>%dms) %s%n", timeoutMs, p);
                timeout++;
            } catch (Exception e) {
                System.out.printf("ERR    %s : %s%n", p, e.getCause() == null ? e : e.getCause());
                error++;
            }
        }
        exec.shutdownNow();
        double total = (System.nanoTime() - t0) / 1e9;
        System.out.printf("%n=== %d files in %.1fs : %d pass, %d fail, %d timeout, %d error, %d unknown ===%n",
                files.size(), total, pass, fail, timeout, error, unknown);
        if (fail > 0 || error > 0) System.exit(1);
    }

    private static Outcome runOne(String src) {
        long t0 = System.nanoTime();
        Solver solver = new Solver();
        List<Solver.Verdict> verdicts = solver.run(src);
        Solver.Verdict v = verdicts.isEmpty() ? Solver.Verdict.UNKNOWN : verdicts.get(verdicts.size() - 1);
        return new Outcome(solver.declaredStatus(), v, (System.nanoTime() - t0) / 1e6);
    }

    private record Outcome(String expected, Solver.Verdict actual, double timeMs) {
        boolean actualMatchesExpected() {
            String a = switch (actual) {
                case SAT -> "sat";
                case UNSAT -> "unsat";
                case UNKNOWN -> "unknown";
            };
            return a.equals(expected);
        }
    }
}
