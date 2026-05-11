package com.z3x;

import com.z3x.solver.Solver;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

/**
 * Race Z3Experiement against an external z3 binary. Whichever produces a definitive verdict first
 * wins; the loser is interrupted. The verdict (sat / unsat) is printed to stdout.
 *
 * Intended for OpenJML to invoke via:
 *   {@code java -cp ... com.z3x.Portfolio <smt2-file> [<z3-binary>] [<timeout-ms>]}
 *
 * If z3 is not on PATH (or fails for any reason), Z3Experiement's verdict is used.
 */
public final class Portfolio {

    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("usage: Portfolio <smt2-file> [<z3-binary>] [<timeout-ms>]");
            System.exit(64);
        }
        Path file = Path.of(args[0]);
        String z3Bin = args.length >= 2 ? args[1] : "z3";
        long timeoutMs = args.length >= 3 ? Long.parseLong(args[2]) : 10_000;
        String src = Files.readString(file);
        Result r = race(src, z3Bin, timeoutMs);
        System.out.println(r.verdict);
        System.err.printf("won-by=%s time=%.1fms%n", r.winner, r.timeMs);
    }

    public record Result(String verdict, String winner, double timeMs) {}

    public static Result race(String src, String z3Bin, long timeoutMs) {
        ExecutorService exec = Executors.newFixedThreadPool(2);
        long t0 = System.nanoTime();
        Future<String> own = exec.submit((Callable<String>) () -> {
            try {
                List<Solver.Verdict> v = new Solver().run(src);
                if (v.isEmpty()) return "unknown";
                return switch (v.get(v.size() - 1)) {
                    case SAT -> "sat";
                    case UNSAT -> "unsat";
                    case UNKNOWN -> "unknown";
                };
            } catch (Exception e) {
                return "error:" + e.getClass().getSimpleName();
            }
        });
        Future<String> ext = exec.submit((Callable<String>) () -> runZ3(z3Bin, src));
        String winner = null;
        String verdict = "timeout";
        try {
            // Poll both; the first definitive verdict wins.
            long deadline = System.nanoTime() + timeoutMs * 1_000_000L;
            while (System.nanoTime() < deadline) {
                if (own.isDone()) {
                    String r = own.get();
                    if (r != null && (r.equals("sat") || r.equals("unsat"))) {
                        winner = "z3experiement";
                        verdict = r;
                        break;
                    }
                }
                if (ext.isDone()) {
                    String r = ext.get();
                    if (r != null && (r.equals("sat") || r.equals("unsat"))) {
                        winner = "z3";
                        verdict = r;
                        break;
                    }
                }
                Thread.sleep(5);
            }
            if (winner == null) {
                // One of them might have returned an unknown/error; fall back to either non-null.
                if (own.isDone()) { winner = "z3experiement"; verdict = own.get(); }
                else if (ext.isDone()) { winner = "z3"; verdict = ext.get(); }
                else { winner = "none"; verdict = "timeout"; }
            }
        } catch (InterruptedException | ExecutionException e) {
            winner = "error";
            verdict = "error";
        } finally {
            own.cancel(true);
            ext.cancel(true);
            exec.shutdownNow();
        }
        double ms = (System.nanoTime() - t0) / 1e6;
        return new Result(verdict, winner, ms);
    }

    /** Spawn a z3 subprocess that reads the SMT-LIB script on stdin and prints sat/unsat on stdout. */
    private static String runZ3(String bin, String src) {
        try {
            ProcessBuilder pb = new ProcessBuilder(bin, "-in");
            pb.redirectErrorStream(true);
            Process p = pb.start();
            try (OutputStream stdin = p.getOutputStream()) {
                stdin.write(src.getBytes(StandardCharsets.UTF_8));
                stdin.flush();
            }
            String output = new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
            if (!p.waitFor(60, TimeUnit.SECONDS)) { p.destroyForcibly(); return "timeout"; }
            // The last line is typically the verdict.
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
