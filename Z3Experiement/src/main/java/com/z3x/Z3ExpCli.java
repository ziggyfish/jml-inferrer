package com.z3x;

import com.z3x.solver.Solver;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.List;

/**
 * z3-compatible CLI for Z3Experiement. Reads SMT-LIB2 commands from stdin in {@code -in} mode
 * and writes sat/unsat verdicts to stdout. Accepts and ignores most z3 command-line options
 * so OpenJML's invocation lines (e.g. {@code z3 -in -smt2 -t:120000 -memory:8192}) work as-is.
 *
 * Supported behaviours:
 *  - {@code -in} mode (read from stdin, default and only mode).
 *  - {@code (check-sat)}: print sat/unsat/unknown on its own line.
 *  - {@code (get-model)} / {@code (get-unsat-core)}: forwarded to the underlying Solver.
 *  - {@code (set-option ...)} / {@code (set-info ...)}: parsed; most ignored.
 *  - {@code (reset)}: reset the underlying Solver.
 *  - {@code (exit)}: terminate.
 *
 * Not supported (will likely produce unknown or stay silent):
 *  - {@code (get-assignment)} (OpenJML doesn't use it for the Java VC corpus).
 *  - {@code (display ...)} and Z3 extensions.
 *
 * Designed so OpenJML's existing z3 invocation can be redirected here by replacing the binary
 * path in the {@code Solvers-linux} directory (or via the {@code OPENJML_PROVER=z3exp} env var
 * that {@link com.jml.inferrer.validation.OpenJMLInvoker} respects).
 */
public final class Z3ExpCli {

    private static boolean printSuccess = false;

    public static void main(String[] args) throws Exception {
        Solver solver = new Solver();
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
        StringBuilder buf = new StringBuilder();
        int paren = 0;
        boolean inString = false;
        boolean inComment = false;
        boolean inQuotedSymbol = false;
        int ch;
        while ((ch = br.read()) != -1) {
            char c = (char) ch;
            buf.append(c);
            if (inComment) { if (c == '\n') inComment = false; continue; }
            if (inString)  { if (c == '"') inString = false; continue; }
            if (inQuotedSymbol) { if (c == '|') inQuotedSymbol = false; continue; }
            if (c == ';') { inComment = true; continue; }
            if (c == '"') { inString = true; continue; }
            if (c == '|') { inQuotedSymbol = true; continue; }
            if (c == '(') paren++;
            else if (c == ')') {
                paren--;
                if (paren == 0) {
                    String cmd = buf.toString();
                    buf.setLength(0);
                    if (!handleCommand(solver, cmd)) return;
                }
            }
        }
    }

    /** Process one top-level S-expression. Return false to exit. */
    private static boolean handleCommand(Solver solver, String cmd) {
        String trimmed = cmd.trim();
        if (trimmed.startsWith("(exit") || trimmed.startsWith("( exit")) return false;
        // Track :print-success state — OpenJML enables it for synchronisation.
        if (trimmed.contains(":print-success")) {
            if (trimmed.contains("true")) printSuccess = true;
            if (trimmed.contains("false")) printSuccess = false;
        }
        // Several commands z3 responds to but we don't implement: emit a benign reply.
        if (trimmed.startsWith("(get-info") || trimmed.startsWith("( get-info")) {
            // Echo a generic response.
            System.out.println("unsupported");
            System.out.flush();
            return true;
        }
        if (trimmed.startsWith("(echo") || trimmed.startsWith("( echo")) {
            // (echo "TEXT") → print TEXT.
            int q1 = trimmed.indexOf('"');
            int q2 = trimmed.lastIndexOf('"');
            if (q1 > 0 && q2 > q1) System.out.println(trimmed.substring(q1 + 1, q2));
            else System.out.println();
            System.out.flush();
            return true;
        }
        // check-sat: forward to solver and print verdict.
        boolean isCheckSat = trimmed.startsWith("(check-sat") || trimmed.startsWith("( check-sat");
        boolean isGet = trimmed.startsWith("(get-") || trimmed.startsWith("( get-");
        try {
            List<Solver.Verdict> verdicts = solver.run(trimmed);
            if (isCheckSat) {
                for (Solver.Verdict v : verdicts) {
                    System.out.println(switch (v) {
                        case SAT -> "sat";
                        case UNSAT -> "unsat";
                        case UNKNOWN -> "unknown";
                    });
                }
                System.out.flush();
            } else if (isGet) {
                // get-model / get-unsat-core handled by Solver.run via println; no extra output.
            } else if (printSuccess) {
                System.out.println("success");
                System.out.flush();
            }
        } catch (Exception e) {
            // z3 prints (error "...") on parse/eval failures. Match format.
            String msg = e.getMessage() == null ? e.getClass().getSimpleName() : e.getMessage();
            System.out.println("(error \"" + msg.replace("\"", "\\\"").replace("\n", " ") + "\")");
            if (printSuccess) System.out.println("success");
            System.out.flush();
        }
        return true;
    }
}
