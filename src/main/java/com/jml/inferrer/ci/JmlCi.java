package com.jml.inferrer.ci;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

/**
 * RQ4 Phase 3.2 — CI/CD integration CLI.
 *
 * <p>Three subcommands tailored to the per-PR workflow described in
 * {@code journal/rq4_cicd_design.md}:</p>
 *
 * <ul>
 *   <li>{@code infer} — run the inferrer on a set of source files (or a
 *       diff against a base ref) and write the inferred JML annotations
 *       in place. Supports a content-hash cache so unchanged methods are
 *       skipped.</li>
 *   <li>{@code verify} — discharge the inferred specifications through
 *       OpenJML's Extended Static Checker. Reports per-method outcomes
 *       and optionally writes a machine-readable JSON summary.</li>
 *   <li>{@code summary} — render a markdown summary of the most recent
 *       inference + verification run, suitable for posting as a PR
 *       comment. Distinguishes new clauses from carried-over clauses.</li>
 * </ul>
 *
 * <p>The CLI is deliberately stateless across invocations except via the
 * cache directory ({@code --cache-dir}, default {@code .jml-cache/}).
 * The cache key for each method is
 * {@code sha256(method-source + callee-spec-hashes + inferrer-version)}.</p>
 *
 * <p>Failure mode: any unexpected exception is caught and reported to
 * stdout as a human-readable message; the process exits with status 0
 * unless invoked with {@code --strict}, so the inferrer never blocks a
 * merge by default. The {@code summary} subcommand reads the most recent
 * run's JSON output regardless of strictness, so the PR comment always
 * appears.</p>
 */
public class JmlCi {

    private static final Logger logger = LoggerFactory.getLogger(JmlCi.class);

    public static void main(String[] args) {
        int exitCode;
        try {
            exitCode = new JmlCi().run(args, System.out);
        } catch (Throwable t) {
            System.err.println("[jml-ci] unexpected error: " + t.getMessage());
            t.printStackTrace(System.err);
            exitCode = 2;
        }
        System.exit(exitCode);
    }

    int run(String[] args, PrintStream out) throws Exception {
        if (args.length < 1 || isHelp(args[0])) {
            printUsage(out);
            return args.length == 0 ? 1 : 0;
        }
        String subcommand = args[0];
        String[] rest = Arrays.copyOfRange(args, 1, args.length);
        return switch (subcommand) {
            case "infer" -> new InferCommand().execute(parseOptions(rest), out);
            case "verify" -> new VerifyCommand().execute(parseOptions(rest), out);
            case "summary" -> new SummaryCommand().execute(parseOptions(rest), out);
            case "embed" -> new EmbedCommand().execute(parseOptions(rest), out);
            default -> {
                out.println("[jml-ci] unknown subcommand: " + subcommand);
                printUsage(out);
                yield 1;
            }
        };
    }

    private boolean isHelp(String s) {
        return s.equals("-h") || s.equals("--help") || s.equals("help");
    }

    private void printUsage(PrintStream out) {
        out.println("Usage: jml-ci <subcommand> [options]");
        out.println();
        out.println("Subcommands:");
        out.println("  infer   --root <dir>  [--diff <base..head>]  [--cache-dir <dir>]  [--strict]");
        out.println("  verify  --root <dir>  [--diff <base..head>]  [--report <file>]   [--strict]");
        out.println("  embed   --jar <input.jar>  --output <output.jar>");
        out.println("  summary --report <file>  [--format markdown|json]  [--out <file>]");
        out.println();
        out.println("Common options:");
        out.println("  --diff <base..head>   restrict work to files changed in the git diff");
        out.println("  --cache-dir <dir>     content-hash keyed cache (default .jml-cache/)");
        out.println("  --strict              exit with non-zero status on inference / verify failures");
        out.println("  --help, -h            show this help");
    }

    /**
     * Parse {@code --key value} pairs and {@code --flag} switches from a
     * flat argument list. Flag keys are stored with empty-string value so
     * callers can detect their presence with {@code containsKey}.
     */
    static java.util.Map<String, String> parseOptions(String[] args) {
        java.util.Map<String, String> opts = new java.util.LinkedHashMap<>();
        int i = 0;
        while (i < args.length) {
            String a = args[i];
            if (!a.startsWith("--")) {
                throw new IllegalArgumentException("expected --flag, got: " + a);
            }
            if (i + 1 < args.length && !args[i + 1].startsWith("--")) {
                opts.put(a.substring(2), args[i + 1]);
                i += 2;
            } else {
                opts.put(a.substring(2), "");
                i += 1;
            }
        }
        return opts;
    }

    static List<Path> resolveSourceRoots(String root, String diff) {
        Path rootPath = Paths.get(root != null ? root : ".");
        if (!Files.isDirectory(rootPath)) {
            throw new IllegalArgumentException("root is not a directory: " + rootPath);
        }
        if (diff == null || diff.isBlank()) return List.of(rootPath);
        return DiffResolver.changedJavaFiles(rootPath, diff);
    }
}
