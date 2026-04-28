package com.jml.inferrer.validation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Invokes OpenJML via ProcessBuilder for Extended Static Checking (ESC).
 *
 * Command: openjml --esc --timeout N --classpath tmpdir file.java
 */
public class OpenJMLInvoker {

    private static final Logger logger = LoggerFactory.getLogger(OpenJMLInvoker.class);

    private final Path openjmlPath;
    private final int timeoutSeconds;

    /**
     * Creates a new invoker.
     *
     * @param openjmlPath    path to the openjml executable or JAR
     * @param timeoutSeconds per-file verification timeout in seconds
     */
    public OpenJMLInvoker(Path openjmlPath, int timeoutSeconds) {
        this.openjmlPath = openjmlPath;
        this.timeoutSeconds = timeoutSeconds;
    }

    /**
     * Runs OpenJML ESC on a single Java source file.
     *
     * @param sourceFile the Java file to verify
     * @param classpath  additional classpath entries (may be null)
     * @return the invocation result
     */
    public InvocationResult verify(Path sourceFile, Path classpath) {
        List<String> command = buildCommand(sourceFile, classpath);

        logger.debug("Running OpenJML: {}", String.join(" ", command));

        long startTime = System.currentTimeMillis();

        try {
            ProcessBuilder pb = new ProcessBuilder(command);
            pb.redirectErrorStream(true);
            pb.directory(sourceFile.getParent().toFile());

            Process process = pb.start();
            String output = new String(process.getInputStream().readAllBytes());

            boolean completed = process.waitFor(timeoutSeconds, TimeUnit.SECONDS);
            long durationMs = System.currentTimeMillis() - startTime;

            if (!completed) {
                process.destroyForcibly();
                logger.warn("OpenJML timed out after {}s for: {}", timeoutSeconds, sourceFile);
                return new InvocationResult(-1, output, durationMs, true);
            }

            int exitCode = process.exitValue();
            logger.debug("OpenJML finished with exit code {} for: {} ({}ms)",
                    exitCode, sourceFile, durationMs);
            return new InvocationResult(exitCode, output, durationMs, false);

        } catch (IOException e) {
            long durationMs = System.currentTimeMillis() - startTime;
            logger.error("Failed to invoke OpenJML: {}", e.getMessage());
            return new InvocationResult(-1, "Error: " + e.getMessage(), durationMs, false);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            long durationMs = System.currentTimeMillis() - startTime;
            return new InvocationResult(-1, "Interrupted", durationMs, false);
        }
    }

    private List<String> buildCommand(Path sourceFile, Path classpath) {
        List<String> command = new ArrayList<>();

        String execName = openjmlPath.getFileName().toString();

        if (execName.endsWith(".jar")) {
            // Invoke via java -jar
            command.add("java");
            command.add("-jar");
            command.add(openjmlPath.toAbsolutePath().toString());
        } else {
            command.add(openjmlPath.toAbsolutePath().toString());
        }

        command.add("--esc");
        command.add("--timeout");
        command.add(String.valueOf(timeoutSeconds));

        if (classpath != null) {
            command.add("--classpath");
            command.add(classpath.toAbsolutePath().toString());
        }

        // Strict-but-tractable configuration. `--code-math=safe` makes every arithmetic op
        // in method bodies an overflow proof obligation; `--spec-math=bigint` lets specs
        // speak about mathematical integers (so a precondition can express
        // `(\bigint)a + (\bigint)b <= MAX_VALUE` without itself being a circular overflow
        // claim). `--arithmetic-failure=hard` promotes overflow warnings to errors.
        //
        // `--nonnull-by-default` was tried but requires the inferrer to emit @Nullable
        // on every field that could hold null — linked-list nodes, optional state, etc.
        // Switched to `--nullable-by-default` (matches Java default) so refs are nullable
        // unless the inferrer can prove non-null. `--check-feasibility=all` was also tried
        // but timed out the SMT solver on common shapes (sum of squares, multi-step
        // arithmetic).
        command.add("--code-math=safe");
        command.add("--spec-math=bigint");
        command.add("--arithmetic-failure=hard");
        command.add("--nullable-by-default");

        // Counter-example output: when verification fails and z3 returns SAT
        // with a model, OpenJML pretty-prints the violating input bindings and
        // an execution trace pointing at the failing assertion. Lets the test
        // harness (and the inferrer's calibration analysis) tell apart
        //   (a) "spec wrong on input X"   — counter-example present
        //   (b) "solver gave up"          — "Validity is unknown - no model"
        // Costs ~10-20% on the failing-test path; no cost when verification
        // succeeds. See FormalVerificationTestBase for how the output is
        // streamed into the test log.
        command.add("--counterexample");
        command.add("--trace");
        command.add("--subexpressions");

        // The fork-built OpenJML emits `define-fun-rec` for \sum / \product /
        // \num_of; the default bundled z3-4.3.1 predates that command. Prefer
        // z3-4.7.1 or cvc5 (both support define-fun-rec) when available.
        // The OPENJML_PROVER env var lets experiments pick between them.
        Path openjmlDir = openjmlPath.toAbsolutePath().getParent();
        if (openjmlDir != null) {
            String preferred = System.getenv("OPENJML_PROVER");
            if (preferred == null || preferred.isBlank()) preferred = "z3";
            Path solversDir = openjmlDir.resolve("Solvers-linux");
            Path cvc5 = solversDir.resolve("cvc5");
            Path z3_4_7 = solversDir.resolve("z3-4.7.1");
            if ("cvc5".equalsIgnoreCase(preferred) && java.nio.file.Files.isExecutable(cvc5)) {
                command.add("--prover=cvc5");
                command.add("--exec");
                command.add(cvc5.toAbsolutePath().toString());
            } else if (java.nio.file.Files.isExecutable(z3_4_7)) {
                command.add("--prover=z3_4_3");
                command.add("--exec");
                command.add(z3_4_7.toAbsolutePath().toString());
            }
        }

        command.add(sourceFile.toAbsolutePath().toString());

        return command;
    }

    /**
     * Result of invoking OpenJML on a single file.
     */
    public record InvocationResult(int exitCode, String output, long durationMs, boolean timedOut) {

        /**
         * Returns true if the process completed without error.
         * Note: exit code 0 does NOT mean all specs verified — OpenJML returns 0
         * even when verification failures are found. Always check the output
         * for actual verification results.
         */
        public boolean isSuccess() {
            return exitCode == 0 && !timedOut;
        }

        /**
         * Returns true if the output contains any warning or error lines,
         * indicating that OpenJML found issues even if exit code was 0.
         */
        public boolean hasOutputWarnings() {
            if (output == null || output.isBlank()) return false;
            return output.contains("warning:") || output.contains("error:");
        }
    }
}
