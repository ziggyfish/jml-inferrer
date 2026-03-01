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

        // Suppress some noisy warnings
        command.add("--no-purityCheck");

        command.add(sourceFile.toAbsolutePath().toString());

        return command;
    }

    /**
     * Result of invoking OpenJML on a single file.
     */
    public record InvocationResult(int exitCode, String output, long durationMs, boolean timedOut) {

        /**
         * Returns true if the verification completed successfully (all verified).
         */
        public boolean isSuccess() {
            return exitCode == 0 && !timedOut;
        }
    }
}
