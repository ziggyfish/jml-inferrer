package com.jml.inferrer.ci;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/**
 * Resolves a git diff specifier (e.g. {@code origin/main..HEAD}) into the
 * list of changed {@code .java} files relative to a working-tree root.
 *
 * <p>Uses {@code git} as a subprocess; if {@code git} is not on PATH, the
 * resolver returns an empty list and logs a warning. This is the
 * documented fail-open semantics of the CI integration: a failure here
 * never blocks the rest of the pipeline.</p>
 */
public final class DiffResolver {

    private static final Logger logger = LoggerFactory.getLogger(DiffResolver.class);

    private DiffResolver() {
    }

    public static List<Path> changedJavaFiles(Path root, String diffSpec) {
        List<Path> result = new ArrayList<>();
        ProcessBuilder pb = new ProcessBuilder("git", "diff", "--name-only", diffSpec);
        pb.directory(root.toFile());
        pb.redirectErrorStream(true);
        try {
            Process p = pb.start();
            try (BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                String line;
                while ((line = r.readLine()) != null) {
                    if (line.endsWith(".java")) {
                        Path resolved = root.resolve(line);
                        if (java.nio.file.Files.exists(resolved)) {
                            result.add(resolved);
                        }
                    }
                }
            }
            p.waitFor();
        } catch (IOException | InterruptedException e) {
            logger.warn("git diff failed; treating diff as empty (fail-open): {}", e.getMessage());
            return List.of();
        }
        return result;
    }
}
