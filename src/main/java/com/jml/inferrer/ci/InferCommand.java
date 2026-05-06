package com.jml.inferrer.ci;

import com.jml.inferrer.processor.CodebaseProcessor;
import com.jml.inferrer.validation.OpenJMLValidator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

/**
 * {@code jml-ci infer} — run the inferrer over a directory or a git diff.
 *
 * <p>For each {@code .java} file in scope, look up its content hash in
 * the cache; if hit, skip; if miss, run the inferrer and write the
 * resulting annotations in place. Records the per-file outcome in a
 * report file consumable by {@code jml-ci summary}.</p>
 */
class InferCommand {

    private static final Logger logger = LoggerFactory.getLogger(InferCommand.class);

    int execute(Map<String, String> opts, PrintStream out) throws Exception {
        String root = opts.getOrDefault("root", ".");
        String diff = opts.get("diff");
        String cacheDir = opts.getOrDefault("cache-dir", ".jml-cache");
        String reportPath = opts.getOrDefault("report", ".jml-cache/infer-report.json");
        boolean strict = opts.containsKey("strict");

        List<Path> files = (diff == null || diff.isBlank())
                ? collectJavaFiles(Paths.get(root))
                : DiffResolver.changedJavaFiles(Paths.get(root), diff);

        Path cache = Paths.get(cacheDir);
        Files.createDirectories(cache);

        // Two-stage workflow:
        //   Stage A: per-file cache decision. Files whose content hash is
        //            already cached are skipped (no parse, no infer). Files
        //            whose content hash is missing are queued for inference.
        //   Stage B: if any files were queued, run the inferrer on the
        //            project root. The inferrer needs the whole codebase
        //            to build its call graph; processing single files in
        //            isolation would lose interprocedural information.
        Map<String, FileOutcome> outcomes = new LinkedHashMap<>();
        List<Path> queued = new java.util.ArrayList<>();
        int cached = 0;
        for (Path file : files) {
            String key = CacheKey.forFile(file);
            Path marker = cache.resolve(key);
            if (Files.exists(marker)) {
                cached++;
                outcomes.put(file.toString(), new FileOutcome(file.toString(), "cached", null));
            } else {
                queued.add(file);
                outcomes.put(file.toString(), new FileOutcome(file.toString(), "pending", null));
            }
        }

        int processed = 0;
        int errors = 0;
        if (!queued.isEmpty()) {
            try {
                CodebaseProcessor processor = new CodebaseProcessor();
                processor.processCodebase(Paths.get(root));
                processed = queued.size();
                for (Path file : queued) {
                    String key = CacheKey.forFile(file);
                    Files.writeString(cache.resolve(key), "ok\n",
                            StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
                    outcomes.put(file.toString(), new FileOutcome(file.toString(), "inferred", null));
                }
            } catch (Exception e) {
                errors = queued.size();
                for (Path file : queued) {
                    outcomes.put(file.toString(), new FileOutcome(file.toString(), "error", e.getMessage()));
                }
                logger.warn("inference failed: {}", e.getMessage());
            }
        }

        writeReport(Paths.get(reportPath), outcomes, processed, cached, errors);

        out.printf("[jml-ci infer] %d files: %d inferred, %d cached, %d errors%n",
                files.size(), processed, cached, errors);
        out.printf("[jml-ci infer] report written to %s%n", reportPath);

        if (strict && errors > 0) return 1;
        return 0;
    }

    private static List<Path> collectJavaFiles(Path root) throws Exception {
        try (Stream<Path> s = Files.walk(root)) {
            return s.filter(p -> p.toString().endsWith(".java"))
                    .filter(p -> !p.toString().contains("target/"))
                    .filter(p -> !p.toString().contains("\\target\\"))
                    .toList();
        }
    }

    private static void writeReport(Path path, Map<String, FileOutcome> outcomes,
                                     int inferred, int cached, int errors) throws Exception {
        Files.createDirectories(path.getParent());
        StringBuilder json = new StringBuilder();
        json.append("{\n");
        json.append("  \"command\": \"infer\",\n");
        json.append("  \"summary\": { \"inferred\": ").append(inferred)
                .append(", \"cached\": ").append(cached)
                .append(", \"errors\": ").append(errors).append(" },\n");
        json.append("  \"files\": [\n");
        boolean first = true;
        for (FileOutcome f : outcomes.values()) {
            if (!first) json.append(",\n");
            first = false;
            json.append("    { \"path\": \"").append(escape(f.path()))
                    .append("\", \"status\": \"").append(f.status()).append("\"");
            if (f.error() != null) {
                json.append(", \"error\": \"").append(escape(f.error())).append("\"");
            }
            json.append(" }");
        }
        json.append("\n  ]\n}\n");
        Files.writeString(path, json.toString());
    }

    private static String escape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    record FileOutcome(String path, String status, String error) {
    }
}
