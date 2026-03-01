package com.jml.inferrer.validation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Aggregate validation report containing per-file results and summary statistics.
 */
public class ValidationReport {

    private final List<FileValidationResult> fileResults = new ArrayList<>();
    private long totalVerificationTimeMs;

    public void addFileResult(FileValidationResult result) {
        fileResults.add(result);
    }

    public List<FileValidationResult> getFileResults() {
        return fileResults;
    }

    public long getTotalVerificationTimeMs() {
        return totalVerificationTimeMs;
    }

    public void setTotalVerificationTimeMs(long totalVerificationTimeMs) {
        this.totalVerificationTimeMs = totalVerificationTimeMs;
    }

    // --- Aggregate statistics ---

    public int getTotalMethods() {
        return fileResults.stream()
                .mapToInt(f -> f.getMethodResults().size())
                .sum();
    }

    public int getVerifiedCount() {
        return countByStatus(MethodVerificationResult.Status.VERIFIED);
    }

    public int getFailedCount() {
        return countByStatus(MethodVerificationResult.Status.FAILED);
    }

    public int getErrorCount() {
        return countByStatus(MethodVerificationResult.Status.ERROR);
    }

    public int getTimeoutCount() {
        return countByStatus(MethodVerificationResult.Status.TIMEOUT);
    }

    public int getSkippedCount() {
        return countByStatus(MethodVerificationResult.Status.SKIPPED);
    }

    public double getVerificationRate() {
        int total = getTotalMethods() - getSkippedCount();
        return total > 0 ? (100.0 * getVerifiedCount() / total) : 0.0;
    }

    /**
     * Returns per-spec-type statistics: spec type -> [verified, total].
     */
    public Map<String, int[]> getPerSpecTypeStats() {
        Map<String, int[]> stats = new HashMap<>();
        stats.put("requires", new int[]{0, 0});
        stats.put("ensures", new int[]{0, 0});
        stats.put("loop_invariant", new int[]{0, 0});
        stats.put("signals", new int[]{0, 0});
        stats.put("assignable", new int[]{0, 0});

        for (FileValidationResult file : fileResults) {
            for (MethodVerificationResult method : file.getMethodResults()) {
                for (String spec : method.getVerifiedSpecs()) {
                    String type = extractSpecType(spec);
                    if (stats.containsKey(type)) {
                        stats.get(type)[0]++;
                        stats.get(type)[1]++;
                    }
                }
                for (String spec : method.getFailedSpecs()) {
                    String type = extractSpecType(spec);
                    if (stats.containsKey(type)) {
                        stats.get(type)[1]++;
                    }
                }
            }
        }
        return stats;
    }

    private String extractSpecType(String spec) {
        String trimmed = spec.trim().toLowerCase();
        if (trimmed.startsWith("requires")) return "requires";
        if (trimmed.startsWith("ensures")) return "ensures";
        if (trimmed.startsWith("loop_invariant")) return "loop_invariant";
        if (trimmed.startsWith("signals")) return "signals";
        if (trimmed.startsWith("assignable")) return "assignable";
        return "other";
    }

    private int countByStatus(MethodVerificationResult.Status status) {
        return fileResults.stream()
                .flatMap(f -> f.getMethodResults().stream())
                .filter(m -> m.getStatus() == status)
                .mapToInt(m -> 1)
                .sum();
    }

    /**
     * Per-file validation results.
     */
    public static class FileValidationResult {

        private final String filePath;
        private final List<MethodVerificationResult> methodResults = new ArrayList<>();

        public FileValidationResult(String filePath) {
            this.filePath = filePath;
        }

        public String getFilePath() {
            return filePath;
        }

        public List<MethodVerificationResult> getMethodResults() {
            return methodResults;
        }

        public void addMethodResult(MethodVerificationResult result) {
            methodResults.add(result);
        }
    }
}
