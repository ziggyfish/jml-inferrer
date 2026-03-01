package com.jml.inferrer.validation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;

/**
 * Generates console and JSON reports from a ValidationReport.
 * Follows the pattern established by MetricsCollector.
 */
public class ValidationReportGenerator {

    private static final Logger logger = LoggerFactory.getLogger(ValidationReportGenerator.class);

    /**
     * Prints a human-readable validation report to the console.
     */
    public void printReport(ValidationReport report) {
        System.out.println("\n" + "=".repeat(80));
        System.out.println("OPENJML THEOREM PROVER VALIDATION REPORT");
        System.out.println("=".repeat(80));

        // Summary statistics
        System.out.println("\n[SUMMARY]");
        System.out.printf("  Total Methods Checked:  %d\n", report.getTotalMethods());
        System.out.printf("  Verified (PASS):        %d\n", report.getVerifiedCount());
        System.out.printf("  Failed (FAIL):          %d\n", report.getFailedCount());
        System.out.printf("  Errors:                 %d\n", report.getErrorCount());
        System.out.printf("  Timeouts:               %d\n", report.getTimeoutCount());
        System.out.printf("  Skipped:                %d\n", report.getSkippedCount());
        System.out.printf("  Verification Rate:      %.1f%%\n", report.getVerificationRate());
        System.out.printf("  Total Time:             %.2f seconds\n",
                report.getTotalVerificationTimeMs() / 1000.0);

        // Per-spec-type stats
        Map<String, int[]> specStats = report.getPerSpecTypeStats();
        System.out.println("\n[PER-SPECIFICATION-TYPE RESULTS]");
        for (Map.Entry<String, int[]> entry : specStats.entrySet()) {
            int verified = entry.getValue()[0];
            int total = entry.getValue()[1];
            if (total > 0) {
                double rate = 100.0 * verified / total;
                System.out.printf("  %-20s: %d/%d verified (%.1f%%)\n",
                        entry.getKey(), verified, total, rate);
            }
        }

        // Per-file details
        System.out.println("\n[PER-FILE RESULTS]");
        for (ValidationReport.FileValidationResult fileResult : report.getFileResults()) {
            System.out.printf("\n  %s\n", fileResult.getFilePath());
            for (MethodVerificationResult method : fileResult.getMethodResults()) {
                String statusIcon = switch (method.getStatus()) {
                    case VERIFIED -> "PASS";
                    case FAILED -> "FAIL";
                    case ERROR -> "ERR ";
                    case TIMEOUT -> "TIME";
                    case SKIPPED -> "SKIP";
                };
                System.out.printf("    [%s] %s (line %d, %dms)\n",
                        statusIcon, method.getFullMethodName(),
                        method.getLineNumber(), method.getVerificationTimeMs());

                // Show failed specs
                for (String failed : method.getFailedSpecs()) {
                    System.out.printf("           FAIL: %s\n", failed);
                }
                // Show errors
                for (String error : method.getErrorMessages()) {
                    System.out.printf("           ERROR: %s\n", error);
                }
            }
        }

        System.out.println("\n" + "=".repeat(80));
        System.out.printf("VERIFICATION RATE: %.1f%% (%d/%d methods verified)\n",
                report.getVerificationRate(), report.getVerifiedCount(),
                report.getTotalMethods() - report.getSkippedCount());
        System.out.println("=".repeat(80) + "\n");
    }

    /**
     * Exports the validation report to a JSON file.
     */
    public void exportJSON(ValidationReport report, Path outputPath) throws IOException {
        try (FileWriter writer = new FileWriter(outputPath.toFile())) {
            writer.write("{\n");

            // Summary
            writer.write("  \"summary\": {\n");
            writer.write(String.format("    \"totalMethods\": %d,\n", report.getTotalMethods()));
            writer.write(String.format("    \"verified\": %d,\n", report.getVerifiedCount()));
            writer.write(String.format("    \"failed\": %d,\n", report.getFailedCount()));
            writer.write(String.format("    \"errors\": %d,\n", report.getErrorCount()));
            writer.write(String.format("    \"timeouts\": %d,\n", report.getTimeoutCount()));
            writer.write(String.format("    \"skipped\": %d,\n", report.getSkippedCount()));
            writer.write(String.format("    \"verificationRate\": %.2f,\n", report.getVerificationRate()));
            writer.write(String.format("    \"totalTimeMs\": %d\n", report.getTotalVerificationTimeMs()));
            writer.write("  },\n");

            // Per-spec-type stats
            writer.write("  \"perSpecType\": {\n");
            Map<String, int[]> specStats = report.getPerSpecTypeStats();
            int specCount = 0;
            for (Map.Entry<String, int[]> entry : specStats.entrySet()) {
                writer.write(String.format("    \"%s\": {\"verified\": %d, \"total\": %d}",
                        entry.getKey(), entry.getValue()[0], entry.getValue()[1]));
                if (++specCount < specStats.size()) writer.write(",");
                writer.write("\n");
            }
            writer.write("  },\n");

            // Per-file results
            writer.write("  \"files\": [\n");
            var fileResults = report.getFileResults();
            for (int f = 0; f < fileResults.size(); f++) {
                var fileResult = fileResults.get(f);
                writer.write("    {\n");
                writer.write(String.format("      \"path\": \"%s\",\n",
                        escapeJSON(fileResult.getFilePath())));
                writer.write("      \"methods\": [\n");

                var methods = fileResult.getMethodResults();
                for (int m = 0; m < methods.size(); m++) {
                    var method = methods.get(m);
                    writer.write("        {\n");
                    writer.write(String.format("          \"className\": \"%s\",\n",
                            escapeJSON(method.getClassName())));
                    writer.write(String.format("          \"methodName\": \"%s\",\n",
                            escapeJSON(method.getMethodName())));
                    writer.write(String.format("          \"lineNumber\": %d,\n",
                            method.getLineNumber()));
                    writer.write(String.format("          \"status\": \"%s\",\n",
                            method.getStatus().name()));
                    writer.write(String.format("          \"verificationTimeMs\": %d,\n",
                            method.getVerificationTimeMs()));

                    // Verified specs
                    writer.write("          \"verifiedSpecs\": [");
                    writeStringList(writer, method.getVerifiedSpecs());
                    writer.write("],\n");

                    // Failed specs
                    writer.write("          \"failedSpecs\": [");
                    writeStringList(writer, method.getFailedSpecs());
                    writer.write("],\n");

                    // Error messages
                    writer.write("          \"errorMessages\": [");
                    writeStringList(writer, method.getErrorMessages());
                    writer.write("]\n");

                    writer.write("        }");
                    if (m < methods.size() - 1) writer.write(",");
                    writer.write("\n");
                }

                writer.write("      ]\n");
                writer.write("    }");
                if (f < fileResults.size() - 1) writer.write(",");
                writer.write("\n");
            }
            writer.write("  ]\n");

            writer.write("}\n");
        }

        logger.info("Validation report exported to: {}", outputPath);
    }

    private void writeStringList(FileWriter writer, java.util.List<String> items) throws IOException {
        for (int i = 0; i < items.size(); i++) {
            writer.write(String.format("\"%s\"", escapeJSON(items.get(i))));
            if (i < items.size() - 1) writer.write(", ");
        }
    }

    private String escapeJSON(String value) {
        if (value == null) return "";
        return value.replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\t", "\\t");
    }
}
