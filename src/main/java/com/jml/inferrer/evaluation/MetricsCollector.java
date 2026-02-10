package com.jml.inferrer.evaluation;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.time.Duration;
import java.time.Instant;
import java.util.*;

/**
 * Collects comprehensive metrics for evaluating JML specification inference quality.
 * Used for research paper evaluation section.
 */
public class MetricsCollector {

    private static final Logger logger = LoggerFactory.getLogger(MetricsCollector.class);

    // Timing metrics
    private Instant startTime;
    private Instant endTime;
    private long totalAnalysisTimeMs = 0;

    // File and code metrics
    private int totalFiles = 0;
    private int totalClasses = 0;
    private int totalMethods = 0;
    private int totalLinesOfCode = 0;

    // Coverage metrics
    private int classesWithAnnotations = 0;
    private int methodsWithAnnotations = 0;
    private int methodsWithPreconditions = 0;
    private int methodsWithPostconditions = 0;
    private int methodsWithLoopInvariants = 0;
    private int methodsWithFrameConditions = 0;
    private int methodsWithExceptionSpecs = 0;

    // Annotation type counts
    private final Map<String, Integer> annotationTypeCounts = new HashMap<>();

    // Specification strength distribution
    private int weakSpecs = 0;      // Trivial (e.g., "x != null" when never null)
    private int mediumSpecs = 0;    // Useful constraints
    private int strongSpecs = 0;    // Precise relationships with \old()

    // Method purity classification
    private int pureMethods = 0;
    private int observerMethods = 0;
    private int mutatorMethods = 0;

    // Complexity analysis
    private final Map<String, Integer> complexityDistribution = new HashMap<>();

    // Class-level metrics
    private int classesWithInvariants = 0;
    private int classesWithImmutable = 0;
    private int classesWithThreadSafe = 0;
    private int classesWithMustCall = 0;

    // Nullability metrics
    private int fieldsWithNullability = 0;
    private int nonNullAnnotations = 0;
    private int nullableAnnotations = 0;

    /**
     * Start timing the analysis.
     */
    public void startAnalysis() {
        this.startTime = Instant.now();
        logger.info("Metrics collection started");
    }

    /**
     * End timing the analysis.
     */
    public void endAnalysis() {
        this.endTime = Instant.now();
        this.totalAnalysisTimeMs = Duration.between(startTime, endTime).toMillis();
        logger.info("Metrics collection completed in {}ms", totalAnalysisTimeMs);
    }

    /**
     * Record metrics for a single class.
     */
    public void recordClass(ClassOrInterfaceDeclaration classDecl, int linesOfCode) {
        totalClasses++;
        totalLinesOfCode += linesOfCode;

        // Check for class-level annotations
        boolean hasAnnotations = !classDecl.getAnnotations().isEmpty();
        if (hasAnnotations) {
            classesWithAnnotations++;

            for (AnnotationExpr annotation : classDecl.getAnnotations()) {
                String annotationName = getSimpleAnnotationName(annotation);
                annotationTypeCounts.merge(annotationName, 1, Integer::sum);

                // Track specific class-level annotations
                switch (annotationName) {
                    case "Invariant" -> classesWithInvariants++;
                    case "Immutable" -> classesWithImmutable++;
                    case "ThreadSafe" -> classesWithThreadSafe++;
                    case "MustCall" -> classesWithMustCall++;
                }
            }
        }

        // Count field nullability annotations
        classDecl.getFields().forEach(field -> {
            field.getAnnotations().forEach(annotation -> {
                String name = getSimpleAnnotationName(annotation);
                if (name.equals("NonNull")) {
                    fieldsWithNullability++;
                    nonNullAnnotations++;
                } else if (name.equals("Nullable")) {
                    fieldsWithNullability++;
                    nullableAnnotations++;
                }
            });
        });
    }

    /**
     * Record metrics for a single method.
     */
    public void recordMethod(MethodDeclaration methodDecl) {
        totalMethods++;

        // Check if method has any annotations
        boolean hasAnnotations = !methodDecl.getAnnotations().isEmpty();
        if (hasAnnotations) {
            methodsWithAnnotations++;
        }

        // Count annotations by type
        boolean hasRequires = false;
        boolean hasEnsures = false;
        boolean hasLoopInvariant = false;
        boolean hasAssignable = false;
        boolean hasSignals = false;

        for (AnnotationExpr annotation : methodDecl.getAnnotations()) {
            String annotationName = getSimpleAnnotationName(annotation);
            annotationTypeCounts.merge(annotationName, 1, Integer::sum);

            // Track specific categories
            switch (annotationName) {
                case "Requires" -> hasRequires = true;
                case "Ensures" -> {
                    hasEnsures = true;
                    // Check if it's a strong spec with \old()
                    String value = getAnnotationValue(annotation);
                    if (value != null && value.contains("\\old(")) {
                        strongSpecs++;
                    } else if (value != null && value.contains("==")) {
                        mediumSpecs++;
                    } else {
                        weakSpecs++;
                    }
                }
                case "LoopInvariant" -> hasLoopInvariant = true;
                case "Assignable" -> hasAssignable = true;
                case "Signals" -> hasSignals = true;
                case "Pure" -> pureMethods++;
                case "Observer" -> observerMethods++;
                case "Mutator" -> mutatorMethods++;
                case "Complexity" -> recordComplexity(annotation);
            }
        }

        // Update coverage metrics
        if (hasRequires) methodsWithPreconditions++;
        if (hasEnsures) methodsWithPostconditions++;
        if (hasLoopInvariant) methodsWithLoopInvariants++;
        if (hasAssignable) methodsWithFrameConditions++;
        if (hasSignals) methodsWithExceptionSpecs++;
    }

    /**
     * Extract simple annotation name (without package).
     */
    private String getSimpleAnnotationName(AnnotationExpr annotation) {
        String fullName = annotation.getNameAsString();
        int lastDot = fullName.lastIndexOf('.');
        return lastDot >= 0 ? fullName.substring(lastDot + 1) : fullName;
    }

    /**
     * Extract annotation value for analysis.
     */
    private String getAnnotationValue(AnnotationExpr annotation) {
        if (annotation.isSingleMemberAnnotationExpr()) {
            return annotation.asSingleMemberAnnotationExpr()
                    .getMemberValue().toString();
        }
        return null;
    }

    /**
     * Record complexity annotation for distribution analysis.
     */
    private void recordComplexity(AnnotationExpr annotation) {
        if (annotation.isNormalAnnotationExpr()) {
            annotation.asNormalAnnotationExpr().getPairs().forEach(pair -> {
                if (pair.getNameAsString().equals("time")) {
                    String complexity = pair.getValue().toString().replace("\"", "");
                    complexityDistribution.merge(complexity, 1, Integer::sum);
                }
            });
        }
    }

    /**
     * Record a file being processed.
     */
    public void recordFile() {
        totalFiles++;
    }

    /**
     * Generate a comprehensive metrics report.
     */
    public MetricsReport generateReport() {
        MetricsReport report = new MetricsReport();

        // Timing
        report.totalAnalysisTimeMs = totalAnalysisTimeMs;
        report.averageTimePerFile = totalFiles > 0 ? (double) totalAnalysisTimeMs / totalFiles : 0;
        report.averageTimePerClass = totalClasses > 0 ? (double) totalAnalysisTimeMs / totalClasses : 0;

        // Code metrics
        report.totalFiles = totalFiles;
        report.totalClasses = totalClasses;
        report.totalMethods = totalMethods;
        report.totalLinesOfCode = totalLinesOfCode;

        // Coverage metrics (as percentages)
        report.classAnnotationCoverage = calculatePercentage(classesWithAnnotations, totalClasses);
        report.methodAnnotationCoverage = calculatePercentage(methodsWithAnnotations, totalMethods);
        report.preconditionCoverage = calculatePercentage(methodsWithPreconditions, totalMethods);
        report.postconditionCoverage = calculatePercentage(methodsWithPostconditions, totalMethods);
        report.loopInvariantCoverage = calculatePercentage(methodsWithLoopInvariants, totalMethods);
        report.frameConditionCoverage = calculatePercentage(methodsWithFrameConditions, totalMethods);

        // Annotation statistics
        report.totalAnnotations = annotationTypeCounts.values().stream().mapToInt(Integer::intValue).sum();
        report.annotationTypeCounts = new HashMap<>(annotationTypeCounts);

        // Specification strength
        report.weakSpecs = weakSpecs;
        report.mediumSpecs = mediumSpecs;
        report.strongSpecs = strongSpecs;

        // Method purity
        report.pureMethods = pureMethods;
        report.observerMethods = observerMethods;
        report.mutatorMethods = mutatorMethods;

        // Complexity distribution
        report.complexityDistribution = new HashMap<>(complexityDistribution);

        // Class-level metrics
        report.classesWithInvariants = classesWithInvariants;
        report.classesWithImmutable = classesWithImmutable;
        report.classesWithThreadSafe = classesWithThreadSafe;
        report.classesWithMustCall = classesWithMustCall;

        // Nullability
        report.nonNullAnnotations = nonNullAnnotations;
        report.nullableAnnotations = nullableAnnotations;

        return report;
    }

    /**
     * Export metrics to JSON for further analysis.
     */
    public void exportJSON(Path outputPath) throws IOException {
        MetricsReport report = generateReport();

        try (FileWriter writer = new FileWriter(outputPath.toFile())) {
            writer.write("{\n");
            writer.write("  \"timing\": {\n");
            writer.write(String.format("    \"totalAnalysisTimeMs\": %d,\n", report.totalAnalysisTimeMs));
            writer.write(String.format("    \"averageTimePerFile\": %.2f,\n", report.averageTimePerFile));
            writer.write(String.format("    \"averageTimePerClass\": %.2f\n", report.averageTimePerClass));
            writer.write("  },\n");

            writer.write("  \"codeMetrics\": {\n");
            writer.write(String.format("    \"totalFiles\": %d,\n", report.totalFiles));
            writer.write(String.format("    \"totalClasses\": %d,\n", report.totalClasses));
            writer.write(String.format("    \"totalMethods\": %d,\n", report.totalMethods));
            writer.write(String.format("    \"totalLinesOfCode\": %d\n", report.totalLinesOfCode));
            writer.write("  },\n");

            writer.write("  \"coverage\": {\n");
            writer.write(String.format("    \"classAnnotationCoverage\": %.2f,\n", report.classAnnotationCoverage));
            writer.write(String.format("    \"methodAnnotationCoverage\": %.2f,\n", report.methodAnnotationCoverage));
            writer.write(String.format("    \"preconditionCoverage\": %.2f,\n", report.preconditionCoverage));
            writer.write(String.format("    \"postconditionCoverage\": %.2f,\n", report.postconditionCoverage));
            writer.write(String.format("    \"loopInvariantCoverage\": %.2f,\n", report.loopInvariantCoverage));
            writer.write(String.format("    \"frameConditionCoverage\": %.2f\n", report.frameConditionCoverage));
            writer.write("  },\n");

            writer.write("  \"annotationCounts\": {\n");
            int count = 0;
            for (Map.Entry<String, Integer> entry : report.annotationTypeCounts.entrySet()) {
                writer.write(String.format("    \"%s\": %d", entry.getKey(), entry.getValue()));
                if (++count < report.annotationTypeCounts.size()) writer.write(",");
                writer.write("\n");
            }
            writer.write("  },\n");

            writer.write("  \"specificationStrength\": {\n");
            writer.write(String.format("    \"weak\": %d,\n", report.weakSpecs));
            writer.write(String.format("    \"medium\": %d,\n", report.mediumSpecs));
            writer.write(String.format("    \"strong\": %d\n", report.strongSpecs));
            writer.write("  },\n");

            writer.write("  \"methodPurity\": {\n");
            writer.write(String.format("    \"pure\": %d,\n", report.pureMethods));
            writer.write(String.format("    \"observer\": %d,\n", report.observerMethods));
            writer.write(String.format("    \"mutator\": %d\n", report.mutatorMethods));
            writer.write("  },\n");

            writer.write("  \"complexityDistribution\": {\n");
            count = 0;
            for (Map.Entry<String, Integer> entry : report.complexityDistribution.entrySet()) {
                writer.write(String.format("    \"%s\": %d", entry.getKey(), entry.getValue()));
                if (++count < report.complexityDistribution.size()) writer.write(",");
                writer.write("\n");
            }
            writer.write("  },\n");

            writer.write("  \"classLevelMetrics\": {\n");
            writer.write(String.format("    \"classesWithInvariants\": %d,\n", report.classesWithInvariants));
            writer.write(String.format("    \"classesWithImmutable\": %d,\n", report.classesWithImmutable));
            writer.write(String.format("    \"classesWithThreadSafe\": %d,\n", report.classesWithThreadSafe));
            writer.write(String.format("    \"classesWithMustCall\": %d\n", report.classesWithMustCall));
            writer.write("  },\n");

            writer.write("  \"nullability\": {\n");
            writer.write(String.format("    \"nonNullAnnotations\": %d,\n", report.nonNullAnnotations));
            writer.write(String.format("    \"nullableAnnotations\": %d\n", report.nullableAnnotations));
            writer.write("  }\n");

            writer.write("}\n");
        }

        logger.info("Metrics exported to: {}", outputPath);
    }

    /**
     * Print a human-readable report to console.
     */
    public void printReport() {
        MetricsReport report = generateReport();

        System.out.println("\n" + "=".repeat(80));
        System.out.println("JML SPECIFICATION INFERENCE - COMPREHENSIVE METRICS REPORT");
        System.out.println("=".repeat(80));

        System.out.println("\n[TIMING METRICS]");
        System.out.printf("  Total Analysis Time: %.2f seconds\n", report.totalAnalysisTimeMs / 1000.0);
        System.out.printf("  Average Time per File: %.2f ms\n", report.averageTimePerFile);
        System.out.printf("  Average Time per Class: %.2f ms\n", report.averageTimePerClass);

        System.out.println("\n[CODE METRICS]");
        System.out.printf("  Total Files Analyzed: %d\n", report.totalFiles);
        System.out.printf("  Total Classes: %d\n", report.totalClasses);
        System.out.printf("  Total Methods: %d\n", report.totalMethods);
        System.out.printf("  Total Lines of Code: %d\n", report.totalLinesOfCode);

        System.out.println("\n[ANNOTATION COVERAGE]");
        System.out.printf("  Classes with Annotations: %.1f%% (%d/%d)\n",
                report.classAnnotationCoverage, classesWithAnnotations, totalClasses);
        System.out.printf("  Methods with Annotations: %.1f%% (%d/%d)\n",
                report.methodAnnotationCoverage, methodsWithAnnotations, totalMethods);
        System.out.printf("  Methods with Preconditions: %.1f%% (%d/%d)\n",
                report.preconditionCoverage, methodsWithPreconditions, totalMethods);
        System.out.printf("  Methods with Postconditions: %.1f%% (%d/%d)\n",
                report.postconditionCoverage, methodsWithPostconditions, totalMethods);
        System.out.printf("  Methods with Loop Invariants: %.1f%% (%d/%d)\n",
                report.loopInvariantCoverage, methodsWithLoopInvariants, totalMethods);
        System.out.printf("  Methods with Frame Conditions: %.1f%% (%d/%d)\n",
                report.frameConditionCoverage, methodsWithFrameConditions, totalMethods);

        System.out.println("\n[ANNOTATION TYPE DISTRIBUTION]");
        report.annotationTypeCounts.entrySet().stream()
                .sorted(Map.Entry.<String, Integer>comparingByValue().reversed())
                .forEach(entry -> System.out.printf("  @%-20s: %,6d\n", entry.getKey(), entry.getValue()));

        System.out.println("\n[SPECIFICATION STRENGTH]");
        int totalSpecs = report.weakSpecs + report.mediumSpecs + report.strongSpecs;
        if (totalSpecs > 0) {
            System.out.printf("  Weak Specs:   %,6d (%.1f%%)\n", report.weakSpecs,
                    calculatePercentage(report.weakSpecs, totalSpecs));
            System.out.printf("  Medium Specs: %,6d (%.1f%%)\n", report.mediumSpecs,
                    calculatePercentage(report.mediumSpecs, totalSpecs));
            System.out.printf("  Strong Specs: %,6d (%.1f%%) - with \\old()\n", report.strongSpecs,
                    calculatePercentage(report.strongSpecs, totalSpecs));
        }

        System.out.println("\n[METHOD PURITY CLASSIFICATION]");
        System.out.printf("  Pure Methods:     %,6d\n", report.pureMethods);
        System.out.printf("  Observer Methods: %,6d\n", report.observerMethods);
        System.out.printf("  Mutator Methods:  %,6d\n", report.mutatorMethods);

        System.out.println("\n[COMPLEXITY ANALYSIS]");
        report.complexityDistribution.entrySet().stream()
                .sorted(Map.Entry.comparingByKey())
                .forEach(entry -> System.out.printf("  %-15s: %,6d methods\n", entry.getKey(), entry.getValue()));

        System.out.println("\n[CLASS-LEVEL SPECIFICATIONS]");
        System.out.printf("  Classes with Invariants:  %,6d (%.1f%%)\n",
                report.classesWithInvariants, calculatePercentage(report.classesWithInvariants, totalClasses));
        System.out.printf("  Classes with @Immutable:  %,6d (%.1f%%)\n",
                report.classesWithImmutable, calculatePercentage(report.classesWithImmutable, totalClasses));
        System.out.printf("  Classes with @ThreadSafe: %,6d (%.1f%%)\n",
                report.classesWithThreadSafe, calculatePercentage(report.classesWithThreadSafe, totalClasses));
        System.out.printf("  Classes with @MustCall:   %,6d (%.1f%%)\n",
                report.classesWithMustCall, calculatePercentage(report.classesWithMustCall, totalClasses));

        System.out.println("\n[NULLABILITY ANALYSIS]");
        System.out.printf("  @NonNull Annotations:  %,6d\n", report.nonNullAnnotations);
        System.out.printf("  @Nullable Annotations: %,6d\n", report.nullableAnnotations);

        System.out.println("\n" + "=".repeat(80));
        System.out.printf("TOTAL ANNOTATIONS GENERATED: %,d\n", report.totalAnnotations);
        System.out.println("=".repeat(80) + "\n");
    }

    private double calculatePercentage(int part, int total) {
        return total > 0 ? (100.0 * part / total) : 0.0;
    }

    /**
     * Data class holding all metrics for reporting.
     */
    public static class MetricsReport {
        // Timing
        public long totalAnalysisTimeMs;
        public double averageTimePerFile;
        public double averageTimePerClass;

        // Code metrics
        public int totalFiles;
        public int totalClasses;
        public int totalMethods;
        public int totalLinesOfCode;

        // Coverage (percentages)
        public double classAnnotationCoverage;
        public double methodAnnotationCoverage;
        public double preconditionCoverage;
        public double postconditionCoverage;
        public double loopInvariantCoverage;
        public double frameConditionCoverage;

        // Annotation statistics
        public int totalAnnotations;
        public Map<String, Integer> annotationTypeCounts;

        // Specification strength
        public int weakSpecs;
        public int mediumSpecs;
        public int strongSpecs;

        // Method purity
        public int pureMethods;
        public int observerMethods;
        public int mutatorMethods;

        // Complexity
        public Map<String, Integer> complexityDistribution;

        // Class-level
        public int classesWithInvariants;
        public int classesWithImmutable;
        public int classesWithThreadSafe;
        public int classesWithMustCall;

        // Nullability
        public int nonNullAnnotations;
        public int nullableAnnotations;
    }
}
