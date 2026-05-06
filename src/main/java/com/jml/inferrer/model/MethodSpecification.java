package com.jml.inferrer.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Represents the inferred JML specifications for a method.
 */
public class MethodSpecification {

    /**
     * Confidence level for specifications.
     */
    public enum ConfidenceLevel {
        HIGH, MEDIUM, LOW
    }

    private final List<String> preconditions;
    private final List<String> postconditions;
    private final List<String> loopInvariants;
    private final Map<String, Integer> loopInvariantLine; // invariant -> source line of its loop (0 = legacy/first)
    // Tracks (loopLine, indexInLoopInvariants) per emission. Allows the same invariant
    // string to attach to multiple distinct loops without being deduplicated. The
    // legacy `loopInvariantLine` map only records the FIRST line per expr, which lost
    // the per-loop attribution when the same invariant fired for multiple loops.
    private final List<int[]> loopInvariantLines;
    // Per-expression set of loop lines, used for (expr, line) deduplication.
    private final Map<String, java.util.Set<Integer>> invariantLinesByExpr;
    // Termination measures (loop_decreases). Parallel to loopInvariants but
    // converted with the `loop_decreases` JML keyword instead of `loop_invariant`.
    // Per-entry source-line attribution mirrors loopInvariantLine.
    private final List<String> loopDecreases;
    private final Map<String, Integer> loopDecreasesLine;
    private final List<String> exceptionSpecifications;
    private final List<String> assignableClauses;

    // Confidence tracking for each specification
    private final Map<String, ConfidenceLevel> specificationConfidence;

    // Inherited specifications tracking (spec -> source class/interface)
    private final Map<String, String> inheritedPreconditions;
    private final Map<String, String> inheritedPostconditions;

    // Generic type constraints
    private final List<String> typeConstraints;

    // Method properties
    private boolean isPure = false;
    private boolean isObserver = false;
    private boolean isMutator = false;
    private boolean isThreadSafe = false;

    // RQ3: termination flag — true if the method is known to terminate on
    // every input. Default is true; the inferrer may set it to false when it
    // sees a recursive call without a `decreases` clause or a loop without a
    // `loop_decreases` heuristic. The CompositionalAnalyzer reads this flag
    // before propagating the callee's postcondition: a non-terminating
    // callee's postcondition is conditional on termination, so propagating
    // it unconditionally is unsound.
    private boolean terminates = true;

    // Overall confidence for the method
    private ConfidenceLevel overallConfidence = ConfidenceLevel.MEDIUM;

    // Complexity
    private String timeComplexity;
    private String spaceComplexity;

    public MethodSpecification() {
        this.preconditions = new ArrayList<>();
        this.postconditions = new ArrayList<>();
        this.loopInvariants = new ArrayList<>();
        this.loopInvariantLine = new HashMap<>();
        this.loopInvariantLines = new ArrayList<>();
        this.invariantLinesByExpr = new HashMap<>();
        this.loopDecreases = new ArrayList<>();
        this.loopDecreasesLine = new HashMap<>();
        this.exceptionSpecifications = new ArrayList<>();
        this.assignableClauses = new ArrayList<>();
        this.specificationConfidence = new HashMap<>();
        this.inheritedPreconditions = new HashMap<>();
        this.inheritedPostconditions = new HashMap<>();
        this.typeConstraints = new ArrayList<>();
    }

    /**
     * Adds a termination measure for the loop at {@code loopLine}. The expression
     * should be a non-negative integer that strictly decreases each iteration.
     * Emitted as `//@ loop_decreases <expr>;` by AnnotationToJMLConverter.
     * When the inferrer cannot prove this property, it is by design — OpenJML
     * will surface a `LoopDecreases` failure with a counter-example, which is
     * the intended bug-detection signal for non-terminating loops.
     */
    public void addLoopDecreases(String expr, int loopLine) {
        if (expr == null || expr.isBlank()) return;
        if (!this.loopDecreases.contains(expr)) {
            this.loopDecreases.add(expr);
            this.loopDecreasesLine.put(expr, loopLine);
        }
    }

    public List<String> getLoopDecreases() {
        return loopDecreases;
    }

    public int getLoopDecreasesLine(String expr) {
        return loopDecreasesLine.getOrDefault(expr, 0);
    }

    public void addPrecondition(String precondition) {
        if (com.jml.inferrer.analysis.AnalysisUtils.isTriviallyTrueClause(precondition)) return;
        if (!this.preconditions.contains(precondition)) {
            this.preconditions.add(precondition);
        }
    }

    public void addPrecondition(String precondition, ConfidenceLevel confidence) {
        if (com.jml.inferrer.analysis.AnalysisUtils.isTriviallyTrueClause(precondition)) return;
        if (!this.preconditions.contains(precondition)) {
            this.preconditions.add(precondition);
        }
        this.specificationConfidence.put(precondition, confidence);
    }

    public void addPostcondition(String postcondition) {
        if (!this.postconditions.contains(postcondition)) {
            this.postconditions.add(postcondition);
        }
    }

    public void addPostcondition(String postcondition, ConfidenceLevel confidence) {
        if (!this.postconditions.contains(postcondition)) {
            this.postconditions.add(postcondition);
        }
        this.specificationConfidence.put(postcondition, confidence);
    }

    public void addLoopInvariant(String loopInvariant) {
        addLoopInvariant(loopInvariant, 0);
    }

    public void addLoopInvariant(String loopInvariant, ConfidenceLevel confidence) {
        addLoopInvariant(loopInvariant, 0);
        this.specificationConfidence.put(loopInvariant, confidence);
    }

    /**
     * Adds a loop invariant tied to the loop at {@code loopLine} (the loop's source line).
     * When a method has multiple loops the converter uses this to place each invariant
     * directly above the right loop. {@code loopLine == 0} means "first loop" (legacy).
     */
    public void addLoopInvariant(String loopInvariant, int loopLine) {
        if (com.jml.inferrer.analysis.AnalysisUtils.isTriviallyTrueClause(loopInvariant)) return;
        // Per-loop dedup: the same invariant string can attach to multiple distinct
        // loops (e.g. `i >= 0` for each of three sequential while-loops in a merge).
        // Dedup key is (expr, loopLine), not just expr — otherwise we drop the second
        // loop's invariant and OpenJML can't discharge its index obligations.
        //
        // BUT: `loopLine == 0` is the legacy sentinel for "first loop / no
        // attribution". When the same invariant is added once with line=0 (from a
        // legacy analyzer path) and once with a real line (from an attributing
        // analyzer), we must NOT emit it twice — the spec-quality check rejects
        // duplicate spec lines. So treat line=0 as a wildcard: skip if any entry
        // already exists with the same expr, and skip new (expr, X) if (expr, 0)
        // already exists (the legacy entry already covers the first loop).
        Set<Integer> linesForExpr = this.invariantLinesByExpr
                .computeIfAbsent(loopInvariant, k -> new java.util.LinkedHashSet<>());
        if (linesForExpr.contains(loopLine)) return;
        if (loopLine == 0 && !linesForExpr.isEmpty()) return;
        if (loopLine != 0 && linesForExpr.contains(0)) return;
        linesForExpr.add(loopLine);
        this.loopInvariants.add(loopInvariant);
        this.loopInvariantLine.put(loopInvariant, loopLine);
        this.loopInvariantLines.add(new int[]{loopLine, this.loopInvariants.size() - 1});
    }

    public int getLoopInvariantLine(String loopInvariant) {
        return loopInvariantLine.getOrDefault(loopInvariant, 0);
    }

    /**
     * Returns the per-position line attribution for {@link #getLoopInvariants()}.
     * Index {@code i} of this list gives the loop ordinal for the invariant at
     * position {@code i} of {@code getLoopInvariants()}. Used by the JML emission
     * pipeline so duplicate invariant strings can attach to different loops
     * (otherwise the legacy {@code loopInvariantLine} map only remembers one line
     * per expression — losing the per-loop attribution for repeated invariants).
     */
    public int getLoopInvariantLineAt(int index) {
        if (index < 0 || index >= this.loopInvariantLines.size()) return 0;
        return this.loopInvariantLines.get(index)[0];
    }

    public void addExceptionSpecification(String exceptionSpec) {
        if (!this.exceptionSpecifications.contains(exceptionSpec)) {
            this.exceptionSpecifications.add(exceptionSpec);
        }
    }

    public void addExceptionSpecification(String exceptionSpec, ConfidenceLevel confidence) {
        if (!this.exceptionSpecifications.contains(exceptionSpec)) {
            this.exceptionSpecifications.add(exceptionSpec);
        }
        this.specificationConfidence.put(exceptionSpec, confidence);
    }

    public void addAssignableClause(String assignable) {
        if (!this.assignableClauses.contains(assignable)) {
            this.assignableClauses.add(assignable);
        }
    }

    /**
     * Adds an inherited precondition from a parent class or interface.
     */
    public void addInheritedPrecondition(String precondition, String source) {
        if (!this.preconditions.contains(precondition)) {
            this.preconditions.add(precondition);
        }
        this.inheritedPreconditions.put(precondition, source);
        this.specificationConfidence.put(precondition, ConfidenceLevel.HIGH);
    }

    /**
     * Adds an inherited postcondition from a parent class or interface.
     */
    public void addInheritedPostcondition(String postcondition, String source) {
        if (!this.postconditions.contains(postcondition)) {
            this.postconditions.add(postcondition);
        }
        this.inheritedPostconditions.put(postcondition, source);
        this.specificationConfidence.put(postcondition, ConfidenceLevel.HIGH);
    }

    /**
     * Adds a type constraint from generic analysis.
     */
    public void addTypeConstraint(String constraint) {
        this.typeConstraints.add(constraint);
    }

    /**
     * Gets the confidence level for a specific specification.
     */
    public ConfidenceLevel getConfidence(String specification) {
        return specificationConfidence.getOrDefault(specification, ConfidenceLevel.MEDIUM);
    }

    /**
     * Gets all specification confidence mappings.
     */
    public Map<String, ConfidenceLevel> getSpecificationConfidence() {
        return specificationConfidence;
    }

    /**
     * Gets inherited preconditions with their sources.
     */
    public Map<String, String> getInheritedPreconditions() {
        return inheritedPreconditions;
    }

    /**
     * Gets inherited postconditions with their sources.
     */
    public Map<String, String> getInheritedPostconditions() {
        return inheritedPostconditions;
    }

    /**
     * Gets type constraints from generic analysis.
     */
    public List<String> getTypeConstraints() {
        return typeConstraints;
    }

    /**
     * Gets the overall confidence level for this method.
     */
    public ConfidenceLevel getOverallConfidence() {
        return overallConfidence;
    }

    /**
     * Sets the overall confidence level for this method.
     */
    public void setOverallConfidence(ConfidenceLevel confidence) {
        this.overallConfidence = confidence;
    }

    /**
     * Calculates the overall confidence based on individual specification confidences.
     */
    public void calculateOverallConfidence() {
        if (specificationConfidence.isEmpty()) {
            this.overallConfidence = ConfidenceLevel.MEDIUM;
            return;
        }

        int highCount = 0;
        int lowCount = 0;

        for (ConfidenceLevel level : specificationConfidence.values()) {
            if (level == ConfidenceLevel.HIGH) highCount++;
            else if (level == ConfidenceLevel.LOW) lowCount++;
        }

        int total = specificationConfidence.size();
        if (highCount > total / 2) {
            this.overallConfidence = ConfidenceLevel.HIGH;
        } else if (lowCount > total / 2) {
            this.overallConfidence = ConfidenceLevel.LOW;
        } else {
            this.overallConfidence = ConfidenceLevel.MEDIUM;
        }
    }

    public List<String> getPreconditions() {
        return preconditions;
    }

    public List<String> getPostconditions() {
        return postconditions;
    }

    public List<String> getLoopInvariants() {
        return loopInvariants;
    }

    public List<String> getExceptionSpecifications() {
        return exceptionSpecifications;
    }

    public List<String> getAssignableClauses() {
        return assignableClauses;
    }

    public boolean isPure() {
        return isPure;
    }

    public void setPure(boolean pure) {
        isPure = pure;
    }

    public boolean isObserver() {
        return isObserver;
    }

    public void setObserver(boolean observer) {
        isObserver = observer;
    }

    public boolean isMutator() {
        return isMutator;
    }

    public void setMutator(boolean mutator) {
        isMutator = mutator;
    }

    /** RQ3: returns whether the method is known to terminate. Default true. */
    public boolean terminates() {
        return terminates;
    }

    /** RQ3: set the termination flag. Called by the inferrer when a recursive
     * call without a {@code decreases} clause or a loop without an evident
     * decreases heuristic is detected. */
    public void setTerminates(boolean terminates) {
        this.terminates = terminates;
    }

    public boolean isThreadSafe() {
        return isThreadSafe;
    }

    public void setThreadSafe(boolean threadSafe) {
        isThreadSafe = threadSafe;
    }

    public String getTimeComplexity() {
        return timeComplexity;
    }

    public void setTimeComplexity(String timeComplexity) {
        this.timeComplexity = timeComplexity;
    }

    public String getSpaceComplexity() {
        return spaceComplexity;
    }

    public void setSpaceComplexity(String spaceComplexity) {
        this.spaceComplexity = spaceComplexity;
    }

    public boolean hasSpecifications() {
        return !preconditions.isEmpty() || !postconditions.isEmpty() || !loopInvariants.isEmpty()
                || !exceptionSpecifications.isEmpty() || !assignableClauses.isEmpty()
                || !typeConstraints.isEmpty()
                || isPure || isObserver || isMutator || isThreadSafe
                || timeComplexity != null || spaceComplexity != null;
    }

    /**
     * Checks if the method has any inherited specifications.
     */
    public boolean hasInheritedSpecifications() {
        return !inheritedPreconditions.isEmpty() || !inheritedPostconditions.isEmpty();
    }
}
