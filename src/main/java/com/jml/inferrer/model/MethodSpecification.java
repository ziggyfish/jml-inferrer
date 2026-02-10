package com.jml.inferrer.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

    // Overall confidence for the method
    private ConfidenceLevel overallConfidence = ConfidenceLevel.MEDIUM;

    // Complexity
    private String timeComplexity;
    private String spaceComplexity;

    public MethodSpecification() {
        this.preconditions = new ArrayList<>();
        this.postconditions = new ArrayList<>();
        this.loopInvariants = new ArrayList<>();
        this.exceptionSpecifications = new ArrayList<>();
        this.assignableClauses = new ArrayList<>();
        this.specificationConfidence = new HashMap<>();
        this.inheritedPreconditions = new HashMap<>();
        this.inheritedPostconditions = new HashMap<>();
        this.typeConstraints = new ArrayList<>();
    }

    public void addPrecondition(String precondition) {
        this.preconditions.add(precondition);
    }

    public void addPrecondition(String precondition, ConfidenceLevel confidence) {
        this.preconditions.add(precondition);
        this.specificationConfidence.put(precondition, confidence);
    }

    public void addPostcondition(String postcondition) {
        this.postconditions.add(postcondition);
    }

    public void addPostcondition(String postcondition, ConfidenceLevel confidence) {
        this.postconditions.add(postcondition);
        this.specificationConfidence.put(postcondition, confidence);
    }

    public void addLoopInvariant(String loopInvariant) {
        this.loopInvariants.add(loopInvariant);
    }

    public void addLoopInvariant(String loopInvariant, ConfidenceLevel confidence) {
        this.loopInvariants.add(loopInvariant);
        this.specificationConfidence.put(loopInvariant, confidence);
    }

    public void addExceptionSpecification(String exceptionSpec) {
        this.exceptionSpecifications.add(exceptionSpec);
    }

    public void addExceptionSpecification(String exceptionSpec, ConfidenceLevel confidence) {
        this.exceptionSpecifications.add(exceptionSpec);
        this.specificationConfidence.put(exceptionSpec, confidence);
    }

    public void addAssignableClause(String assignable) {
        this.assignableClauses.add(assignable);
    }

    /**
     * Adds an inherited precondition from a parent class or interface.
     */
    public void addInheritedPrecondition(String precondition, String source) {
        this.preconditions.add(precondition);
        this.inheritedPreconditions.put(precondition, source);
        this.specificationConfidence.put(precondition, ConfidenceLevel.HIGH);
    }

    /**
     * Adds an inherited postcondition from a parent class or interface.
     */
    public void addInheritedPostcondition(String postcondition, String source) {
        this.postconditions.add(postcondition);
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
