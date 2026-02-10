package com.jml.inferrer.model;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents the inferred JML specifications for a method.
 */
public class MethodSpecification {

    private final List<String> preconditions;
    private final List<String> postconditions;
    private final List<String> loopInvariants;
    private final List<String> exceptionSpecifications;
    private final List<String> assignableClauses;

    // Method properties
    private boolean isPure = false;
    private boolean isObserver = false;
    private boolean isMutator = false;
    private boolean isThreadSafe = false;

    // Complexity
    private String timeComplexity;
    private String spaceComplexity;

    public MethodSpecification() {
        this.preconditions = new ArrayList<>();
        this.postconditions = new ArrayList<>();
        this.loopInvariants = new ArrayList<>();
        this.exceptionSpecifications = new ArrayList<>();
        this.assignableClauses = new ArrayList<>();
    }

    public void addPrecondition(String precondition) {
        this.preconditions.add(precondition);
    }

    public void addPostcondition(String postcondition) {
        this.postconditions.add(postcondition);
    }

    public void addLoopInvariant(String loopInvariant) {
        this.loopInvariants.add(loopInvariant);
    }

    public void addExceptionSpecification(String exceptionSpec) {
        this.exceptionSpecifications.add(exceptionSpec);
    }

    public void addAssignableClause(String assignable) {
        this.assignableClauses.add(assignable);
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
                || isPure || isObserver || isMutator || isThreadSafe
                || timeComplexity != null || spaceComplexity != null;
    }
}
