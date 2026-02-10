package com.jml.inferrer.model;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents the inferred specifications for a class.
 */
public class ClassSpecification {

    private final List<String> invariants;
    private boolean isImmutable = false;
    private boolean isThreadSafe = false;
    private final List<String> mustCallMethods;

    public ClassSpecification() {
        this.invariants = new ArrayList<>();
        this.mustCallMethods = new ArrayList<>();
    }

    public void addInvariant(String invariant) {
        this.invariants.add(invariant);
    }

    public List<String> getInvariants() {
        return invariants;
    }

    public boolean isImmutable() {
        return isImmutable;
    }

    public void setImmutable(boolean immutable) {
        isImmutable = immutable;
    }

    public boolean isThreadSafe() {
        return isThreadSafe;
    }

    public void setThreadSafe(boolean threadSafe) {
        isThreadSafe = threadSafe;
    }

    public void addMustCallMethod(String methodName) {
        this.mustCallMethods.add(methodName);
    }

    public List<String> getMustCallMethods() {
        return mustCallMethods;
    }

    public boolean hasSpecifications() {
        return !invariants.isEmpty() || isImmutable || isThreadSafe || !mustCallMethods.isEmpty();
    }
}
