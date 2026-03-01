package com.jml.inferrer.validation;

import java.util.ArrayList;
import java.util.List;

/**
 * Holds per-method verification results from OpenJML theorem proving.
 */
public class MethodVerificationResult {

    public enum Status {
        VERIFIED,
        FAILED,
        ERROR,
        TIMEOUT,
        SKIPPED
    }

    private final String className;
    private final String methodName;
    private final int lineNumber;
    private Status status;
    private final List<String> verifiedSpecs = new ArrayList<>();
    private final List<String> failedSpecs = new ArrayList<>();
    private final List<String> errorMessages = new ArrayList<>();
    private long verificationTimeMs;

    public MethodVerificationResult(String className, String methodName, int lineNumber) {
        this.className = className;
        this.methodName = methodName;
        this.lineNumber = lineNumber;
        this.status = Status.SKIPPED;
    }

    public String getClassName() {
        return className;
    }

    public String getMethodName() {
        return methodName;
    }

    public int getLineNumber() {
        return lineNumber;
    }

    public Status getStatus() {
        return status;
    }

    public void setStatus(Status status) {
        this.status = status;
    }

    public List<String> getVerifiedSpecs() {
        return verifiedSpecs;
    }

    public List<String> getFailedSpecs() {
        return failedSpecs;
    }

    public List<String> getErrorMessages() {
        return errorMessages;
    }

    public long getVerificationTimeMs() {
        return verificationTimeMs;
    }

    public void setVerificationTimeMs(long verificationTimeMs) {
        this.verificationTimeMs = verificationTimeMs;
    }

    public void addVerifiedSpec(String spec) {
        verifiedSpecs.add(spec);
    }

    public void addFailedSpec(String spec) {
        failedSpecs.add(spec);
    }

    public void addErrorMessage(String message) {
        errorMessages.add(message);
    }

    public String getFullMethodName() {
        return className + "." + methodName;
    }
}
