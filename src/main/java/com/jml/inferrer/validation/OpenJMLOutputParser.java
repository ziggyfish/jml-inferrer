package com.jml.inferrer.validation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Parses OpenJML text output into structured verification results.
 *
 * OpenJML output format examples:
 *   File.java:42: warning: The prover cannot establish an assertion (Precondition) in method foo
 *   File.java:42: error: cannot find symbol
 *   File.java:42: verified: method foo
 *   1 verification failure(s) out of 5 method(s)
 */
public class OpenJMLOutputParser {

    private static final Logger logger = LoggerFactory.getLogger(OpenJMLOutputParser.class);

    // Pattern: File.java:LINE: warning/verify: ... (AssertionType) in method METHODNAME
    private static final Pattern WARNING_PATTERN = Pattern.compile(
            "([^:]+):(\\d+):\\s*(?:warning|verify):\\s*(.+?)\\s*(?:\\(([^)]+)\\))?\\s*(?:in method\\s+(\\w+))?");

    // Pattern: File.java:LINE: error: ...
    private static final Pattern ERROR_PATTERN = Pattern.compile(
            "([^:]+):(\\d+):\\s*error:\\s*(.+)");

    // Pattern: verified: method METHODNAME or Verifying ... METHODNAME ... verified
    private static final Pattern VERIFIED_PATTERN = Pattern.compile(
            "(?:verified:\\s*method\\s+(\\w+))|(?:Verifying\\s+[^\\s]+\\.([\\w]+)\\s+.*verified)");

    // Pattern for assertion type extraction from warning messages
    private static final Pattern ASSERTION_TYPE_PATTERN = Pattern.compile(
            "\\(([^)]+)\\)");

    /**
     * Parses OpenJML output for a single file into method verification results.
     *
     * @param output   the raw OpenJML stdout/stderr output
     * @param fileName the source file name being verified
     * @param methods  list of method names with line numbers to match against
     * @return list of per-method verification results
     */
    public List<MethodVerificationResult> parse(String output, String fileName,
                                                 List<MethodInfo> methods) {
        if (output == null || output.isBlank()) {
            // No output typically means all verified or no methods to check
            return createDefaultResults(methods, MethodVerificationResult.Status.VERIFIED);
        }

        // Collect warnings and errors by line number / method name
        Map<String, List<String>> warningsByMethod = new HashMap<>();
        Map<String, List<String>> errorsByMethod = new HashMap<>();
        Set<String> verifiedMethods = new HashSet<>();

        String[] lines = output.split("\n");
        for (String line : lines) {
            line = line.trim();
            if (line.isEmpty()) continue;

            // Check for verification success
            Matcher verifiedMatcher = VERIFIED_PATTERN.matcher(line);
            if (verifiedMatcher.find()) {
                String methodName = verifiedMatcher.group(1) != null
                        ? verifiedMatcher.group(1) : verifiedMatcher.group(2);
                if (methodName != null) {
                    verifiedMethods.add(methodName);
                }
                continue;
            }

            // Check for warnings (verification failures)
            Matcher warningMatcher = WARNING_PATTERN.matcher(line);
            if (warningMatcher.find()) {
                int lineNum = Integer.parseInt(warningMatcher.group(2));
                String message = warningMatcher.group(3);
                String assertionType = warningMatcher.group(4);
                String methodName = warningMatcher.group(5);

                // Try to match to a method by name or line proximity
                String matchedMethod = resolveMethod(methodName, lineNum, methods);
                if (matchedMethod != null) {
                    String specDescription = assertionType != null
                            ? assertionType + ": " + message
                            : message;
                    warningsByMethod.computeIfAbsent(matchedMethod, k -> new ArrayList<>())
                            .add(specDescription);
                }
                continue;
            }

            // Check for errors (parse/type errors)
            Matcher errorMatcher = ERROR_PATTERN.matcher(line);
            if (errorMatcher.find()) {
                int lineNum = Integer.parseInt(errorMatcher.group(2));
                String message = errorMatcher.group(3);

                String matchedMethod = resolveMethodByLine(lineNum, methods);
                if (matchedMethod != null) {
                    errorsByMethod.computeIfAbsent(matchedMethod, k -> new ArrayList<>())
                            .add(message);
                }
            }
        }

        // Build results
        List<MethodVerificationResult> results = new ArrayList<>();
        for (MethodInfo method : methods) {
            MethodVerificationResult result = new MethodVerificationResult(
                    method.className(), method.methodName(), method.lineNumber());

            List<String> warnings = warningsByMethod.get(method.methodName());
            List<String> errors = errorsByMethod.get(method.methodName());

            if (errors != null && !errors.isEmpty()) {
                result.setStatus(MethodVerificationResult.Status.ERROR);
                errors.forEach(result::addErrorMessage);
            } else if (warnings != null && !warnings.isEmpty()) {
                result.setStatus(MethodVerificationResult.Status.FAILED);
                warnings.forEach(result::addFailedSpec);
                // Specs not mentioned in warnings are considered verified
                for (String spec : method.specs()) {
                    boolean failed = warnings.stream()
                            .anyMatch(w -> w.toLowerCase().contains(specTypeKeyword(spec)));
                    if (!failed) {
                        result.addVerifiedSpec(spec);
                    }
                }
            } else if (verifiedMethods.contains(method.methodName())
                    || (!warningsByMethod.containsKey(method.methodName())
                    && !errorsByMethod.containsKey(method.methodName()))) {
                result.setStatus(MethodVerificationResult.Status.VERIFIED);
                method.specs().forEach(result::addVerifiedSpec);
            }

            results.add(result);
        }

        return results;
    }

    /**
     * Resolves a method by name or line proximity.
     */
    private String resolveMethod(String methodName, int lineNum, List<MethodInfo> methods) {
        if (methodName != null) {
            for (MethodInfo m : methods) {
                if (m.methodName().equals(methodName)) {
                    return methodName;
                }
            }
        }
        return resolveMethodByLine(lineNum, methods);
    }

    /**
     * Finds the method whose line range contains the given line number.
     */
    private String resolveMethodByLine(int lineNum, List<MethodInfo> methods) {
        MethodInfo closest = null;
        int closestDist = Integer.MAX_VALUE;

        for (MethodInfo m : methods) {
            // Line is within method range or closest to start
            if (lineNum >= m.lineNumber()) {
                int dist = lineNum - m.lineNumber();
                if (dist < closestDist) {
                    closestDist = dist;
                    closest = m;
                }
            }
        }
        // Only match if within ~100 lines (reasonable method size)
        if (closest != null && closestDist < 100) {
            return closest.methodName();
        }
        return null;
    }

    private String specTypeKeyword(String spec) {
        if (spec.startsWith("requires")) return "precondition";
        if (spec.startsWith("ensures")) return "postcondition";
        if (spec.startsWith("loop_invariant")) return "loopinvariant";
        if (spec.startsWith("signals")) return "exceptionalposcondition";
        if (spec.startsWith("assignable")) return "assignable";
        return spec;
    }

    private List<MethodVerificationResult> createDefaultResults(
            List<MethodInfo> methods, MethodVerificationResult.Status status) {
        List<MethodVerificationResult> results = new ArrayList<>();
        for (MethodInfo m : methods) {
            MethodVerificationResult result = new MethodVerificationResult(
                    m.className(), m.methodName(), m.lineNumber());
            result.setStatus(status);
            if (status == MethodVerificationResult.Status.VERIFIED) {
                m.specs().forEach(result::addVerifiedSpec);
            }
            results.add(result);
        }
        return results;
    }

    /**
     * Information about a method being verified.
     */
    public record MethodInfo(String className, String methodName, int lineNumber, List<String> specs) {
    }
}
