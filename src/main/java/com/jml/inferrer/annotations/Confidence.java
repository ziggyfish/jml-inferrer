package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Annotation indicating the confidence level of inferred specifications.
 *
 * This helps users understand how reliable the inferred specifications are:
 * - HIGH: Strong evidence from explicit code patterns (e.g., explicit null checks, validated inputs)
 * - MEDIUM: Moderate evidence from common patterns (e.g., standard operations, typical usage)
 * - LOW: Weak evidence, heuristic-based inference (e.g., naming conventions, type assumptions)
 *
 * Example usage:
 * <pre>
 * {@code
 * @Confidence(Confidence.Level.HIGH)
 * @Requires("input != null")
 * public void processInput(String input) { ... }
 * }
 * </pre>
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface Confidence {

    /**
     * The confidence level for the specifications on this method.
     *
     * @return The confidence level
     */
    Level value();

    /**
     * Confidence levels for inferred specifications.
     */
    enum Level {
        /**
         * High confidence: Strong code evidence for the specification.
         * Examples:
         * - Explicit null check with throw (if (x == null) throw new NPE())
         * - Explicit bounds validation
         * - Return statement directly returns checked value
         */
        HIGH,

        /**
         * Medium confidence: Reasonable evidence from common patterns.
         * Examples:
         * - Method call on parameter (implies non-null)
         * - Standard library usage patterns
         * - Loop bounds from for-loop structure
         */
        MEDIUM,

        /**
         * Low confidence: Heuristic-based or weak evidence.
         * Examples:
         * - Inference from naming conventions
         * - Type-based assumptions
         * - Complex control flow analysis
         */
        LOW
    }
}
