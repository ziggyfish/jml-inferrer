package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Provides pre-defined JML specifications for common Java standard library methods.
 * Used as a fallback when the SpecificationCache does not contain specs for called methods.
 */
public class StandardLibrarySpecs {

    private static final Map<String, MethodSpecification> SPECS = new HashMap<>();

    static {
        // String methods
        addSpec("String.length", 0,
                List.of(),
                List.of("\\result >= 0"));

        addSpec("String.isEmpty", 0,
                List.of(),
                List.of());

        addSpec("String.charAt", 1,
                List.of("index >= 0", "index < this.length()"),
                List.of());

        addSpec("String.substring", 1,
                List.of("beginIndex >= 0", "beginIndex <= this.length()"),
                List.of("\\result != null"));

        addSpec("String.substring", 2,
                List.of("beginIndex >= 0", "endIndex <= this.length()", "beginIndex <= endIndex"),
                List.of("\\result != null"));

        addSpec("String.indexOf", 1,
                List.of("str != null"),
                List.of("\\result >= -1"));

        addSpec("String.trim", 0,
                List.of(),
                List.of("\\result != null", "\\result.length() <= this.length()"));

        // Also register without class prefix for simple name lookups
        addSpec("length", 0,
                List.of(),
                List.of("\\result >= 0"));

        addSpec("charAt", 1,
                List.of("index >= 0", "index < this.length()"),
                List.of());

        addSpec("substring", 1,
                List.of("beginIndex >= 0", "beginIndex <= this.length()"),
                List.of("\\result != null"));

        addSpec("substring", 2,
                List.of("beginIndex >= 0", "endIndex <= this.length()", "beginIndex <= endIndex"),
                List.of("\\result != null"));

        addSpec("indexOf", 1,
                List.of("str != null"),
                List.of("\\result >= -1"));

        addSpec("trim", 0,
                List.of(),
                List.of("\\result != null", "\\result.length() <= this.length()"));

        // Math methods
        // Note: Math.abs(Integer.MIN_VALUE) returns Integer.MIN_VALUE (negative),
        // so we cannot guarantee \result >= 0 for integer types
        addSpec("Math.abs", 1,
                List.of(),
                List.of());

        addSpec("Math.max", 2,
                List.of(),
                List.of("\\result >= a", "\\result >= b"));

        addSpec("Math.min", 2,
                List.of(),
                List.of("\\result <= a", "\\result <= b"));

        addSpec("abs", 1,
                List.of(),
                List.of());

        addSpec("max", 2,
                List.of(),
                List.of("\\result >= a", "\\result >= b"));

        addSpec("min", 2,
                List.of(),
                List.of("\\result <= a", "\\result <= b"));

        // List methods
        addSpec("List.get", 1,
                List.of("index >= 0", "index < this.size()"),
                List.of());

        addSpec("List.size", 0,
                List.of(),
                List.of("\\result >= 0"));

        addSpec("List.isEmpty", 0,
                List.of(),
                List.of());

        addSpec("List.add", 1,
                List.of(),
                List.of("this.size() == \\old(this.size()) + 1"));

        addSpec("get", 1,
                List.of("index >= 0", "index < this.size()"),
                List.of());

        addSpec("size", 0,
                List.of(),
                List.of("\\result >= 0"));

        addSpec("add", 1,
                List.of(),
                List.of("this.size() == \\old(this.size()) + 1"));

        // Map methods
        addSpec("Map.size", 0,
                List.of(),
                List.of("\\result >= 0"));

        addSpec("Map.containsKey", 1,
                List.of(),
                List.of());

        // Collections utility methods
        addSpec("Collections.unmodifiableList", 1,
                List.of("list != null"),
                List.of("\\result != null"));

        addSpec("unmodifiableList", 1,
                List.of("list != null"),
                List.of("\\result != null"));

        // Objects utility methods
        addSpec("Objects.requireNonNull", 1,
                List.of("obj != null"),
                List.of("\\result != null", "\\result == obj"));

        addSpec("requireNonNull", 1,
                List.of("obj != null"),
                List.of("\\result != null", "\\result == obj"));

        // Arrays utility methods
        addSpec("Arrays.copyOf", 2,
                List.of("original != null", "newLength >= 0"),
                List.of("\\result != null", "\\result.length == newLength"));

        addSpec("copyOf", 2,
                List.of("original != null", "newLength >= 0"),
                List.of("\\result != null", "\\result.length == newLength"));

        // Integer methods
        addSpec("Integer.parseInt", 1,
                List.of("s != null"),
                List.of());

        addSpec("parseInt", 1,
                List.of("s != null"),
                List.of());

        addSpec("Integer.valueOf", 1,
                List.of(),
                List.of("\\result != null"));

        addSpec("valueOf", 1,
                List.of(),
                List.of("\\result != null"));
    }

    private static void addSpec(String methodKey, int argCount,
                                List<String> preconditions, List<String> postconditions) {
        MethodSpecification spec = new MethodSpecification();
        preconditions.forEach(spec::addPrecondition);
        postconditions.forEach(spec::addPostcondition);
        SPECS.put(methodKey + "(" + argCount + ")", spec);
        // Also store without arg count for simpler lookups
        SPECS.putIfAbsent(methodKey, spec);
    }

    /**
     * Gets preconditions for a standard library method.
     *
     * @param methodName The method name (e.g., "String.charAt" or just "charAt")
     * @param argCount   The number of arguments
     * @return List of precondition strings, or empty list if not found
     */
    public static List<String> getPreconditions(String methodName, int argCount) {
        // Try with arg count first for precise matching
        MethodSpecification spec = SPECS.get(methodName + "(" + argCount + ")");
        if (spec == null) {
            spec = SPECS.get(methodName);
        }
        if (spec != null && !spec.getPreconditions().isEmpty()) {
            return spec.getPreconditions();
        }
        return List.of();
    }

    /**
     * Gets postconditions for a standard library method.
     *
     * @param methodName The method name (e.g., "Math.abs" or just "abs")
     * @param argCount   The number of arguments
     * @return List of postcondition strings, or empty list if not found
     */
    public static List<String> getPostconditions(String methodName, int argCount) {
        // Try with arg count first for precise matching
        MethodSpecification spec = SPECS.get(methodName + "(" + argCount + ")");
        if (spec == null) {
            spec = SPECS.get(methodName);
        }
        if (spec != null && !spec.getPostconditions().isEmpty()) {
            return spec.getPostconditions();
        }
        return List.of();
    }

    /**
     * Gets the full specification for a standard library method.
     *
     * @param methodName The method name
     * @param argCount   The number of arguments
     * @return The MethodSpecification, or null if not found
     */
    public static MethodSpecification getSpec(String methodName, int argCount) {
        MethodSpecification spec = SPECS.get(methodName + "(" + argCount + ")");
        if (spec == null) {
            spec = SPECS.get(methodName);
        }
        return spec;
    }
}
