package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Third batch of regression tests for invalid JML specification inference.
 * Covers: stream operation natural language, switch statement natural language,
 * Integer.MAX_VALUE in invariants, type constraints, and ClassInvariantInferrer
 * raw toString() issues.
 */
@DisplayName("Invalid Inference Regression 3")
class InvalidInferenceRegressionTest3 extends InferrerTestBase {

    // =========================================================================
    // Stream operation specs must be valid JML, not natural language
    // =========================================================================

    @Test
    @DisplayName("Stream distinct() should generate \\forall uniqueness spec, not natural language")
    void streamDistinctGeneratesForall() {
        MethodSpecification spec = infer("""
            import java.util.List;
            import java.util.stream.Collectors;
            class T {
                List<String> unique(List<String> items) {
                    return items.stream().distinct().collect(Collectors.toList());
                }
            }
            """, "unique");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("contains no duplicates"),
                    "Postcondition must not contain natural language 'contains no duplicates': " + post);
        }
        // Should generate a \forall uniqueness postcondition
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\forall") && p.contains("equals")),
                "Expected \\forall uniqueness postcondition, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Stream sorted() should generate \\forall ordering spec, not natural language")
    void streamSortedGeneratesForall() {
        MethodSpecification spec = infer("""
            import java.util.List;
            import java.util.stream.Collectors;
            class T {
                List<Integer> sortList(List<Integer> items) {
                    return items.stream().sorted().collect(Collectors.toList());
                }
            }
            """, "sortList");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("is sorted"),
                    "Postcondition must not contain natural language 'is sorted': " + post);
        }
        // Should generate a \forall ordering postcondition
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\forall") && p.contains("compareTo")),
                "Expected \\forall ordering postcondition, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Stream filter nonNull should generate \\forall non-null spec, not natural language")
    void streamFilterNonNullGeneratesForall() {
        MethodSpecification spec = infer("""
            import java.util.List;
            import java.util.Objects;
            import java.util.stream.Collectors;
            class T {
                List<String> removeNulls(List<String> items) {
                    return items.stream().filter(Objects::nonNull).collect(Collectors.toList());
                }
            }
            """, "removeNulls");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("contains no null"),
                    "Postcondition must not contain natural language 'contains no null': " + post);
        }
        // Should generate a \forall non-null postcondition
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\forall") && p.contains("!= null")),
                "Expected \\forall non-null postcondition, got: " + spec.getPostconditions());
    }

    // =========================================================================
    // Switch statement specs must be valid JML, not natural language
    // =========================================================================

    @Test
    @DisplayName("Switch with default should generate \\result != null, not natural language")
    void switchExhaustiveGeneratesResultNotNull() {
        MethodSpecification spec = infer("""
            class T {
                String describe(int code) {
                    switch (code) {
                        case 1: return "one";
                        case 2: return "two";
                        default: return "other";
                    }
                }
            }
            """, "describe");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("is exhaustive"),
                    "Postcondition must not contain natural language 'is exhaustive': " + post);
        }
        // Should infer \result != null since all branches return non-null strings
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Switch expression should generate \\result != null, not natural language")
    void switchExpressionGeneratesResultNotNull() {
        MethodSpecification spec = infer("""
            class T {
                String describe(int code) {
                    return switch (code) {
                        case 1 -> "one";
                        case 2 -> "two";
                        default -> "other";
                    };
                }
            }
            """, "describe");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("always yields a value"),
                    "Postcondition must not contain natural language 'always yields a value': " + post);
        }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null, got: " + spec.getPostconditions());
    }

    // =========================================================================
    // Integer.MAX_VALUE must not appear as string literal in invariants
    // =========================================================================

    @Test
    @DisplayName("Accumulator loop should not use Integer.MAX_VALUE string in invariant")
    void noIntegerMaxValueString() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int[] arr) {
                    int total = 0;
                    for (int i = 0; i < arr.length; i++) {
                        total += arr[i];
                    }
                    return total;
                }
            }
            """, "sum");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("Integer.MAX_VALUE"),
                    "Loop invariant must not contain Java constant name 'Integer.MAX_VALUE': " + inv);
        }
    }

    // =========================================================================
    // Type constraints must be valid JML expressions
    // =========================================================================

    @Test
    @DisplayName("Generic type bound should generate instanceof precondition, not natural language")
    void genericTypeBoundGeneratesInstanceof() {
        MethodSpecification spec = infer("""
            class T {
                <E extends Number> E first(E[] arr) {
                    return arr[0];
                }
            }
            """, "first");
        // Should not generate "E extends Number" type constraint
        for (String constraint : spec.getTypeConstraints()) {
            assertFalse(constraint.contains("extends"),
                    "Type constraint must not contain natural language 'extends': " + constraint);
        }
        // Should generate instanceof precondition for the parameter
        assertTrue(spec.getPreconditions().stream()
                        .anyMatch(p -> p.contains("instanceof Number")),
                "Expected instanceof Number precondition, got: " + spec.getPreconditions());
    }

    // =========================================================================
    // ClassInvariantInferrer: final field init must not use raw toString()
    // =========================================================================

    @Test
    @DisplayName("Final field with new expression initializer should not use raw toString")
    void finalFieldNewExprNotRaw() {
        // ClassInvariantInferrer generates invariants for final fields, but init.toString()
        // could produce "new ArrayList()" which is not valid JML
        MethodSpecification spec = infer("""
            import java.util.ArrayList;
            import java.util.List;
            class T {
                final List<String> items = new ArrayList<>();
                void add(String item) {
                    items.add(item);
                }
            }
            """, "add");
        // This tests through the method inferrer, not ClassInvariantInferrer directly.
        // But we should ensure no method-level spec contains "new " from field init.
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("new "),
                    "Postcondition must not contain 'new' from field initializer: " + post);
        }
    }

    // =========================================================================
    // Switch case values should generate valid JML range postconditions
    // =========================================================================

    @Test
    @DisplayName("Switch with exhaustive cases should infer \\result != null for String return")
    void switchExhaustiveInfersResultNotNull() {
        MethodSpecification spec = infer("""
            class T {
                String describe(int code) {
                    switch (code) {
                        case 1: return "one";
                        case 2: return "two";
                        default: return "other";
                    }
                }
            }
            """, "describe");
        // Should infer \result != null since all branches return non-null strings
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null, got: " + spec.getPostconditions());
    }

    // =========================================================================
    // Stream specs that ARE valid JML should still be generated
    // =========================================================================

    @Test
    @DisplayName("Stream collect should still generate \\result != null")
    void streamCollectResultNotNull() {
        MethodSpecification spec = infer("""
            import java.util.List;
            import java.util.stream.Collectors;
            class T {
                List<String> filter(List<String> items) {
                    return items.stream().filter(s -> s != null).collect(Collectors.toList());
                }
            }
            """, "filter");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null for stream collect, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Stream count should still generate \\result >= 0")
    void streamCountResultNonNegative() {
        MethodSpecification spec = infer("""
            import java.util.List;
            class T {
                long countNonNull(List<String> items) {
                    return items.stream().filter(s -> s != null).count();
                }
            }
            """, "countNonNull");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "Expected \\result >= 0 for stream count, got: " + spec.getPostconditions());
    }
}
