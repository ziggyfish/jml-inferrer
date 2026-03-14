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

    // =========================================================================
    // String postconditions must use .equals(), not == (Regression 4)
    // =========================================================================

    @Test
    @DisplayName("String return from if/else should use .equals(), not ==")
    void stringReturnUsesEquals() {
        MethodSpecification spec = infer("""
            class T {
                public String getValue(String a, String b) {
                    if (a.isEmpty()) {
                        return "b";
                    } else {
                        return "a";
                    }
                }
            }
            """, "getValue");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("\\result == \""),
                    "Postcondition must use .equals() for strings, not ==: " + post);
        }
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\result.equals(")),
                "Expected .equals() in postcondition, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard isEmpty() in if-condition should not generate precondition")
    void guardIsEmptyNoPrecondition() {
        MethodSpecification spec = infer("""
            class T {
                public String getValue(String a, String b) {
                    if (a.isEmpty()) {
                        return "b";
                    } else {
                        return "a";
                    }
                }
            }
            """, "getValue");
        assertFalse(spec.getPreconditions().stream()
                        .anyMatch(p -> p.contains("!a.isEmpty()")),
                "Should not generate !a.isEmpty() precondition for guard condition, got: " + spec.getPreconditions());
    }

    // =========================================================================
    // Compound assignment accumulation (Regression 4)
    // =========================================================================

    @Test
    @DisplayName("Multiple compound assignments to same field should accumulate")
    void compoundAssignmentAccumulates() {
        MethodSpecification spec = infer("""
            class T {
                int c;
                public int getValue(int a) {
                    a = a * a;
                    c += 3;
                    c += 3;
                    int b = a + c;
                    b = b * b;
                    return b;
                }
            }
            """, "getValue");
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\old(this.c) + 6")),
                "Expected \\old(this.c) + 6 for accumulated compound assignment, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Field in symbolic expression should use \\old when modified")
    void fieldUsesOldInSymbolicExpr() {
        MethodSpecification spec = infer("""
            class T {
                int c;
                public int getValue(int a) {
                    a = a * a;
                    c += 3;
                    c += 3;
                    int b = a + c;
                    b = b * b;
                    return b;
                }
            }
            """, "getValue");
        for (String post : spec.getPostconditions()) {
            if (post.contains("\\result ==") && post.contains("a * a")) {
                assertTrue(post.contains("\\old(this.c)"),
                        "Symbolic expression should use \\old(this.c) for modified field: " + post);
            }
        }
    }

    @Test
    @DisplayName("Self-multiplication should correctly parenthesize")
    void selfMultiplicationParenthesized() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int x) {
                    int a = x + 1;
                    a = a * a;
                    return a;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("((x + 1) * (x + 1))")),
                "Expected ((x + 1) * (x + 1)) for self-multiplication, got: " + spec.getPostconditions());
    }

    // =========================================================================
    // Division results must not have spurious positive bounds (Regression 5)
    // =========================================================================

    @Test
    @DisplayName("Integer division should not infer \\result >= 1")
    void divisionNoSpuriousPositiveBound() {
        MethodSpecification spec = infer("""
            class T {
                int average(int a, int b) {
                    return (a + b) / 2;
                }
            }
            """, "average");
        assertFalse(spec.getPostconditions().stream()
                        .anyMatch(p -> p.equals("\\result >= 1") || p.equals("\\result > 0")),
                "Division result should not have spurious positive bound, got: " + spec.getPostconditions());
    }
}
