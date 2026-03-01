package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for precondition inference: null checks, type constraints, validation, relationships.
 */
@DisplayName("Precondition Inference")
class PreconditionInferenceTest extends InferrerTestBase {

    // ---- Null checks ----

    @Test
    @DisplayName("Null check on reference parameter (method call)")
    void nullCheckMethodCall() {
        MethodSpecification spec = infer("""
            class T {
                int compute(String s) {
                    return s.length();
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("s != null")),
                "Expected s != null, got: " + spec.getPreconditions());
    }

    @Test
    @DisplayName("Null check on reference parameter (field access)")
    void nullCheckFieldAccess() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int[] arr) {
                    return arr.length;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null, got: " + spec.getPreconditions());
    }

    @Test
    @DisplayName("No null check for primitive parameter")
    void noPrimitiveNullCheck() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int x) {
                    return x + 1;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().noneMatch(p -> p.contains("x != null")),
                "Primitive should not have null check");
    }

    @Test
    @DisplayName("Multiple reference params each get null checks")
    void multipleReferenceParams() {
        MethodSpecification spec = infer("""
            class T {
                int compute(String a, String b) {
                    return a.length() + b.length();
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("a != null")),
                "Expected a != null");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("b != null")),
                "Expected b != null");
    }

    // ---- Array constraints ----

    @Test
    @DisplayName("Array parameter - null and length checks")
    void arrayPreconditions() {
        MethodSpecification spec = infer("""
            class T {
                int first(int[] arr) {
                    return arr[0];
                }
            }
            """, "first");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr.length > 0")),
                "Expected arr.length > 0");
    }

    @Test
    @DisplayName("Array specific index access requires sufficient length")
    void arraySpecificIndex() {
        MethodSpecification spec = infer("""
            class T {
                int third(int[] arr) {
                    return arr[2];
                }
            }
            """, "third");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr.length > 2")),
                "Expected arr.length > 2");
    }

    @Test
    @DisplayName("Array length comparison in conditional")
    void arrayLengthComparison() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int[] arr) {
                    if (arr.length > 5) {
                        return arr[0];
                    }
                    return 0;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr.length > 5")
                || p.contains("arr.length > 0")),
                "Expected array length precondition, got: " + spec.getPreconditions());
    }

    // ---- Numeric constraints ----

    @Test
    @DisplayName("Numeric comparison -> precondition")
    void numericComparison() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n > 0) {
                        return n * 2;
                    }
                    return 0;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n > 0")),
                "Expected n > 0");
    }

    @Test
    @DisplayName("Numeric >= comparison")
    void numericGreaterEqual() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n >= 10) {
                        return n;
                    }
                    return 0;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n >= 10")),
                "Expected n >= 10");
    }

    @Test
    @DisplayName("Numeric < comparison")
    void numericLessThan() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n < 100) {
                        return n;
                    }
                    return 100;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n < 100")),
                "Expected n < 100");
    }

    // ---- Early validation ----

    @Test
    @DisplayName("Early validation with throw -> inverted precondition")
    void earlyValidationThrow() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n < 0) {
                        throw new IllegalArgumentException("negative");
                    }
                    return n * 2;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n >= 0")),
                "Expected n >= 0 from early validation");
    }

    @Test
    @DisplayName("Early validation: if (n == 0) throw -> n != 0")
    void earlyValidationEquality() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n == 0) {
                        throw new ArithmeticException("zero");
                    }
                    return 10 / n;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n != 0")),
                "Expected n != 0");
    }

    @Test
    @DisplayName("Negated condition in early validation: if (!(condition)) throw")
    void negatedEarlyValidation() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (!(n > 0)) {
                        throw new IllegalArgumentException();
                    }
                    return n;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n > 0")),
                "Expected n > 0 from negated validation");
    }

    @Test
    @DisplayName("OR-based early validation: if (a < 0 || b < 0) throw")
    void orEarlyValidation() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    if (a < 0 || b < 0) {
                        throw new IllegalArgumentException();
                    }
                    return a + b;
                }
            }
            """, "compute");
        // Inverted OR: a >= 0 && b >= 0
        assertTrue(spec.getPreconditions().stream()
                .anyMatch(p -> p.contains("a >= 0") || p.contains("b >= 0")),
                "Expected a >= 0 and/or b >= 0, got: " + spec.getPreconditions());
    }

    // ---- String constraints ----

    @Test
    @DisplayName("String parameter - isEmpty check")
    void stringEmptyCheck() {
        MethodSpecification spec = infer("""
            class T {
                char firstChar(String s) {
                    if (s.isEmpty()) return '?';
                    return s.charAt(0);
                }
            }
            """, "firstChar");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("s != null")),
                "Expected s != null");
        assertTrue(spec.getPreconditions().stream()
                .anyMatch(p -> p.contains("isEmpty") || p.contains("length() > 0")),
                "Expected non-empty precondition");
    }

    @Test
    @DisplayName("String charAt implies non-empty")
    void stringCharAtImpliesNonEmpty() {
        MethodSpecification spec = infer("""
            class T {
                char getFirst(String s) {
                    return s.charAt(0);
                }
            }
            """, "getFirst");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("s.length() > 0")),
                "Expected s.length() > 0");
    }

    // ---- Collection constraints ----

    @Test
    @DisplayName("Collection parameter - get access implies non-empty")
    void collectionGetPrecondition() {
        MethodSpecification spec = infer("""
            import java.util.List;
            class T {
                Object first(List<String> list) {
                    return list.get(0);
                }
            }
            """, "first");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("list != null")),
                "Expected list != null");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("list.size() > 0")),
                "Expected list.size() > 0");
    }

    @Test
    @DisplayName("Collection parameter used with for-each -> null check")
    void collectionForEach() {
        MethodSpecification spec = infer("""
            import java.util.List;
            class T {
                int sum(List<Integer> items) {
                    int total = 0;
                    for (Integer i : items) {
                        total += i;
                    }
                    return total;
                }
            }
            """, "sum");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("items != null")),
                "Expected items != null for for-each usage");
    }

    // ---- Parameter relationships ----

    @Test
    @DisplayName("Parameter relationship: a < b")
    void parameterRelationship() {
        MethodSpecification spec = infer("""
            class T {
                int range(int low, int high) {
                    if (low < high) {
                        return high - low;
                    }
                    return 0;
                }
            }
            """, "range");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("low < high")),
                "Expected low < high");
    }

    @Test
    @DisplayName("Parameter relationship: a >= b")
    void parameterRelationshipGe() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int start, int end) {
                    if (start >= end) {
                        return 0;
                    }
                    return end - start;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("start >= end")),
                "Expected start >= end");
    }

    @Test
    @DisplayName("Multiple numeric checks on same param")
    void multipleNumericChecks() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n > 0) {
                        if (n < 100) {
                            return n;
                        }
                    }
                    return 0;
                }
            }
            """, "compute");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n > 0")),
                "Expected n > 0");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n < 100")),
                "Expected n < 100");
    }

    @Test
    @DisplayName("Comparable parameter generates type constraint")
    void comparableParam() {
        MethodSpecification spec = infer("""
            class T {
                int compare(Comparable a, Comparable b) {
                    return a.compareTo(b);
                }
            }
            """, "compare");
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("Comparable")),
                "Expected Comparable constraint");
    }

    @Test
    @DisplayName("No preconditions for parameterless method")
    void noParamMethod() {
        MethodSpecification spec = infer("""
            class T {
                int answer() {
                    return 42;
                }
            }
            """, "answer");
        assertTrue(spec.getPreconditions().isEmpty() ||
                spec.getPreconditions().stream().noneMatch(p -> p.contains("!= null")),
                "No null checks for parameterless method");
    }
}
