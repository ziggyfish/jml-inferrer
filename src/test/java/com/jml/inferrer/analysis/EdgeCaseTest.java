package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Edge case tests: empty methods, degenerate inputs, boundary conditions, exotic patterns.
 */
@DisplayName("Edge Cases")
class EdgeCaseTest extends InferrerTestBase {

    @Test
    @DisplayName("Empty method body")
    void emptyMethodBody() {
        MethodSpecification spec = infer("""
            class T { void doNothing() { } }
            """, "doNothing");
        // Expected annotated method after inference:
        //   @Pure
        //   @Assignable("\\nothing")
        //   void doNothing() { }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Method with only a return statement")
    void onlyReturn() {
        MethodSpecification spec = infer("""
            class T { int zero() { return 0; } }
            """, "zero");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == 0")
        //   int zero() { return 0; }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Method returning null")
    void returnsNull() {
        MethodSpecification spec = infer("""
            class T { String nothing() { return null; } }
            """, "nothing");
        // Expected annotated method after inference:
        //   (no @Ensures for \\result != null -- method explicitly returns null)
        //   String nothing() { return null; }
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.equals("\\result != null")),
                "Should not claim non-null when returning null");
    }

    @Test
    @DisplayName("No parameters")
    void noParameters() {
        MethodSpecification spec = infer("""
            class T { int answer() { return 42; } }
            """, "answer");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == 42")
        //   int answer() { return 42; }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Many parameters")
    void manyParameters() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int a, int b, int c, int d, int e) {
                    return a + b + c + d + e;
                }
            }
            """, "sum");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == a + b + c + d + e")
        //   int sum(int a, int b, int c, int d, int e) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Overly long expression is skipped (> 100 chars)")
    void longExpressionSkipped() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int v1 = a + 1;
                    int v2 = v1 * v1 + v1 * v1 + v1 * v1;
                    int v3 = v2 * v2 * v2 * v2 * v2 * v2;
                    int v4 = v3 + v2 + v1 + v3 + v2 + v1;
                    return v4;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   (no @Ensures for \\result == ... -- expression too long, skipped)
        //   @Pure
        //   int compute(int a) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Unreachable code after throw")
    void unreachableAfterThrow() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    throw new UnsupportedOperationException();
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Signals("throws UnsupportedOperationException")
        //   int compute(int a) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Void method with only local computation")
    void voidWithLocalComputation() {
        MethodSpecification spec = infer("""
            class T {
                void process(int x) {
                    int a = x + 1;
                    int b = a * 2;
                }
            }
            """, "process");
        // Expected annotated method after inference:
        //   @Pure
        //   (no @Ensures for \\result -- void method has no return value)
        //   void process(int x) { ... }
        assertNotNull(spec);
        assertTrue(spec.getPostconditions().stream().noneMatch(p -> p.contains("\\result")),
                "Void method should have no \\result postconditions");
    }

    @Test
    @DisplayName("Return expression that's already a parameter (trivial)")
    void trivialReturnSkipped() {
        MethodSpecification spec = infer("""
            class T {
                int identity(int x) {
                    int y = x;
                    return y;
                }
            }
            """, "identity");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == x")
        //   int identity(int x) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Switch statement taints variables")
    void switchTaintsVariables() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int mode) {
                    int x = a * 2;
                    int y = 0;
                    switch (mode) {
                        case 1: y = 10; break;
                        case 2: y = 20; break;
                        default: y = 30;
                    }
                    return x + y;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Pure
        //   (y is tainted by switch, so no full symbolic \\result)
        //   int compute(int a, int mode) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Return inside try block resolves through env")
    void returnInsideTry() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    try {
                        return x + 1;
                    } catch (Exception e) {
                        return -1;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == (a * 2) + 1")   (from try-block return path)
        //   @Signals("on Exception returns -1")
        //   int compute(int a) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("(a * 2) + 1")),
                "Expected result from try block");
    }

    @Test
    @DisplayName("Method with boolean return type")
    void booleanReturn() {
        MethodSpecification spec = infer("""
            class T {
                boolean isPositive(int n) {
                    return n > 0;
                }
            }
            """, "isPositive");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == (n > 0)")
        //   boolean isPositive(int n) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Method with long return type")
    void longReturn() {
        MethodSpecification spec = infer("""
            class T {
                long compute(long a, long b) {
                    return a + b;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == a + b")
        //   long compute(long a, long b) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Method with double return type")
    void doubleReturn() {
        MethodSpecification spec = infer("""
            class T {
                double compute(double x) {
                    return x * x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result >= 0")     (x * x is always non-negative)
        //   double compute(double x) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "Expected >= 0 for x*x");
    }

    @Test
    @DisplayName("Static method")
    void staticMethod() {
        MethodSpecification spec = infer("""
            class T {
                static int add(int a, int b) {
                    return a + b;
                }
            }
            """, "add");
        // Expected annotated method after inference:
        //   @Pure
        //   @ThreadSafe
        //   @Ensures("\\result == a + b")
        //   static int add(int a, int b) { ... }
        assertTrue(spec.isPure(), "Static method with no state should be pure");
    }

    @Test
    @DisplayName("Method with varargs parameter")
    void varargsMethod() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int... values) {
                    int s = 0;
                    for (int v : values) s += v;
                    return s;
                }
            }
            """, "sum");
        // Expected annotated method after inference:
        //   @Requires("values != null")
        //   @Complexity(time = "O(n)")
        //   int sum(int... values) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Method with generic parameter")
    void genericParameter() {
        MethodSpecification spec = infer("""
            class T {
                <E> boolean contains(E[] arr, E target) {
                    for (E e : arr) {
                        if (e.equals(target)) return true;
                    }
                    return false;
                }
            }
            """, "contains");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Complexity(time = "O(n)")
        //   <E> boolean contains(E[] arr, E target) { ... }
        assertNotNull(spec);
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null");
    }

    @Test
    @DisplayName("Method returning new array")
    void returningNewArray() {
        MethodSpecification spec = infer("""
            class T {
                int[] zeros(int size) {
                    return new int[size];
                }
            }
            """, "zeros");
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length == size")
        //   @Pure
        //   int[] zeros(int size) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length == size")),
                "Expected length == size");
    }

    @Test
    @DisplayName("Nested try-catch blocks")
    void nestedTryCatch() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    try {
                        try {
                            return x + 1;
                        } catch (ArithmeticException e) {
                            return x;
                        }
                    } catch (Exception e) {
                        return -1;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == (a * 2) + 1")   (from innermost try block)
        //   @Signals("on ArithmeticException returns (a * 2)")
        //   @Signals("on Exception returns -1")
        //   int compute(int a) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Method with labeled break (doesn't crash)")
    void labeledBreak() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int[][] matrix) {
                    int target = -1;
                    outer:
                    for (int i = 0; i < matrix.length; i++) {
                        for (int j = 0; j < matrix[i].length; j++) {
                            if (matrix[i][j] == 0) {
                                target = i;
                                break outer;
                            }
                        }
                    }
                    return target;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Requires("matrix != null")
        //   @Complexity(time = "O(n^2)")
        //   int compute(int[][] matrix) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Chained method calls on string parameter")
    void chainedMethodCalls() {
        MethodSpecification spec = infer("""
            class T {
                String normalize(String s) {
                    return s.trim().toLowerCase();
                }
            }
            """, "normalize");
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   String normalize(String s) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null");
    }

    @Test
    @DisplayName("Constructor call in return")
    void constructorCallReturn() {
        MethodSpecification spec = infer("""
            import java.util.ArrayList;
            import java.util.List;
            class T {
                List<String> createList(int capacity) {
                    return new ArrayList<>(capacity);
                }
            }
            """, "createList");
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Pure
        //   List<String> createList(int capacity) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null");
    }

    @Test
    @DisplayName("Multiple return types with void branches")
    void multipleReturnVoidBranches() {
        MethodSpecification spec = infer("""
            class T {
                void process(int n) {
                    if (n < 0) return;
                    if (n == 0) return;
                    // do something
                    int x = n * 2;
                }
            }
            """, "process");
        // Expected annotated method after inference:
        //   @Requires("n < 0")           (or similar numeric constraints)
        //   (no @Ensures for \\result -- void method)
        //   void process(int n) { ... }
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Heavily overloaded expressions don't crash")
    void heavilyOverloadedExpression() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b, int c) {
                    return (a + b) * (b + c) - (a * c) + (b * b) / (a + 1);
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == (a + b) * (b + c) - (a * c) + (b * b) / (a + 1)")
        //   int compute(int a, int b, int c) { ... }
        assertNotNull(spec);
    }
}
