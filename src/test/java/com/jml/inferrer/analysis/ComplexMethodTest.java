package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests with complex, real-world-style methods that exercise multiple inference capabilities.
 */
@DisplayName("Complex Real-World Methods")
class ComplexMethodTest extends InferrerTestBase {

    @Test
    @DisplayName("Binary search - recursion with divide by 2")
    void binarySearch() {
        MethodSpecification spec = infer("""
            class T {
                int binarySearch(int[] arr, int target, int low, int high) {
                    if (low > high) return -1;
                    int mid = (low + high) / 2;
                    if (arr[mid] == target) return mid;
                    if (arr[mid] < target) return binarySearch(arr, target, mid + 1, high);
                    return binarySearch(arr, target, low, mid - 1);
                }
            }
            """, "binarySearch");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Complexity(time = "O(n log n)")
        //   int binarySearch(int[] arr, int target, int low, int high) { ... }
        assertEquals("O(n log n)", spec.getTimeComplexity());
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null");
    }

    @Test
    @DisplayName("Fibonacci - exponential recursion")
    void fibonacci() {
        MethodSpecification spec = infer("""
            class T {
                int fib(int n) {
                    if (n <= 0) return 0;
                    if (n == 1) return 1;
                    return fib(n - 1) + fib(n - 2);
                }
            }
            """, "fib");
        // Expected annotated method after inference:
        //   @Complexity(time = "O(2^n)")
        //   @Ensures("\\result >= 0")
        //   int fib(int n) { ... }
        assertEquals("O(2^n)", spec.getTimeComplexity());
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "Expected non-negative result");
    }

    @Test
    @DisplayName("Matrix multiply - O(n^3)")
    void matrixMultiply() {
        MethodSpecification spec = infer("""
            class T {
                int[][] multiply(int[][] a, int[][] b) {
                    int n = a.length;
                    int[][] result = new int[n][n];
                    for (int i = 0; i < n; i++)
                        for (int j = 0; j < n; j++)
                            for (int k = 0; k < n; k++)
                                result[i][j] += a[i][k] * b[k][j];
                    return result;
                }
            }
            """, "multiply");
        // Expected annotated method after inference:
        //   @Requires("a != null")
        //   @Requires("b != null")
        //   @Complexity(time = "O(n^3)")
        //   @Ensures("\\result != null")
        //   int[][] multiply(int[][] a, int[][] b) { ... }
        assertEquals("O(n^3)", spec.getTimeComplexity());
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null");
    }

    @Test
    @DisplayName("Linked list reversal")
    void linkedListReversal() {
        MethodSpecification spec = infer("""
            class Node {
                int val;
                Node next;
                Node reverse(Node head) {
                    if (head == null) return null;
                    Node prev = null;
                    Node current = head;
                    while (current != null) {
                        Node next = current.next;
                        current.next = prev;
                        prev = current;
                        current = next;
                    }
                    return prev;
                }
            }
            """, "reverse");
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n)")
        //   Node reverse(Node head) { ... }
        assertNotNull(spec);
        assertEquals("O(n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("String builder with guard and loop")
    void stringBuilderGuardAndLoop() {
        MethodSpecification spec = infer("""
            class T {
                String repeat(String s, int n) {
                    if (s == null) return null;
                    if (n <= 0) return "";
                    StringBuilder sb = new StringBuilder();
                    for (int i = 0; i < n; i++) { sb.append(s); }
                    return sb.toString();
                }
            }
            """, "repeat");
        // Expected annotated method after inference:
        //   @Requires("n > 0")           (or similar numeric constraint)
        //   @Complexity(time = "O(n)")
        //   String repeat(String s, int n) { ... }
        assertTrue(spec.getPreconditions().stream()
                .anyMatch(p -> p.contains("n") && (p.contains(">") || p.contains("<"))),
                "Expected numeric constraint on n");
    }

    @Test
    @DisplayName("GCD algorithm - recursive")
    void gcd() {
        MethodSpecification spec = infer("""
            class T {
                int gcd(int a, int b) {
                    if (b == 0) return a;
                    return gcd(b, a % b);
                }
            }
            """, "gcd");
        // Expected annotated method after inference:
        //   @Complexity(time = "O(2^n)")
        //   int gcd(int a, int b) { ... }
        assertEquals("O(2^n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("Array swap")
    void arraySwap() {
        MethodSpecification spec = infer("""
            class T {
                void swap(int[] arr, int i, int j) {
                    int temp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = temp;
                }
            }
            """, "swap");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Assignable("arr[*]")
        //   @Complexity(time = "O(1)")
        //   void swap(int[] arr, int i, int j) { ... }
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("arr[*]")),
                "Expected arr[*] assignable");
    }

    @Test
    @DisplayName("Complex arithmetic with multiple transformations")
    void complexArithmetic() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int x, int y, int z) {
                    int a = x + y;
                    int b = a * z;
                    int c = b - x;
                    int d = c + a;
                    return d;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == ((((x + y) * z) - x) + (x + y))")
        //   @Pure
        //   int compute(int x, int y, int z) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result ==")),
                "Expected symbolic result");
    }

    @Test
    @DisplayName("Clamp function with guard clauses")
    void clampFunction() {
        MethodSpecification spec = infer("""
            class T {
                int clamp(int value, int min, int max) {
                    if (value < min) return min;
                    if (value > max) return max;
                    return value;
                }
            }
            """, "clamp");
        // Expected annotated method after inference:
        //   @Requires("value >= min")     (or similar value/min relationship)
        //   @Requires("value <= max")
        //   @Pure
        //   int clamp(int value, int min, int max) { ... }
        assertTrue(spec.getPreconditions().stream()
                .anyMatch(p -> p.contains("value") && p.contains("min")),
                "Expected value/min relationship");
    }

    @Test
    @DisplayName("Combined guard + branch + loop + return")
    void combinedPatterns() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n, int[] arr) {
                    if (n < 0) throw new IllegalArgumentException("negative");
                    if (arr == null) return n * 2;
                    int base = n * n;
                    int sum = 0;
                    for (int i = 0; i < arr.length; i++) { sum += arr[i]; }
                    if (sum > 0) return base + sum;
                    else return base;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Requires("n >= 0")           (inverted from: if n < 0 throw)
        //   @Signals("n < 0 ==> throws IllegalArgumentException")
        //   @Complexity(time = "O(n)")
        //   int compute(int n, int[] arr) { ... }
        assertNotNull(spec);
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("n >= 0")),
                "Expected n >= 0 from guard");
    }

    @Test
    @DisplayName("Iterative power function")
    void iterativePower() {
        MethodSpecification spec = infer("""
            class T {
                int power(int base, int exp) {
                    int result = 1;
                    for (int i = 0; i < exp; i++) { result *= base; }
                    return result;
                }
            }
            """, "power");
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n)")
        //   (no @Ensures for \\result == 1 -- result is loop-tainted)
        //   int power(int base, int exp) { ... }
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == 1")),
                "Should not resolve loop-tainted accumulator");
        assertEquals("O(n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("Deeply nested if/else (stress test)")
    void deeplyNestedBranches() {
        MethodSpecification spec = infer("""
            class T {
                int deep(int a) {
                    int x = a * 2;
                    if (a > 100) {
                        if (a > 200) {
                            if (a > 300) {
                                if (a > 400) {
                                    if (a > 500) { return x + 5; }
                                    else { return x + 4; }
                                } else { return x + 3; }
                            } else { return x + 2; }
                        } else { return x + 1; }
                    } else { return x; }
                }
            }
            """, "deep");
        // Expected annotated method after inference:
        //   @Ensures("a > 500 ==> \\result == (a * 2) + 5")
        //   @Ensures("a > 400 && a <= 500 ==> \\result == (a * 2) + 4")
        //   @Ensures("a > 300 && a <= 400 ==> \\result == (a * 2) + 3")
        //   ... (conditional postconditions for each branch)
        //   @Pure
        //   int deep(int a) { ... }
        assertNotNull(spec);
        assertFalse(spec.getPostconditions().isEmpty(), "Expected postconditions from deep nesting");
    }

    @Test
    @DisplayName("Switch expression return")
    void switchExpressionReturn() {
        MethodSpecification spec = infer("""
            class T {
                String dayType(int day) {
                    return switch (day) {
                        case 1, 7 -> "weekend";
                        case 2, 3, 4, 5, 6 -> "weekday";
                        default -> "unknown";
                    };
                }
            }
            """, "dayType");
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Pure
        //   String dayType(int day) { ... }
        assertNotNull(spec);
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null for switch expression");
    }

    @Test
    @DisplayName("Complex method: try/catch + loops + branches doesn't crash")
    void complexDoesNotCrash() {
        MethodSpecification spec = infer("""
            import java.util.ArrayList;
            import java.util.List;
            class T {
                List<String> process(String[] input) {
                    if (input == null) throw new IllegalArgumentException("null");
                    List<String> result = new ArrayList<>();
                    for (String s : input) {
                        try {
                            if (s != null && !s.isEmpty()) {
                                String upper = s.toUpperCase();
                                if (upper.length() > 3) result.add(upper);
                            }
                        } catch (Exception e) { }
                    }
                    return result;
                }
            }
            """, "process");
        // Expected annotated method after inference:
        //   @Requires("input != null")
        //   @Ensures("\\result != null")
        //   @Signals("input == null ==> throws IllegalArgumentException")
        //   @Complexity(time = "O(n)")
        //   List<String> process(String[] input) { ... }
        assertNotNull(spec);
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("input != null")),
                "Expected input != null");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null result");
    }

    @Test
    @DisplayName("Mixed field references: this.field and bare field")
    void mixedFieldReferences() {
        MethodSpecification spec = infer("""
            class T {
                private int count;
                private int max;
                boolean addAndCheck(int value) {
                    this.count += value;
                    if (count > max) { count = max; return true; }
                    return false;
                }
            }
            """, "addAndCheck");
        // Expected annotated method after inference:
        //   @Mutator
        //   @Assignable("this.count")
        //   boolean addAndCheck(int value) { ... }
        assertTrue(spec.isMutator(), "Expected mutator");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("this.count")),
                "Expected this.count assignable");
    }

    @Test
    @DisplayName("Abstract method (no body) -> no crash")
    void abstractMethod() {
        MethodSpecification spec = infer("""
            abstract class T {
                abstract int compute(int x);
                int other() { return 0; }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   (no annotations -- abstract methods have no body to analyze)
        //   abstract int compute(int x);
        assertNotNull(spec);
    }

    @Test
    @DisplayName("Void method with parameter mutation")
    void voidMethodParamMutation() {
        MethodSpecification spec = infer("""
            import java.util.List;
            class T {
                void populate(List<String> list, String item, int count) {
                    for (int i = 0; i < count; i++) { list.add(item); }
                }
            }
            """, "populate");
        // Expected annotated method after inference:
        //   @Requires("list != null")
        //   @Ensures("list.size() == \\old(list.size()) + count")
        //   @Complexity(time = "O(n)")
        //   void populate(List<String> list, String item, int count) { ... }
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("list != null")),
                "Expected list != null");
        assertTrue(anyContainsAll(spec.getPostconditions(), "list.size()", "\\old"),
                "Expected list size increase");
    }

    @Test
    @DisplayName("Bubble sort - quadratic with nested loops and swap")
    void bubbleSort() {
        MethodSpecification spec = infer("""
            class T {
                void bubbleSort(int[] arr) {
                    for (int i = 0; i < arr.length - 1; i++) {
                        for (int j = 0; j < arr.length - i - 1; j++) {
                            if (arr[j] > arr[j + 1]) {
                                int temp = arr[j];
                                arr[j] = arr[j + 1];
                                arr[j + 1] = temp;
                            }
                        }
                    }
                }
            }
            """, "bubbleSort");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Assignable("arr[*]")
        //   @Complexity(time = "O(n^2)")
        //   @LoopInvariant("i >= 0")
        //   @LoopInvariant("j >= 0")
        //   void bubbleSort(int[] arr) { ... }
        assertEquals("O(n^2)", spec.getTimeComplexity());
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("arr[*]")),
                "Expected array modification");
    }

    @Test
    @DisplayName("Stack-based expression evaluator pattern")
    void stackEvaluator() {
        MethodSpecification spec = infer("""
            import java.util.Stack;
            class T {
                int evaluate(int a, int b, String op) {
                    if (op == null) throw new IllegalArgumentException("null op");
                    if (op.equals("+")) return a + b;
                    if (op.equals("-")) return a - b;
                    if (op.equals("*")) return a * b;
                    if (op.equals("/")) {
                        if (b == 0) throw new ArithmeticException("div zero");
                        return a / b;
                    }
                    throw new IllegalArgumentException("unknown op");
                }
            }
            """, "evaluate");
        // Expected annotated method after inference:
        //   @Requires("op != null")
        //   @Signals("op == null ==> throws IllegalArgumentException")
        //   @Signals("b == 0 ==> throws ArithmeticException")
        //   @Signals("throws IllegalArgumentException")
        //   int evaluate(int a, int b, String op) { ... }
        assertNotNull(spec);
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("IllegalArgumentException")),
                "Expected IAE");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("ArithmeticException")),
                "Expected ArithmeticException");
    }

    @Test
    @DisplayName("Filter method: iterates over collection and adds matching items")
    void filterMethod() {
        MethodSpecification spec = infer("""
            import java.util.ArrayList;
            import java.util.List;
            class T {
                List<Integer> filterPositive(int[] arr) {
                    List<Integer> result = new ArrayList<>();
                    for (int val : arr) {
                        if (val > 0) result.add(val);
                    }
                    return result;
                }
            }
            """, "filterPositive");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.size() <= arr.length")
        //   @Complexity(time = "O(n)")
        //   List<Integer> filterPositive(int[] arr) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null result");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.size() <= arr.length")),
                "Expected size constraint relative to input, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Method with multiple return types: early literal, branch computed, final computed")
    void multipleReturnStyles() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    if (a == 0) return 0;
                    if (b == 0) return a;
                    int result = a * b;
                    if (result > 100) {
                        return 100;
                    }
                    return result;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Requires("a == 0")           (or similar numeric constraints)
        //   @Ensures("a == 0 ==> \\result == 0")
        //   @Ensures("b == 0 ==> \\result == a")
        //   @Pure
        //   int compute(int a, int b) { ... }
        assertNotNull(spec);
        assertFalse(spec.getPostconditions().isEmpty(),
                "Expected postconditions for multi-return method");
    }

    @Test
    @DisplayName("Palindrome checker with string operations")
    void palindromeChecker() {
        MethodSpecification spec = infer("""
            class T {
                boolean isPalindrome(String s) {
                    if (s == null) return false;
                    String reversed = new StringBuilder(s).reverse().toString();
                    return s.equals(reversed);
                }
            }
            """, "isPalindrome");
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   boolean isPalindrome(String s) { ... }
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("s != null")),
                "Expected s != null");
    }

    @Test
    @DisplayName("Min/max finder with for-each")
    void minMaxFinder() {
        MethodSpecification spec = infer("""
            class T {
                int findMax(int[] arr) {
                    if (arr == null || arr.length == 0)
                        throw new IllegalArgumentException("empty");
                    int max = arr[0];
                    for (int i = 1; i < arr.length; i++) {
                        if (arr[i] > max) max = arr[i];
                    }
                    return max;
                }
            }
            """, "findMax");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Requires("arr.length > 0")
        //   @Signals("arr == null || arr.length == 0 ==> throws IllegalArgumentException")
        //   @Complexity(time = "O(n)")
        //   int findMax(int[] arr) { ... }
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null");
    }

    @Test
    @DisplayName("Recursive factorial")
    void factorial() {
        MethodSpecification spec = infer("""
            class T {
                int factorial(int n) {
                    if (n <= 1) return 1;
                    return n * factorial(n - 1);
                }
            }
            """, "factorial");
        // Expected annotated method after inference:
        //   @Complexity(time = "O(2^n)")
        //   @Ensures("\\result >= 1")     (or "\\result > 0")
        //   int factorial(int n) { ... }
        assertEquals("O(2^n)", spec.getTimeComplexity());
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result >= 1") || p.contains("\\result > 0")),
                "Expected positive result for factorial");
    }

    @Test
    @DisplayName("Map iteration with collection operations")
    void mapIteration() {
        MethodSpecification spec = infer("""
            import java.util.Map;
            import java.util.HashMap;
            class T {
                Map<String, Integer> count(String[] words) {
                    Map<String, Integer> freq = new HashMap<>();
                    for (String w : words) {
                        freq.put(w, freq.getOrDefault(w, 0) + 1);
                    }
                    return freq;
                }
            }
            """, "count");
        // Expected annotated method after inference:
        //   @Requires("words != null")
        //   @Ensures("\\result != null")
        //   @Complexity(time = "O(n)")
        //   Map<String, Integer> count(String[] words) { ... }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null result");
        assertEquals("O(n)", spec.getTimeComplexity());
    }
}
