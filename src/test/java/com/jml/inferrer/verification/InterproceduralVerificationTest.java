package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for interprocedural patterns: methods calling other methods,
 * helper method delegation, standard library usage, and multi-method classes.
 */
class InterproceduralVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Method calling another method in same class
    // =========================================================================

    @Test
    @DisplayName("Interproc: public method delegates to private helper")
    void delegateToHelper() throws IOException {
        String source = """
                public class Delegator1 {
                    private int square(int x) {
                        return x * x;
                    }
                    public int sumOfSquares(int a, int b) {
                        return square(a) + square(b);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delegator1", "sumOfSquares"));
    }

    @Test
    @DisplayName("Interproc: validation helper called before computation")
    void validationHelper() throws IOException {
        String source = """
                public class Delegator2 {
                    private void validatePositive(int n) {
                        if (n <= 0) throw new IllegalArgumentException();
                    }
                    public int process(int a, int b) {
                        validatePositive(a);
                        validatePositive(b);
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delegator2", "process"));
    }

    @Test
    @DisplayName("Interproc: getter used in computation")
    void getterInComputation() throws IOException {
        String source = """
                public class Delegator3 {
                    private int width;
                    private int height;
                    public int getWidth() { return width; }
                    public int getHeight() { return height; }
                    public int area() {
                        return getWidth() * getHeight();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delegator3", "area"));
    }

    @Test
    @DisplayName("Interproc: chained method calls")
    void chainedMethodCalls() throws IOException {
        String source = """
                public class Delegator4 {
                    private int abs(int n) {
                        return n < 0 ? -n : n;
                    }
                    private int max(int a, int b) {
                        return a >= b ? a : b;
                    }
                    public int maxAbs(int a, int b) {
                        return max(abs(a), abs(b));
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delegator4", "maxAbs"));
    }

    // =========================================================================
    // Standard library method usage
    // =========================================================================

    @Test
    @DisplayName("StdLib: Math.max of two values")
    void mathMax() throws IOException {
        String source = """
                public class StdLib1 {
                    public int maximum(int a, int b) {
                        return Math.max(a, b);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StdLib1", "maximum"));
    }

    @Test
    @DisplayName("StdLib: Math.min of two values")
    void mathMin() throws IOException {
        String source = """
                public class StdLib2 {
                    public int minimum(int a, int b) {
                        return Math.min(a, b);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StdLib2", "minimum"));
    }

    @Test
    @DisplayName("StdLib: Math.abs of value")
    void mathAbs() throws IOException {
        String source = """
                public class StdLib3 {
                    public double absValue(double x) {
                        return Math.abs(x);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StdLib3", "absValue"));
    }

    @Test
    @DisplayName("StdLib: Arrays.sort then access")
    void arraysSortThenAccess() throws IOException {
        String source = """
                import java.util.Arrays;
                public class StdLib4 {
                    public int median(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int[] copy = Arrays.copyOf(arr, arr.length);
                        Arrays.sort(copy);
                        return copy[copy.length / 2];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StdLib4", "median"));
    }

    @Test
    @DisplayName("StdLib: Integer.parseInt with guard")
    void integerParseInt() throws IOException {
        String source = """
                public class StdLib5 {
                    public int parseOrDefault(String s, int defaultValue) {
                        if (s == null) return defaultValue;
                        if (s.isEmpty()) return defaultValue;
                        try {
                            return Integer.parseInt(s);
                        } catch (NumberFormatException e) {
                            return defaultValue;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StdLib5", "parseOrDefault"));
    }

    @Test
    @DisplayName("StdLib: String.valueOf conversion")
    void stringValueOf() throws IOException {
        String source = """
                public class StdLib6 {
                    public String intToString(int n) {
                        return String.valueOf(n);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StdLib6", "intToString"));
    }

    // =========================================================================
    // Multi-method classes with field coordination
    // =========================================================================

    @Test
    @DisplayName("Interproc: setter then getter consistency")
    void setterGetterConsistency() throws IOException {
        String source = """
                public class SetGet1 {
                    private int value;
                    public void setValue(int v) {
                        this.value = v;
                    }
                    public int getValue() {
                        return value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SetGet1", "setValue"));
    }

    @Test
    @DisplayName("Interproc: increment then check threshold")
    void incrementThenCheck() throws IOException {
        String source = """
                public class Counter1 {
                    private int count;
                    private int threshold;
                    public void increment() {
                        count++;
                    }
                    public boolean isAboveThreshold() {
                        return count > threshold;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Counter1", "increment"));
    }

    @Test
    @DisplayName("Interproc: add item updates size field")
    void addItemUpdatesSize() throws IOException {
        String source = """
                public class SimpleList1 {
                    private int[] items;
                    private int size;
                    public void add(int item) {
                        if (size >= items.length) throw new IllegalStateException();
                        items[size] = item;
                        size++;
                    }
                    public int size() {
                        return size;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SimpleList1", "add"));
    }

    // =========================================================================
    // Recursive methods
    // =========================================================================

    @Test
    @DisplayName("Recursive: factorial")
    void recursiveFactorial() throws IOException {
        String source = """
                public class Recursive1 {
                    public int factorial(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        if (n <= 1) return 1;
                        return n * factorial(n - 1);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Recursive1", "factorial"));
    }

    @Test
    @DisplayName("Recursive: fibonacci")
    void recursiveFibonacci() throws IOException {
        String source = """
                public class Recursive2 {
                    public int fib(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        if (n <= 1) return n;
                        return fib(n - 1) + fib(n - 2);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Recursive2", "fib"));
    }

    @Test
    @DisplayName("Recursive: sum of array elements")
    void recursiveArraySum() throws IOException {
        String source = """
                public class Recursive3 {
                    public int sum(int[] arr, int index) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (index < 0 || index > arr.length) throw new IndexOutOfBoundsException();
                        if (index == arr.length) return 0;
                        return arr[index] + sum(arr, index + 1);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Recursive3", "sum"));
    }

    @Test
    @DisplayName("Recursive: binary search")
    void recursiveBinarySearch() throws IOException {
        String source = """
                public class Recursive4 {
                    public int binarySearch(int[] arr, int target, int lo, int hi) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (lo > hi) return -1;
                        int mid = lo + (hi - lo) / 2;
                        if (arr[mid] == target) return mid;
                        if (arr[mid] < target) return binarySearch(arr, target, mid + 1, hi);
                        return binarySearch(arr, target, lo, mid - 1);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Recursive4", "binarySearch"));
    }

    @Test
    @DisplayName("Recursive: power computation")
    void recursivePower() throws IOException {
        String source = """
                public class Recursive5 {
                    public long power(int base, int exp) {
                        if (exp < 0) throw new IllegalArgumentException();
                        if (exp == 0) return 1;
                        if (exp % 2 == 0) {
                            long half = power(base, exp / 2);
                            return half * half;
                        }
                        return base * power(base, exp - 1);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Recursive5", "power"));
    }

    // =========================================================================
    // Methods using this reference
    // =========================================================================

    @Test
    @DisplayName("Interproc: method returns this for chaining")
    void returnThisChaining() throws IOException {
        String source = """
                public class Chainable1 {
                    private int x;
                    private int y;
                    public Chainable1 setX(int x) {
                        this.x = x;
                        return this;
                    }
                    public Chainable1 setY(int y) {
                        this.y = y;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Chainable1", "setX"));
    }

    @Test
    @DisplayName("Interproc: method compares this fields")
    void compareThisFields() throws IOException {
        String source = """
                public class Comparable1 {
                    private int value;
                    public int compareTo(Comparable1 other) {
                        if (other == null) throw new IllegalArgumentException();
                        return this.value - other.value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Comparable1", "compareTo"));
    }

    @Test
    @DisplayName("Interproc: equals based on field comparison")
    void equalsFieldComparison() throws IOException {
        String source = """
                public class Equatable1 {
                    private int id;
                    private String name;
                    public boolean isEqual(Equatable1 other) {
                        if (other == null) return false;
                        return this.id == other.id;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Equatable1", "isEqual"));
    }
}
