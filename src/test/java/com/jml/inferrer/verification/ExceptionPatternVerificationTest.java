package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for exception handling patterns: guard clauses,
 * try-catch recovery, multi-exception methods, and exception-driven control flow.
 */
class ExceptionPatternVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Guard clause variations
    // =========================================================================

    @Test
    @DisplayName("Guard: single null check throws NPE")
    void guardSingleNull() throws IOException {
        String source = """
                public class Guard1 {
                    public int length(String s) {
                        if (s == null) throw new NullPointerException();
                        return s.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard1", "length"));
    }

    @Test
    @DisplayName("Guard: multiple null checks for different params")
    void guardMultipleNull() throws IOException {
        String source = """
                public class Guard2 {
                    public int combinedLength(String a, String b) {
                        if (a == null) throw new NullPointerException("a is null");
                        if (b == null) throw new NullPointerException("b is null");
                        return a.length() + b.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard2", "combinedLength"));
    }

    @Test
    @DisplayName("Guard: range check throws IndexOutOfBounds")
    void guardRangeCheck() throws IOException {
        String source = """
                public class Guard3 {
                    public int get(int[] arr, int index) {
                        if (arr == null) throw new NullPointerException();
                        if (index < 0 || index >= arr.length) throw new IndexOutOfBoundsException();
                        return arr[index];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard3", "get"));
    }

    @Test
    @DisplayName("Guard: positive number required")
    void guardPositiveRequired() throws IOException {
        String source = """
                public class Guard4 {
                    public double squareRoot(double x) {
                        if (x < 0) throw new IllegalArgumentException();
                        return Math.sqrt(x);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard4", "squareRoot"));
    }

    @Test
    @DisplayName("Guard: non-empty string required")
    void guardNonEmptyString() throws IOException {
        String source = """
                public class Guard5 {
                    public char firstChar(String s) {
                        if (s == null || s.isEmpty()) throw new IllegalArgumentException();
                        return s.charAt(0);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard5", "firstChar"));
    }

    @Test
    @DisplayName("Guard: capacity check before insertion")
    void guardCapacityCheck() throws IOException {
        String source = """
                public class Guard6 {
                    private int[] data;
                    private int size;
                    private int capacity;
                    public void add(int value) {
                        if (size >= capacity) throw new IllegalStateException("full");
                        data[size] = value;
                        size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard6", "add"));
    }

    @Test
    @DisplayName("Guard: division by zero prevention")
    void guardDivisionByZero() throws IOException {
        String source = """
                public class Guard7 {
                    public int safeDivide(int a, int b) {
                        if (b == 0) throw new ArithmeticException("division by zero");
                        return a / b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard7", "safeDivide"));
    }

    @Test
    @DisplayName("Guard: percentage range check")
    void guardPercentageRange() throws IOException {
        String source = """
                public class Guard8 {
                    public double applyDiscount(double price, double percent) {
                        if (price < 0) throw new IllegalArgumentException();
                        if (percent < 0 || percent > 100) throw new IllegalArgumentException();
                        return price * (1.0 - percent / 100.0);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Guard8", "applyDiscount"));
    }

    // =========================================================================
    // Try-catch recovery patterns
    // =========================================================================

    @Test
    @DisplayName("TryCatch: return default on NumberFormatException")
    void tryCatchReturnDefault() throws IOException {
        String source = """
                public class TryCatch1 {
                    public int parseIntSafe(String s) {
                        if (s == null) return 0;
                        try {
                            return Integer.parseInt(s);
                        } catch (NumberFormatException e) {
                            return 0;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TryCatch1", "parseIntSafe"));
    }

    @Test
    @DisplayName("TryCatch: wrap and rethrow as different exception type")
    void tryCatchWrapAndRethrow() throws IOException {
        String source = """
                public class TryCatch2 {
                    public int compute(String input) {
                        if (input == null) throw new IllegalArgumentException();
                        try {
                            return Integer.parseInt(input) * 2;
                        } catch (NumberFormatException e) {
                            throw new IllegalArgumentException("bad input", e);
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TryCatch2", "compute"));
    }

    @Test
    @DisplayName("TryCatch: fallback value on array index exception")
    void tryCatchFallbackOnArrayBounds() throws IOException {
        String source = """
                public class TryCatch3 {
                    public int safeGet(int[] arr, int index, int defaultVal) {
                        if (arr == null) return defaultVal;
                        try {
                            return arr[index];
                        } catch (ArrayIndexOutOfBoundsException e) {
                            return defaultVal;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TryCatch3", "safeGet"));
    }

    // =========================================================================
    // Exception-driven control flow
    // =========================================================================

    @Test
    @DisplayName("Exception: early exit pattern with multiple checks")
    void earlyExitMultipleChecks() throws IOException {
        String source = """
                public class ExcFlow1 {
                    public double computeRatio(int numerator, int denominator, int scale) {
                        if (denominator == 0) throw new ArithmeticException();
                        if (scale <= 0) throw new IllegalArgumentException();
                        return (double) numerator / denominator * scale;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ExcFlow1", "computeRatio"));
    }

    @Test
    @DisplayName("Exception: state validation before operation")
    void stateValidation() throws IOException {
        String source = """
                public class ExcFlow2 {
                    private boolean initialized;
                    private int[] data;
                    public int sum() {
                        if (!initialized) throw new IllegalStateException();
                        if (data == null) throw new IllegalStateException();
                        int total = 0;
                        for (int i = 0; i < data.length; i++) {
                            total += data[i];
                        }
                        return total;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ExcFlow2", "sum"));
    }

    @Test
    @DisplayName("Exception: assertion-style checks in computation")
    void assertionStyleChecks() throws IOException {
        String source = """
                public class ExcFlow3 {
                    public int[] createRange(int start, int end) {
                        if (start > end) throw new IllegalArgumentException();
                        int length = end - start;
                        int[] result = new int[length];
                        for (int i = 0; i < length; i++) {
                            result[i] = start + i;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ExcFlow3", "createRange"));
    }

    // =========================================================================
    // Complex guard + computation combinations
    // =========================================================================

    @Test
    @DisplayName("Guard + loop: validate then iterate")
    void guardThenLoop() throws IOException {
        String source = """
                public class GuardLoop1 {
                    public int countMatches(int[] arr, int target) {
                        if (arr == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardLoop1", "countMatches"));
    }

    @Test
    @DisplayName("Guard + field update: validate then modify state")
    void guardThenFieldUpdate() throws IOException {
        String source = """
                public class GuardField1 {
                    private int balance;
                    public void withdraw(int amount) {
                        if (amount <= 0) throw new IllegalArgumentException();
                        if (amount > balance) throw new IllegalStateException();
                        balance -= amount;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardField1", "withdraw"));
    }

    @Test
    @DisplayName("Guard + return: validate array then compute average")
    void guardThenCompute() throws IOException {
        String source = """
                public class GuardCompute1 {
                    public double average(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (arr.length == 0) throw new IllegalArgumentException();
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            sum += arr[i];
                        }
                        return (double) sum / arr.length;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardCompute1", "average"));
    }

    @Test
    @DisplayName("Guard cascade: validate all inputs then complex computation")
    void guardCascadeThenCompute() throws IOException {
        String source = """
                public class GuardCascade1 {
                    public int weightedSum(int[] values, int[] weights) {
                        if (values == null) throw new IllegalArgumentException();
                        if (weights == null) throw new IllegalArgumentException();
                        if (values.length != weights.length) throw new IllegalArgumentException();
                        if (values.length == 0) throw new IllegalArgumentException();
                        int sum = 0;
                        for (int i = 0; i < values.length; i++) {
                            sum += values[i] * weights[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardCascade1", "weightedSum"));
    }

    // =========================================================================
    // Defensive return patterns (null-safe returns)
    // =========================================================================

    @Test
    @DisplayName("Defensive: return empty array instead of null")
    void defensiveEmptyArray() throws IOException {
        String source = """
                public class Defensive1 {
                    public int[] filterPositive(int[] arr) {
                        if (arr == null) return new int[0];
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) count++;
                        }
                        int[] result = new int[count];
                        int idx = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) {
                                result[idx] = arr[i];
                                idx++;
                            }
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Defensive1", "filterPositive"));
    }

    @Test
    @DisplayName("Defensive: return empty string instead of null")
    void defensiveEmptyString() throws IOException {
        String source = """
                public class Defensive2 {
                    public String safe(String s) {
                        if (s == null) return "";
                        return s;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Defensive2", "safe"));
    }

    @Test
    @DisplayName("Defensive: return -1 for not found")
    void defensiveNotFound() throws IOException {
        String source = """
                public class Defensive3 {
                    public int indexOf(int[] arr, int target) {
                        if (arr == null) return -1;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return i;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Defensive3", "indexOf"));
    }
}
