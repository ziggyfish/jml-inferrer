package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Tier 1 formal verification tests for precondition specifications.
 * Each test writes JML comment syntax directly and invokes OpenJML ESC.
 */
class PreconditionVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Basic null checks
    // =========================================================================

    @Test
    @DisplayName("Null check on method call: requires s != null")
    void nullCheckOnMethodCall() throws IOException {
        String source = """
                public class NullCheckMethodCall {
                    public int compute(String s) {
                        return s.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NullCheckMethodCall", "compute"));
    }

    @Test
    @DisplayName("Null check on array access: requires arr != null")
    void nullCheckOnArrayAccess() throws IOException {
        String source = """
                public class NullCheckArrayAccess {
                    public int first(int[] arr) {
                        return arr[0];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NullCheckArrayAccess", "first"));
    }

    @Test
    @DisplayName("Multiple parameter null checks: requires a != null && b != null")
    void multipleParamNullChecks() throws IOException {
        String source = """
                public class MultipleParamNullChecks {
                    public int totalLength(String a, String b) {
                        return a.length() + b.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultipleParamNullChecks", "totalLength"));
    }

    @Test
    @DisplayName("Three param null checks with concatenation")
    void threeParamNullChecks() throws IOException {
        String source = """
                public class ThreeParamNullChecks {
                    public int combinedLength(String a, String b, String c) {
                        return a.length() + b.length() + c.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ThreeParamNullChecks", "combinedLength"));
    }

    // =========================================================================
    // Array bounds
    // =========================================================================

    @Test
    @DisplayName("Array bounds check: requires arr.length > 0")
    void arrayBoundsCheck() throws IOException {
        String source = """
                public class ArrayBoundsCheck {
                    public int first(int[] arr) {
                        return arr[0];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayBoundsCheck", "first"));
    }

    @Test
    @DisplayName("Array specific index: requires arr.length > 2")
    void arraySpecificIndex() throws IOException {
        String source = """
                public class ArraySpecificIndex {
                    public int third(int[] arr) {
                        return arr[2];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArraySpecificIndex", "third"));
    }

    @Test
    @DisplayName("Combined null and bounds: requires arr != null && arr.length > 0")
    void combinedNullAndBounds() throws IOException {
        String source = """
                public class CombinedNullAndBounds {
                    public int firstElement(int[] arr) {
                        return arr[0];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CombinedNullAndBounds", "firstElement"));
    }

    @Test
    @DisplayName("Array index from parameter: requires idx >= 0 && idx < arr.length")
    void arrayIndexFromParam() throws IOException {
        String source = """
                public class ArrayIndexFromParam {
                    public int getAt(int[] arr, int idx) {
                        return arr[idx];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayIndexFromParam", "getAt"));
    }

    @Test
    @DisplayName("Two arrays same length: swap elements")
    void twoArraysSameLength() throws IOException {
        String source = """
                public class TwoArraysSameLength {
                    public void swap(int[] a, int[] b, int idx) {
                        int tmp = a[idx];
                        a[idx] = b[idx];
                        b[idx] = tmp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TwoArraysSameLength", "swap"));
    }

    // =========================================================================
    // Numeric guards and throws
    // =========================================================================

    @Test
    @DisplayName("Numeric guard with throw: requires n >= 0")
    void numericGuardThrow() throws IOException {
        String source = """
                public class NumericGuardThrow {
                    public int process(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        return n * 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NumericGuardThrow", "process"));
    }

    @Test
    @DisplayName("Equality guard with throw: requires n != 0")
    void equalityGuardThrow() throws IOException {
        String source = """
                public class EqualityGuardThrow {
                    public int divide(int a, int n) {
                        if (n == 0) throw new ArithmeticException();
                        return a / n;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "EqualityGuardThrow", "divide"));
    }

    @Test
    @DisplayName("Positive integer precondition: requires n > 0")
    void positiveIntegerPrecondition() throws IOException {
        String source = """
                public class PositiveIntegerPrecondition {
                    public int reciprocal(int n) {
                        return 100 / n;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PositiveIntegerPrecondition", "reciprocal"));
    }

    @Test
    @DisplayName("Parameter relationship: requires lo <= hi")
    void paramRelationship() throws IOException {
        String source = """
                public class ParamRelationship {
                    public int range(int lo, int hi) {
                        return hi - lo;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ParamRelationship", "range"));
    }

    // =========================================================================
    // Complex: guard clauses + loops
    // =========================================================================

    @Test
    @DisplayName("Guard clause then loop over array")
    void guardThenLoop() throws IOException {
        String source = """
                public class GuardThenLoop {
                    public int sumPositive(int[] arr) {
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) {
                                sum += arr[i];
                            }
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardThenLoop", "sumPositive"));
    }

    @Test
    @DisplayName("Null + bounds + loop: find max in array")
    void findMaxInArray() throws IOException {
        String source = """
                public class FindMaxInArray {
                    public int findMax(int[] arr) {
                        int max = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] > max) {
                                max = arr[i];
                            }
                        }
                        return max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FindMaxInArray", "findMax"));
    }

    @Test
    @DisplayName("Null + bounds + conditional loop: count negatives")
    void countNegatives() throws IOException {
        String source = """
                public class CountNegatives {
                    public int countNeg(int[] arr) {
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < 0) {
                                count++;
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CountNegatives", "countNeg"));
    }

    @Test
    @DisplayName("Range validation then subarray sum")
    void rangeValidationSubarraySum() throws IOException {
        String source = """
                public class RangeValidationSubarraySum {
                    public int subarraySum(int[] arr, int from, int to) {
                        int sum = 0;
                        for (int i = from; i < to; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RangeValidationSubarraySum", "subarraySum"));
    }

    // =========================================================================
    // Complex: multiple guards + branching
    // =========================================================================

    @Test
    @DisplayName("Multiple guards: division with validated divisor and dividend")
    void multipleGuardsValidatedDivision() throws IOException {
        String source = """
                public class MultipleGuardsValidatedDivision {
                    public int safeDivide(int a, int b) {
                        if (b == 0) throw new ArithmeticException();
                        if (a < 0) throw new IllegalArgumentException();
                        return a / b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultipleGuardsValidatedDivision", "safeDivide"));
    }

    @Test
    @DisplayName("Cascaded null checks: object chain dereference")
    void cascadedNullChecks() throws IOException {
        String source = """
                public class CascadedNullChecks {
                    String name;
                    public int getNameLength(CascadedNullChecks obj) {
                        return obj.name.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CascadedNullChecks", "getNameLength"));
    }

    @Test
    @DisplayName("Guard with early return then computation")
    void guardEarlyReturnThenCompute() throws IOException {
        String source = """
                public class GuardEarlyReturnThenCompute {
                    public int sumOrZero(int[] arr) {
                        if (arr.length == 0) return 0;
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardEarlyReturnThenCompute", "sumOrZero"));
    }

    @Test
    @DisplayName("Boolean parameter precondition with branching")
    void booleanParamBranching() throws IOException {
        String source = """
                public class BooleanParamBranching {
                    public int process(int n, boolean doubleIt) {
                        if (doubleIt) {
                            return n * 2;
                        }
                        return n;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BooleanParamBranching", "process"));
    }

    // =========================================================================
    // Complex: fields + preconditions + state
    // =========================================================================

    @Test
    @DisplayName("Field-based precondition: capacity > 0 for add")
    void fieldBasedPrecondition() throws IOException {
        String source = """
                public class FieldBasedPrecondition {
                    int size;
                    int capacity;
                    public void add() {
                        this.size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldBasedPrecondition", "add"));
    }

    @Test
    @DisplayName("Array field null + bounds: get from internal array")
    void arrayFieldNullAndBounds() throws IOException {
        String source = """
                public class ArrayFieldNullAndBounds {
                    int[] data;
                    int size;
                    public int get(int idx) {
                        return this.data[idx];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayFieldNullAndBounds", "get"));
    }

    @Test
    @DisplayName("Stack-like precondition: pop requires size > 0")
    void stackPopPrecondition() throws IOException {
        String source = """
                public class StackPopPrecondition {
                    int[] data;
                    int size;
                    public int pop() {
                        this.size--;
                        return this.data[this.size];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StackPopPrecondition", "pop"));
    }

    // =========================================================================
    // Complex: loops with multiple array accesses
    // =========================================================================

    @Test
    @DisplayName("Copy array: src and dst null checks + length match")
    void copyArrayPreconditions() throws IOException {
        String source = """
                public class CopyArrayPreconditions {
                    public void copy(int[] src, int[] dst) {
                        for (int i = 0; i < src.length; i++) {
                            dst[i] = src[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CopyArrayPreconditions", "copy"));
    }

    @Test
    @DisplayName("Dot product: two arrays same length")
    void dotProductPreconditions() throws IOException {
        String source = """
                public class DotProductPreconditions {
                    public int dotProduct(int[] a, int[] b) {
                        int result = 0;
                        for (int i = 0; i < a.length; i++) {
                            result += a[i] * b[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DotProductPreconditions", "dotProduct"));
    }

    @Test
    @DisplayName("Binary search: array not null, lo/hi bounds valid")
    void binarySearchPreconditions() throws IOException {
        String source = """
                public class BinarySearchPreconditions {
                    public int binarySearch(int[] arr, int target, int lo, int hi) {
                        while (lo < hi) {
                            int mid = lo + (hi - lo) / 2;
                            if (arr[mid] == target) return mid;
                            if (arr[mid] < target) {
                                lo = mid + 1;
                            } else {
                                hi = mid;
                            }
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BinarySearchPreconditions", "binarySearch"));
    }

    @Test
    @DisplayName("Reverse array in place: null + length preconditions")
    void reverseArrayPreconditions() throws IOException {
        String source = """
                public class ReverseArrayPreconditions {
                    public void reverse(int[] arr) {
                        int left = 0;
                        int right = arr.length - 1;
                        while (left < right) {
                            int tmp = arr[left];
                            arr[left] = arr[right];
                            arr[right] = tmp;
                            left++;
                            right--;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ReverseArrayPreconditions", "reverse"));
    }

    // =========================================================================
    // Complex: multi-method interaction patterns
    // =========================================================================

    @Test
    @DisplayName("Clamp with min/max: requires min <= max")
    void clampMinMax() throws IOException {
        String source = """
                public class ClampMinMax {
                    public int clamp(int value, int min, int max) {
                        if (value < min) return min;
                        if (value > max) return max;
                        return value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ClampMinMax", "clamp"));
    }

    @Test
    @DisplayName("Modular arithmetic: requires mod > 0")
    void modularArithmetic() throws IOException {
        String source = """
                public class ModularArithmetic {
                    public int positiveMod(int value, int mod) {
                        int r = value % mod;
                        if (r < 0) r += mod;
                        return r;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ModularArithmetic", "positiveMod"));
    }

    @Test
    @DisplayName("Matrix element access: row/col bounds on 2D-as-1D array")
    void matrixElementAccess() throws IOException {
        String source = """
                public class MatrixElementAccess {
                    public int getElement(int[] data, int cols, int row, int col) {
                        return data[row * cols + col];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MatrixElementAccess", "getElement"));
    }

    @Test
    @DisplayName("Percentage calculation: requires total > 0")
    void percentageCalculation() throws IOException {
        String source = """
                public class PercentageCalculation {
                    public int percentage(int part, int total) {
                        return (part * 100) / total;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PercentageCalculation", "percentage"));
    }

    // =========================================================================
    // Complex: string + null + conditional
    // =========================================================================

    @Test
    @DisplayName("String comparison with null guard")
    void stringComparisonNullGuard() throws IOException {
        String source = """
                public class StringComparisonNullGuard {
                    public boolean longerThan(String a, String b) {
                        return a.length() > b.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StringComparisonNullGuard", "longerThan"));
    }

    @Test
    @DisplayName("Substring preconditions: valid range")
    void substringPreconditions() throws IOException {
        String source = """
                public class SubstringPreconditions {
                    public String safeSubstring(String s, int start, int end) {
                        return s.substring(start, end);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SubstringPreconditions", "safeSubstring"));
    }

    @Test
    @DisplayName("Char at index: string not null and valid index")
    void charAtIndex() throws IOException {
        String source = """
                public class CharAtIndex {
                    public char charAt(String s, int idx) {
                        return s.charAt(idx);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CharAtIndex", "charAt"));
    }

    // =========================================================================
    // Complex: combined pre+post with branching
    // =========================================================================

    @Test
    @DisplayName("Absolute difference: pre on params, post on result")
    void absoluteDifference() throws IOException {
        String source = """
                public class AbsoluteDifference {
                    public int absDiff(int a, int b) {
                        if (a >= b) return a - b;
                        return b - a;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AbsoluteDifference", "absDiff"));
    }

    @Test
    @DisplayName("Bounded increment: value stays within range")
    void boundedIncrement() throws IOException {
        String source = """
                public class BoundedIncrement {
                    int value;
                    int maxValue;
                    public void increment() {
                        this.value++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoundedIncrement", "increment"));
    }

    @Test
    @DisplayName("Safe array fill: range checks on start/end plus loop")
    void safeArrayFill() throws IOException {
        String source = """
                public class SafeArrayFill {
                    public void fill(int[] arr, int start, int end, int value) {
                        for (int i = start; i < end; i++) {
                            arr[i] = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SafeArrayFill", "fill"));
    }

    @Test
    @DisplayName("Linear search with early return: null + bounds in loop")
    void linearSearch() throws IOException {
        String source = """
                public class LinearSearch {
                    public int indexOf(int[] arr, int target) {
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return i;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LinearSearch", "indexOf"));
    }

    @Test
    @DisplayName("Factorial: requires n >= 0 with loop accumulator")
    void factorialPrecondition() throws IOException {
        String source = """
                public class FactorialPrecondition {
                    public int factorial(int n) {
                        int result = 1;
                        for (int i = 1; i <= n; i++) {
                            result *= i;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FactorialPrecondition", "factorial"));
    }

    @Test
    @DisplayName("GCD without validation: inferrer surfaces non-termination bug")
    void gcdPrecondition() throws IOException {
        // Same shape as GCDLoop in LoopInvariantVerificationTest: subtractive Euclidean
        // with no input validation, so gcd(0, -1) loops forever. Inferrer's
        // loop_decreases inference correctly emits `loop_decreases a + b`, which
        // OpenJML cannot discharge for non-positive inputs — the bug-detection signal.
        // See user_phd_context.md, "Bug-detection framing".
        String source = """
                public class GCDPrecondition {
                    public int gcd(int a, int b) {
                        while (a != b) {
                            if (a > b) {
                                a = a - b;
                            } else {
                                b = b - a;
                            }
                        }
                        return a;
                    }
                }
                """;
        assertFailed(inferAndVerify(source, "GCDPrecondition", "gcd"));
    }

    @Test
    @DisplayName("Power: base and exponent constraints")
    void powerPrecondition() throws IOException {
        String source = """
                public class PowerPrecondition {
                    public int power(int base, int exp) {
                        int result = 1;
                        for (int i = 0; i < exp; i++) {
                            result *= base;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PowerPrecondition", "power"));
    }

    // =========================================================================
    // Complex: nested conditions + state
    // =========================================================================

    @Test
    @DisplayName("Ring buffer: head/tail/capacity invariants")
    void ringBufferPreconditions() throws IOException {
        String source = """
                public class RingBufferPreconditions {
                    int[] data;
                    int head;
                    int tail;
                    int size;
                    public void enqueue(int value) {
                        this.data[this.tail] = value;
                        this.tail = (this.tail + 1) % this.data.length;
                        this.size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RingBufferPreconditions", "enqueue"));
    }

    @Test
    @DisplayName("Merge preconditions: two sorted arrays into result")
    void mergePreconditions() throws IOException {
        String source = """
                public class MergePreconditions {
                    public void merge(int[] a, int[] b, int[] result) {
                        int i = 0, j = 0, k = 0;
                        while (i < a.length && j < b.length) {
                            if (a[i] <= b[j]) {
                                result[k++] = a[i++];
                            } else {
                                result[k++] = b[j++];
                            }
                        }
                        while (i < a.length) {
                            result[k++] = a[i++];
                        }
                        while (j < b.length) {
                            result[k++] = b[j++];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MergePreconditions", "merge"));
    }

    @Test
    @DisplayName("Safe division chain: multiple divisor checks")
    void safeDivisionChain() throws IOException {
        String source = """
                public class SafeDivisionChain {
                    public int doubleDivide(int a, int b, int c) {
                        int first = a / b;
                        return first / c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SafeDivisionChain", "doubleDivide"));
    }

    @Test
    @DisplayName("Array rotation: length and shift preconditions")
    void arrayRotation() throws IOException {
        String source = """
                public class ArrayRotation {
                    public int[] rotate(int[] arr, int shift) {
                        int n = arr.length;
                        int[] result = new int[n];
                        for (int i = 0; i < n; i++) {
                            result[(i + shift) % n] = arr[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayRotation", "rotate"));
    }
}
