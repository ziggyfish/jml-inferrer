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
                    //@ requires s != null;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
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
                    //@ requires a != null;
                    //@ requires b != null;
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
                    //@ requires a != null;
                    //@ requires b != null;
                    //@ requires c != null;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 2;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
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
                    //@ requires arr != null;
                    //@ requires idx >= 0;
                    //@ requires idx < arr.length;
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
                    //@ requires a != null;
                    //@ requires b != null;
                    //@ requires a.length == b.length;
                    //@ requires idx >= 0;
                    //@ requires idx < a.length;
                    //@ assignable a[idx], b[idx];
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
                    //@ requires n >= 0;
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
                    //@ requires n != 0;
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
                    //@ requires n > 0;
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
                    //@ requires lo <= hi;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    public int sumPositive(int[] arr) {
                        int sum = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    public int findMax(int[] arr) {
                        int max = arr[0];
                        //@ loop_invariant i >= 1 && i <= arr.length;
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
                    //@ requires arr != null;
                    public int countNeg(int[] arr) {
                        int count = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        //@ loop_invariant count >= 0;
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
                    //@ requires arr != null;
                    //@ requires from >= 0;
                    //@ requires to >= from;
                    //@ requires to <= arr.length;
                    public int subarraySum(int[] arr, int from, int to) {
                        int sum = 0;
                        //@ loop_invariant i >= from && i <= to;
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
                    //@ requires b != 0;
                    //@ requires a >= 0;
                    //@ requires b > 0;
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
                    //@ requires obj != null;
                    //@ requires obj.name != null;
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
                    //@ requires arr != null;
                    public int sumOrZero(int[] arr) {
                        if (arr.length == 0) return 0;
                        int sum = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
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
                    //@ requires n >= 0;
                    //@ ensures \\result >= 0;
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
                    //@ requires this.size < this.capacity;
                    //@ requires this.capacity > 0;
                    //@ assignable this.size;
                    //@ ensures this.size == \\old(this.size) + 1;
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
                    //@ requires this.data != null;
                    //@ requires idx >= 0;
                    //@ requires idx < this.data.length;
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
                    //@ requires this.data != null;
                    //@ requires this.size > 0;
                    //@ requires this.size <= this.data.length;
                    //@ assignable this.size;
                    //@ ensures this.size == \\old(this.size) - 1;
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
                    //@ requires src != null;
                    //@ requires dst != null;
                    //@ requires src.length <= dst.length;
                    //@ assignable dst[*];
                    public void copy(int[] src, int[] dst) {
                        //@ loop_invariant i >= 0 && i <= src.length;
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
                    //@ requires a != null;
                    //@ requires b != null;
                    //@ requires a.length == b.length;
                    public int dotProduct(int[] a, int[] b) {
                        int result = 0;
                        //@ loop_invariant i >= 0 && i <= a.length;
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
                    //@ requires arr != null;
                    //@ requires lo >= 0;
                    //@ requires hi <= arr.length;
                    //@ requires lo <= hi;
                    public int binarySearch(int[] arr, int target, int lo, int hi) {
                        //@ loop_invariant lo >= 0 && hi <= arr.length;
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
                    //@ requires arr != null;
                    //@ assignable arr[*];
                    public void reverse(int[] arr) {
                        int left = 0;
                        int right = arr.length - 1;
                        //@ loop_invariant left >= 0;
                        //@ loop_invariant right >= -1 && right < arr.length;
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
                    //@ requires min <= max;
                    //@ ensures \\result >= min;
                    //@ ensures \\result <= max;
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
                    //@ requires mod > 0;
                    //@ ensures \\result >= 0;
                    //@ ensures \\result < mod;
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
                    //@ requires data != null;
                    //@ requires cols > 0;
                    //@ requires row >= 0;
                    //@ requires col >= 0;
                    //@ requires col < cols;
                    //@ requires row * cols + col < data.length;
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
                    //@ requires total > 0;
                    //@ requires part >= 0;
                    //@ requires part <= total;
                    //@ ensures \\result >= 0;
                    //@ ensures \\result <= 100;
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
                    //@ requires a != null;
                    //@ requires b != null;
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
                    //@ requires s != null;
                    //@ requires start >= 0;
                    //@ requires end >= start;
                    //@ requires end <= s.length();
                    //@ ensures \\result != null;
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
                    //@ requires s != null;
                    //@ requires idx >= 0;
                    //@ requires idx < s.length();
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
                    //@ ensures \\result >= 0;
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
                    //@ requires this.value < this.maxValue;
                    //@ assignable this.value;
                    //@ ensures this.value == \\old(this.value) + 1;
                    //@ ensures this.value <= this.maxValue;
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
                    //@ requires arr != null;
                    //@ requires start >= 0;
                    //@ requires end >= start;
                    //@ requires end <= arr.length;
                    //@ assignable arr[*];
                    public void fill(int[] arr, int start, int end, int value) {
                        //@ loop_invariant i >= start && i <= end;
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
                    //@ requires arr != null;
                    //@ ensures \\result >= -1;
                    //@ ensures \\result < arr.length;
                    public int indexOf(int[] arr, int target) {
                        //@ loop_invariant i >= 0 && i <= arr.length;
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
                    //@ requires n >= 0;
                    //@ requires n <= 12;
                    //@ ensures \\result >= 1;
                    public int factorial(int n) {
                        int result = 1;
                        //@ loop_invariant i >= 1 && i <= n + 1;
                        //@ loop_invariant result >= 1;
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
    @DisplayName("GCD: both params positive with while loop")
    void gcdPrecondition() throws IOException {
        String source = """
                public class GCDPrecondition {
                    //@ requires a > 0;
                    //@ requires b > 0;
                    //@ ensures \\result > 0;
                    public int gcd(int a, int b) {
                        //@ loop_invariant a > 0 && b > 0;
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
        assertVerified(inferAndVerify(source, "GCDPrecondition", "gcd"));
    }

    @Test
    @DisplayName("Power: base and exponent constraints")
    void powerPrecondition() throws IOException {
        String source = """
                public class PowerPrecondition {
                    //@ requires exp >= 0;
                    //@ ensures \\result >= 0 || base < 0;
                    public int power(int base, int exp) {
                        int result = 1;
                        //@ loop_invariant i >= 0 && i <= exp;
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
                    //@ requires this.data != null;
                    //@ requires this.data.length > 0;
                    //@ requires this.size < this.data.length;
                    //@ requires this.tail >= 0;
                    //@ requires this.tail < this.data.length;
                    //@ assignable this.data[this.tail], this.tail, this.size;
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
                    //@ requires a != null;
                    //@ requires b != null;
                    //@ requires result != null;
                    //@ requires result.length >= a.length + b.length;
                    //@ assignable result[*];
                    public void merge(int[] a, int[] b, int[] result) {
                        int i = 0, j = 0, k = 0;
                        //@ loop_invariant i >= 0 && i <= a.length;
                        //@ loop_invariant j >= 0 && j <= b.length;
                        //@ loop_invariant k >= 0 && k <= result.length;
                        //@ loop_invariant k == i + j;
                        while (i < a.length && j < b.length) {
                            if (a[i] <= b[j]) {
                                result[k++] = a[i++];
                            } else {
                                result[k++] = b[j++];
                            }
                        }
                        //@ loop_invariant i >= 0 && i <= a.length;
                        //@ loop_invariant k >= 0 && k <= result.length;
                        while (i < a.length) {
                            result[k++] = a[i++];
                        }
                        //@ loop_invariant j >= 0 && j <= b.length;
                        //@ loop_invariant k >= 0 && k <= result.length;
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
                    //@ requires b != 0;
                    //@ requires c != 0;
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
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    //@ requires shift >= 0;
                    //@ requires shift < arr.length;
                    //@ ensures \\result != null;
                    //@ ensures \\result.length == arr.length;
                    public int[] rotate(int[] arr, int shift) {
                        int n = arr.length;
                        int[] result = new int[n];
                        //@ loop_invariant i >= 0 && i <= n;
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
