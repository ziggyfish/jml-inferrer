package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Tier 1 formal verification tests for loop invariant specifications.
 * Each test writes JML comment syntax directly and invokes OpenJML ESC.
 */
class LoopInvariantVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Basic for-loop invariants
    // =========================================================================

    @Test
    @DisplayName("For loop lower bound: loop_invariant i >= 0")
    void forLoopLowerBound() throws IOException {
        String source = """
                public class ForLoopLowerBound {
                    //@ requires n >= 0;
                    public void count(int n) {
                        //@ loop_invariant i >= 0;
                        //@ loop_invariant i <= n;
                        for (int i = 0; i < n; i++) {
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ForLoopLowerBound", "count"));
    }

    @Test
    @DisplayName("For loop upper bound: loop_invariant i <= arr.length")
    void forLoopUpperBound() throws IOException {
        String source = """
                public class ForLoopUpperBound {
                    //@ requires arr != null;
                    public void iterate(int[] arr) {
                        //@ loop_invariant i >= 0;
                        //@ loop_invariant i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ForLoopUpperBound", "iterate"));
    }

    @Test
    @DisplayName("For loop both bounds: loop_invariant i >= 0 && i <= n")
    void forLoopBothBounds() throws IOException {
        String source = """
                public class ForLoopBothBounds {
                    //@ requires n >= 0;
                    public void count(int n) {
                        //@ loop_invariant i >= 0 && i <= n;
                        for (int i = 0; i < n; i++) {
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ForLoopBothBounds", "count"));
    }

    @Test
    @DisplayName("Countdown loop: loop_invariant i >= 0 && i <= n")
    void countdownLoop() throws IOException {
        String source = """
                public class CountdownLoop {
                    //@ requires n >= 0;
                    public void countdown(int n) {
                        //@ loop_invariant i >= 0 && i <= n;
                        for (int i = n; i > 0; i--) {
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CountdownLoop", "countdown"));
    }

    @Test
    @DisplayName("Step-by-two loop: invariant i >= 0")
    void stepByTwoLoop() throws IOException {
        String source = """
                public class StepByTwoLoop {
                    //@ requires n >= 0;
                    public void stepTwo(int n) {
                        //@ loop_invariant i >= 0;
                        //@ loop_invariant i <= n + 1;
                        for (int i = 0; i < n; i += 2) {
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StepByTwoLoop", "stepTwo"));
    }

    @Test
    @DisplayName("Loop starting at offset: invariant i >= start")
    void loopFromOffset() throws IOException {
        String source = """
                public class LoopFromOffset {
                    //@ requires arr != null;
                    //@ requires start >= 0;
                    //@ requires start <= arr.length;
                    public void iterateFrom(int[] arr, int start) {
                        //@ loop_invariant i >= start && i <= arr.length;
                        for (int i = start; i < arr.length; i++) {
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopFromOffset", "iterateFrom"));
    }

    // =========================================================================
    // While loop invariants
    // =========================================================================

    @Test
    @DisplayName("While loop bound: loop_invariant i >= 0 && i <= n")
    void whileLoopBound() throws IOException {
        String source = """
                public class WhileLoopBound {
                    //@ requires n >= 0;
                    public void count(int n) {
                        int i = 0;
                        //@ loop_invariant i >= 0 && i <= n;
                        while (i < n) {
                            i++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "WhileLoopBound", "count"));
    }

    @Test
    @DisplayName("While countdown: decrement to zero")
    void whileCountdown() throws IOException {
        String source = """
                public class WhileCountdown {
                    //@ requires n >= 0;
                    public void countdown(int n) {
                        int i = n;
                        //@ loop_invariant i >= 0 && i <= n;
                        while (i > 0) {
                            i--;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "WhileCountdown", "countdown"));
    }

    @Test
    @DisplayName("While with two pointers converging")
    void whileTwoPointers() throws IOException {
        String source = """
                public class WhileTwoPointers {
                    //@ requires n >= 0;
                    public void converge(int n) {
                        int lo = 0;
                        int hi = n;
                        //@ loop_invariant lo >= 0;
                        //@ loop_invariant hi >= 0 && hi <= n;
                        //@ loop_invariant lo <= hi + 1;
                        while (lo < hi) {
                            lo++;
                            hi--;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "WhileTwoPointers", "converge"));
    }

    @Test
    @DisplayName("While halving: n decreases toward zero")
    void whileHalving() throws IOException {
        String source = """
                public class WhileHalving {
                    //@ requires n >= 0;
                    //@ ensures \\result >= 0;
                    public int countHalves(int n) {
                        int count = 0;
                        int val = n;
                        //@ loop_invariant val >= 0;
                        //@ loop_invariant count >= 0;
                        while (val > 0) {
                            val = val / 2;
                            count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "WhileHalving", "countHalves"));
    }

    // =========================================================================
    // Accumulator invariants
    // =========================================================================

    @Test
    @DisplayName("Accumulator invariant: loop index bounds during summation")
    void accumulatorInvariant() throws IOException {
        String source = """
                public class AccumulatorInvariant {
                    //@ requires arr != null;
                    public int sum(int[] arr) {
                        int sum = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AccumulatorInvariant", "sum"));
    }

    @Test
    @DisplayName("Product accumulator: index bounds during multiplication")
    void productAccumulator() throws IOException {
        String source = """
                public class ProductAccumulator {
                    //@ requires arr != null;
                    public int product(int[] arr) {
                        int prod = 1;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            prod *= arr[i];
                        }
                        return prod;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ProductAccumulator", "product"));
    }

    @Test
    @DisplayName("Counter accumulator: count >= 0 invariant")
    void counterAccumulator() throws IOException {
        String source = """
                public class CounterAccumulator {
                    //@ requires arr != null;
                    //@ ensures \\result >= 0;
                    //@ ensures \\result <= arr.length;
                    public int countPositive(int[] arr) {
                        int count = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        //@ loop_invariant count >= 0 && count <= i;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CounterAccumulator", "countPositive"));
    }

    @Test
    @DisplayName("Running max: max tracks largest seen element")
    void runningMax() throws IOException {
        String source = """
                public class RunningMax {
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    public int max(int[] arr) {
                        int max = arr[0];
                        //@ loop_invariant i >= 1 && i <= arr.length;
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] > max) max = arr[i];
                        }
                        return max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RunningMax", "max"));
    }

    @Test
    @DisplayName("Running min: min tracks smallest seen element")
    void runningMin() throws IOException {
        String source = """
                public class RunningMin {
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    public int min(int[] arr) {
                        int min = arr[0];
                        //@ loop_invariant i >= 1 && i <= arr.length;
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] < min) min = arr[i];
                        }
                        return min;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RunningMin", "min"));
    }

    // =========================================================================
    // Nested loop invariants
    // =========================================================================

    @Test
    @DisplayName("Nested loop bounds: both outer and inner invariants")
    void nestedLoopBounds() throws IOException {
        String source = """
                public class NestedLoopBounds {
                    //@ requires rows >= 0;
                    //@ requires cols >= 0;
                    public int countCells(int rows, int cols) {
                        int count = 0;
                        //@ loop_invariant i >= 0 && i <= rows;
                        for (int i = 0; i < rows; i++) {
                            //@ loop_invariant j >= 0 && j <= cols;
                            for (int j = 0; j < cols; j++) {
                                count++;
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NestedLoopBounds", "countCells"));
    }

    @Test
    @DisplayName("Nested loop with 2D array access")
    void nestedLoop2DArray() throws IOException {
        String source = """
                public class NestedLoop2DArray {
                    //@ requires matrix != null;
                    //@ requires matrix.length > 0;
                    //@ requires cols > 0;
                    //@ requires matrix.length >= rows * cols;
                    //@ requires rows >= 0;
                    public int sumMatrix(int[] matrix, int rows, int cols) {
                        int sum = 0;
                        //@ loop_invariant i >= 0 && i <= rows;
                        for (int i = 0; i < rows; i++) {
                            //@ loop_invariant j >= 0 && j <= cols;
                            for (int j = 0; j < cols; j++) {
                                sum += matrix[i * cols + j];
                            }
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NestedLoop2DArray", "sumMatrix"));
    }

    @Test
    @DisplayName("Triple nested loop: 3D counting")
    void tripleNestedLoop() throws IOException {
        String source = """
                public class TripleNestedLoop {
                    //@ requires x >= 0;
                    //@ requires y >= 0;
                    //@ requires z >= 0;
                    public int countTriple(int x, int y, int z) {
                        int count = 0;
                        //@ loop_invariant i >= 0 && i <= x;
                        for (int i = 0; i < x; i++) {
                            //@ loop_invariant j >= 0 && j <= y;
                            for (int j = 0; j < y; j++) {
                                //@ loop_invariant k >= 0 && k <= z;
                                for (int k = 0; k < z; k++) {
                                    count++;
                                }
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TripleNestedLoop", "countTriple"));
    }

    // =========================================================================
    // Complex: loops with conditionals
    // =========================================================================

    @Test
    @DisplayName("Loop with conditional accumulation: sum positives only")
    void loopConditionalAccumulation() throws IOException {
        String source = """
                public class LoopConditionalAccumulation {
                    //@ requires arr != null;
                    //@ ensures \\result >= 0;
                    public int sumPositives(int[] arr) {
                        int sum = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        //@ loop_invariant sum >= 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopConditionalAccumulation", "sumPositives"));
    }

    @Test
    @DisplayName("Loop with early exit: find first negative index")
    void loopEarlyExit() throws IOException {
        String source = """
                public class LoopEarlyExit {
                    //@ requires arr != null;
                    //@ ensures \\result >= -1;
                    //@ ensures \\result < arr.length;
                    public int findFirstNegative(int[] arr) {
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < 0) return i;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopEarlyExit", "findFirstNegative"));
    }

    @Test
    @DisplayName("Loop with flag: tracks whether condition met")
    void loopWithFlag() throws IOException {
        String source = """
                public class LoopWithFlag {
                    //@ requires arr != null;
                    public boolean hasZero(int[] arr) {
                        boolean found = false;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == 0) found = true;
                        }
                        return found;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopWithFlag", "hasZero"));
    }

    @Test
    @DisplayName("Loop computing absolute values into new array")
    void loopAbsoluteValues() throws IOException {
        String source = """
                public class LoopAbsoluteValues {
                    //@ requires arr != null;
                    //@ ensures \\result != null;
                    //@ ensures \\result.length == arr.length;
                    public int[] absArray(int[] arr) {
                        int[] result = new int[arr.length];
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            result[i] = arr[i] >= 0 ? arr[i] : -arr[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopAbsoluteValues", "absArray"));
    }

    // =========================================================================
    // Complex: loops with field mutations
    // =========================================================================

    @Test
    @DisplayName("Loop increments field: size grows with loop")
    void loopIncrementsField() throws IOException {
        String source = """
                public class LoopIncrementsField {
                    int size;
                    //@ requires n >= 0;
                    //@ assignable this.size;
                    //@ ensures this.size == \\old(this.size) + n;
                    public void growBy(int n) {
                        //@ loop_invariant i >= 0 && i <= n;
                        //@ loop_invariant this.size == \\old(this.size) + i;
                        for (int i = 0; i < n; i++) {
                            this.size++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopIncrementsField", "growBy"));
    }

    @Test
    @DisplayName("Loop fills array field: zero-init internal storage")
    void loopFillsArrayField() throws IOException {
        String source = """
                public class LoopFillsArrayField {
                    int[] data;
                    //@ requires this.data != null;
                    //@ assignable this.data[*];
                    public void clear() {
                        //@ loop_invariant i >= 0 && i <= this.data.length;
                        for (int i = 0; i < this.data.length; i++) {
                            this.data[i] = 0;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopFillsArrayField", "clear"));
    }

    // =========================================================================
    // Complex: algorithmic loops
    // =========================================================================

    @Test
    @DisplayName("Binary search loop: lo/hi bounds maintained")
    void binarySearchLoop() throws IOException {
        String source = """
                public class BinarySearchLoop {
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    //@ ensures \\result >= -1;
                    //@ ensures \\result < arr.length;
                    public int search(int[] arr, int target) {
                        int lo = 0;
                        int hi = arr.length - 1;
                        //@ loop_invariant lo >= 0;
                        //@ loop_invariant hi < arr.length;
                        while (lo <= hi) {
                            int mid = lo + (hi - lo) / 2;
                            if (arr[mid] == target) return mid;
                            if (arr[mid] < target) lo = mid + 1;
                            else hi = mid - 1;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BinarySearchLoop", "search"));
    }

    @Test
    @DisplayName("Reverse array with loop: two pointer bounds")
    void reverseArrayLoop() throws IOException {
        String source = """
                public class ReverseArrayLoop {
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
        assertVerified(inferAndVerify(source, "ReverseArrayLoop", "reverse"));
    }

    @Test
    @DisplayName("Selection sort inner loop: find minimum in subarray")
    void selectionSortInnerLoop() throws IOException {
        String source = """
                public class SelectionSortInnerLoop {
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    //@ assignable arr[*];
                    public void sort(int[] arr) {
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length - 1; i++) {
                            int minIdx = i;
                            //@ loop_invariant j >= i + 1 && j <= arr.length;
                            //@ loop_invariant minIdx >= i && minIdx < arr.length;
                            for (int j = i + 1; j < arr.length; j++) {
                                if (arr[j] < arr[minIdx]) {
                                    minIdx = j;
                                }
                            }
                            int tmp = arr[i];
                            arr[i] = arr[minIdx];
                            arr[minIdx] = tmp;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SelectionSortInnerLoop", "sort"));
    }

    @Test
    @DisplayName("Partition loop: Dutch national flag two-pointer")
    void partitionLoop() throws IOException {
        String source = """
                public class PartitionLoop {
                    //@ requires arr != null;
                    //@ requires arr.length > 0;
                    //@ assignable arr[*];
                    //@ ensures \\result >= 0 && \\result < arr.length;
                    public int partition(int[] arr, int pivot) {
                        int lo = 0;
                        int hi = arr.length - 1;
                        //@ loop_invariant lo >= 0 && lo <= arr.length;
                        //@ loop_invariant hi >= -1 && hi < arr.length;
                        while (lo <= hi) {
                            if (arr[lo] <= pivot) {
                                lo++;
                            } else {
                                int tmp = arr[lo];
                                arr[lo] = arr[hi];
                                arr[hi] = tmp;
                                hi--;
                            }
                        }
                        return lo > 0 ? lo - 1 : 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PartitionLoop", "partition"));
    }

    @Test
    @DisplayName("Copy range with loop: src and dst bounds maintained")
    void copyRangeLoop() throws IOException {
        String source = """
                public class CopyRangeLoop {
                    //@ requires src != null;
                    //@ requires dst != null;
                    //@ requires from >= 0;
                    //@ requires to >= from;
                    //@ requires to <= src.length;
                    //@ requires dst.length >= to - from;
                    //@ assignable dst[*];
                    public void copyRange(int[] src, int[] dst, int from, int to) {
                        //@ loop_invariant i >= from && i <= to;
                        for (int i = from; i < to; i++) {
                            dst[i - from] = src[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CopyRangeLoop", "copyRange"));
    }

    @Test
    @DisplayName("GCD loop: both values remain positive")
    void gcdLoop() throws IOException {
        String source = """
                public class GCDLoop {
                    //@ requires a > 0;
                    //@ requires b > 0;
                    //@ ensures \\result > 0;
                    public int gcd(int a, int b) {
                        //@ loop_invariant a > 0 && b > 0;
                        while (a != b) {
                            if (a > b) a = a - b;
                            else b = b - a;
                        }
                        return a;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GCDLoop", "gcd"));
    }

    @Test
    @DisplayName("Factorial loop: result stays positive")
    void factorialLoop() throws IOException {
        String source = """
                public class FactorialLoop {
                    public int factorial(int n) {
                        int result = 1;
                        for (int i = 1; i <= n; i++) {
                            result *= i;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FactorialLoop", "factorial"));
    }

    @Test
    @DisplayName("Power loop: exponent counted down correctly")
    void powerLoop() throws IOException {
        String source = """
                public class PowerLoop {
                    public int power(int base, int exp) {
                        int result = 1;
                        for (int i = 0; i < exp; i++) {
                            result *= base;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PowerLoop", "power"));
    }

    @Test
    @DisplayName("Merge loop: three index variables bounded")
    void mergeLoop() throws IOException {
        String source = """
                public class MergeLoop {
                    public void merge(int[] a, int[] b, int[] out) {
                        int i = 0, j = 0, k = 0;
                        while (i < a.length && j < b.length) {
                            if (a[i] <= b[j]) {
                                out[k++] = a[i++];
                            } else {
                                out[k++] = b[j++];
                            }
                        }
                        while (i < a.length) out[k++] = a[i++];
                        while (j < b.length) out[k++] = b[j++];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MergeLoop", "merge"));
    }

    @Test
    @DisplayName("Prefix sum: accumulating loop with array write")
    void prefixSum() throws IOException {
        String source = """
                public class PrefixSum {
                    public void prefixSum(int[] arr) {
                        for (int i = 1; i < arr.length; i++) {
                            arr[i] = arr[i] + arr[i - 1];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PrefixSum", "prefixSum"));
    }
}
