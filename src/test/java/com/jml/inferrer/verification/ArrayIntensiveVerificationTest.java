package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for array-intensive operations: multi-array coordination,
 * in-place transformations, sliding windows, and 2D array operations.
 */
class ArrayIntensiveVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Two-array operations
    // =========================================================================

    @Test
    @DisplayName("Element-wise addition of two arrays")
    void elementWiseAdd() throws IOException {
        String source = """
                public class ArrayMath {
                    public int[] add(int[] a, int[] b) {
                        if (a == null || b == null) throw new IllegalArgumentException();
                        if (a.length != b.length) throw new IllegalArgumentException();
                        int[] result = new int[a.length];
                        for (int i = 0; i < a.length; i++) {
                            result[i] = a[i] + b[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayMath", "add"));
    }

    @Test
    @DisplayName("Dot product of two arrays")
    void dotProduct() throws IOException {
        String source = """
                public class ArrayMath2 {
                    public int dotProduct(int[] a, int[] b) {
                        if (a == null || b == null) throw new IllegalArgumentException();
                        if (a.length != b.length) throw new IllegalArgumentException();
                        int sum = 0;
                        for (int i = 0; i < a.length; i++) {
                            sum += a[i] * b[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayMath2", "dotProduct"));
    }

    @Test
    @DisplayName("Copy source array to destination")
    void arrayCopy() throws IOException {
        String source = """
                public class ArrayCopy {
                    public void copy(int[] src, int[] dst) {
                        if (src == null || dst == null) throw new IllegalArgumentException();
                        if (dst.length < src.length) throw new IllegalArgumentException();
                        for (int i = 0; i < src.length; i++) {
                            dst[i] = src[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayCopy", "copy"));
    }

    @Test
    @DisplayName("Merge two sorted arrays into new array")
    void mergeSortedArrays() throws IOException {
        String source = """
                public class ArrayMerge {
                    public int[] merge(int[] a, int[] b) {
                        if (a == null || b == null) throw new IllegalArgumentException();
                        int[] result = new int[a.length + b.length];
                        int i = 0, j = 0, k = 0;
                        while (i < a.length && j < b.length) {
                            if (a[i] <= b[j]) {
                                result[k] = a[i];
                                i++;
                            } else {
                                result[k] = b[j];
                                j++;
                            }
                            k++;
                        }
                        while (i < a.length) {
                            result[k] = a[i];
                            i++;
                            k++;
                        }
                        while (j < b.length) {
                            result[k] = b[j];
                            j++;
                            k++;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayMerge", "merge"));
    }

    @Test
    @DisplayName("Check if two arrays are equal")
    void arraysEqual() throws IOException {
        String source = """
                public class ArrayEquals {
                    public boolean areEqual(int[] a, int[] b) {
                        if (a == null || b == null) throw new IllegalArgumentException();
                        if (a.length != b.length) return false;
                        for (int i = 0; i < a.length; i++) {
                            if (a[i] != b[i]) return false;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayEquals", "areEqual"));
    }

    // =========================================================================
    // In-place array transformations
    // =========================================================================

    @Test
    @DisplayName("Reverse array in-place")
    void reverseInPlace() throws IOException {
        String source = """
                public class ArrayReverse {
                    public void reverse(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int left = 0;
                        int right = arr.length - 1;
                        while (left < right) {
                            int temp = arr[left];
                            arr[left] = arr[right];
                            arr[right] = temp;
                            left++;
                            right--;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayReverse", "reverse"));
    }

    @Test
    @DisplayName("Negate all elements in-place")
    void negateInPlace() throws IOException {
        String source = """
                public class ArrayNegate {
                    public void negate(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            arr[i] = -arr[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayNegate", "negate"));
    }

    @Test
    @DisplayName("Shift all elements left by one, last becomes zero")
    void shiftLeft() throws IOException {
        String source = """
                public class ArrayShift {
                    public void shiftLeft(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (arr.length == 0) return;
                        for (int i = 0; i < arr.length - 1; i++) {
                            arr[i] = arr[i + 1];
                        }
                        arr[arr.length - 1] = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayShift", "shiftLeft"));
    }

    @Test
    @DisplayName("Replace negative values with zero")
    void replaceNegatives() throws IOException {
        String source = """
                public class ArrayClean {
                    public void replaceNegatives(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < 0) arr[i] = 0;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayClean", "replaceNegatives"));
    }

    @Test
    @DisplayName("Cumulative sum in-place")
    void cumulativeSumInPlace() throws IOException {
        String source = """
                public class CumulativeSum {
                    public void cumulativeSum(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 1; i < arr.length; i++) {
                            arr[i] += arr[i - 1];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CumulativeSum", "cumulativeSum"));
    }

    // =========================================================================
    // Sliding window / subarray
    // =========================================================================

    @Test
    @DisplayName("Sum of subarray from start to end")
    void subarraySum() throws IOException {
        String source = """
                public class SubarraySum {
                    public int sum(int[] arr, int start, int end) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (start < 0 || end > arr.length || start > end) throw new IndexOutOfBoundsException();
                        int sum = 0;
                        for (int i = start; i < end; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SubarraySum", "sum"));
    }

    @Test
    @DisplayName("Find maximum in subarray")
    void subarrayMax() throws IOException {
        String source = """
                public class SubarrayMax {
                    public int max(int[] arr, int start, int end) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (start < 0 || end > arr.length || start >= end) throw new IllegalArgumentException();
                        int max = arr[start];
                        for (int i = start + 1; i < end; i++) {
                            if (arr[i] > max) max = arr[i];
                        }
                        return max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SubarrayMax", "max"));
    }

    @Test
    @DisplayName("Count elements matching condition in subarray")
    void countInRange() throws IOException {
        String source = """
                public class CountRange {
                    public int countPositive(int[] arr, int from, int to) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (from < 0 || to > arr.length) throw new IndexOutOfBoundsException();
                        int count = 0;
                        for (int i = from; i < to; i++) {
                            if (arr[i] > 0) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CountRange", "countPositive"));
    }

    // =========================================================================
    // 2D array operations
    // =========================================================================

    @Test
    @DisplayName("Initialize 2D array with identity matrix pattern")
    void identityMatrix() throws IOException {
        String source = """
                public class MatrixInit {
                    public int[][] identity(int n) {
                        if (n <= 0) throw new IllegalArgumentException();
                        int[][] matrix = new int[n][n];
                        for (int i = 0; i < n; i++) {
                            matrix[i][i] = 1;
                        }
                        return matrix;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MatrixInit", "identity"));
    }

    @Test
    @DisplayName("Transpose square matrix in-place")
    void transposeInPlace() throws IOException {
        String source = """
                public class MatrixTranspose {
                    public void transpose(int[][] matrix, int n) {
                        if (matrix == null) throw new IllegalArgumentException();
                        for (int i = 0; i < n; i++) {
                            for (int j = i + 1; j < n; j++) {
                                int temp = matrix[i][j];
                                matrix[i][j] = matrix[j][i];
                                matrix[j][i] = temp;
                            }
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MatrixTranspose", "transpose"));
    }

    @Test
    @DisplayName("Matrix-vector multiply")
    void matrixVectorMultiply() throws IOException {
        String source = """
                public class MatVecMul {
                    public int[] multiply(int[][] mat, int[] vec, int rows, int cols) {
                        if (mat == null || vec == null) throw new IllegalArgumentException();
                        if (vec.length != cols) throw new IllegalArgumentException();
                        int[] result = new int[rows];
                        for (int i = 0; i < rows; i++) {
                            int sum = 0;
                            for (int j = 0; j < cols; j++) {
                                sum += mat[i][j] * vec[j];
                            }
                            result[i] = sum;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MatVecMul", "multiply"));
    }

    @Test
    @DisplayName("Sum all elements of 2D array")
    void sum2D() throws IOException {
        String source = """
                public class Matrix2DSum {
                    public int sumAll(int[][] matrix) {
                        if (matrix == null) throw new IllegalArgumentException();
                        int total = 0;
                        for (int i = 0; i < matrix.length; i++) {
                            if (matrix[i] == null) throw new IllegalArgumentException();
                            for (int j = 0; j < matrix[i].length; j++) {
                                total += matrix[i][j];
                            }
                        }
                        return total;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Matrix2DSum", "sumAll"));
    }

    // =========================================================================
    // Array with field interaction
    // =========================================================================

    @Test
    @DisplayName("Dynamic array: add element, update size field")
    void dynamicArrayAdd() throws IOException {
        String source = """
                public class DynArray {
                    private int[] data;
                    private int size;
                    public void add(int value) {
                        if (size >= data.length) throw new IllegalStateException();
                        data[size] = value;
                        size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DynArray", "add"));
    }

    @Test
    @DisplayName("Dynamic array: remove last element")
    void dynamicArrayRemoveLast() throws IOException {
        String source = """
                public class DynArray2 {
                    private int[] data;
                    private int size;
                    public int removeLast() {
                        if (size <= 0) throw new IllegalStateException();
                        size--;
                        return data[size];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DynArray2", "removeLast"));
    }

    @Test
    @DisplayName("Dynamic array: get with bounds check")
    void dynamicArrayGet() throws IOException {
        String source = """
                public class DynArray3 {
                    private int[] data;
                    private int size;
                    public int get(int index) {
                        if (index < 0 || index >= size) throw new IndexOutOfBoundsException();
                        return data[index];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DynArray3", "get"));
    }

    @Test
    @DisplayName("Dynamic array: clear resets size but keeps data")
    void dynamicArrayClear() throws IOException {
        String source = """
                public class DynArray4 {
                    private int size;
                    public void clear() {
                        size = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DynArray4", "clear"));
    }

    @Test
    @DisplayName("Dynamic array: contains via linear scan")
    void dynamicArrayContains() throws IOException {
        String source = """
                public class DynArray5 {
                    private int[] data;
                    private int size;
                    public boolean contains(int value) {
                        for (int i = 0; i < size; i++) {
                            if (data[i] == value) return true;
                        }
                        return false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DynArray5", "contains"));
    }

    // =========================================================================
    // Histogram / frequency counting
    // =========================================================================

    @Test
    @DisplayName("Count frequency of each element (values 0-9)")
    void frequencyCount() throws IOException {
        String source = """
                public class Histogram {
                    public int[] countFrequency(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int[] freq = new int[10];
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] >= 0 && arr[i] < 10) {
                                freq[arr[i]]++;
                            }
                        }
                        return freq;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Histogram", "countFrequency"));
    }

    @Test
    @DisplayName("Find most frequent element index")
    void findMostFrequent() throws IOException {
        String source = """
                public class FreqFinder {
                    public int findMaxIndex(int[] freq) {
                        if (freq == null || freq.length == 0) throw new IllegalArgumentException();
                        int maxIdx = 0;
                        for (int i = 1; i < freq.length; i++) {
                            if (freq[i] > freq[maxIdx]) maxIdx = i;
                        }
                        return maxIdx;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FreqFinder", "findMaxIndex"));
    }
}
