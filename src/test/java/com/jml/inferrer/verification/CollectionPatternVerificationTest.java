package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for collection-like patterns: array creation with constraints,
 * filtering into new arrays, size tracking, and collection-style operations.
 */
class CollectionPatternVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Array creation with size constraints
    // =========================================================================

    @Test
    @DisplayName("Collection: create array of same length as input")
    void createSameLength() throws IOException {
        String source = """
                public class ArrCreate1 {
                    public int[] duplicate(int[] src) {
                        if (src == null) throw new IllegalArgumentException();
                        int[] result = new int[src.length];
                        for (int i = 0; i < src.length; i++) {
                            result[i] = src[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCreate1", "duplicate"));
    }

    @Test
    @DisplayName("Collection: create array of double length")
    void createDoubleLength() throws IOException {
        String source = """
                public class ArrCreate2 {
                    public int[] doubleCapacity(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int[] result = new int[arr.length * 2];
                        for (int i = 0; i < arr.length; i++) {
                            result[i] = arr[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCreate2", "doubleCapacity"));
    }

    @Test
    @DisplayName("Collection: create zero-filled array of given size")
    void createZeroFilled() throws IOException {
        String source = """
                public class ArrCreate3 {
                    public int[] zeros(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        return new int[n];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCreate3", "zeros"));
    }

    @Test
    @DisplayName("Collection: create array filled with value")
    void createFilled() throws IOException {
        String source = """
                public class ArrCreate4 {
                    public int[] fill(int n, int value) {
                        if (n < 0) throw new IllegalArgumentException();
                        int[] result = new int[n];
                        for (int i = 0; i < n; i++) {
                            result[i] = value;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCreate4", "fill"));
    }

    // =========================================================================
    // Filter patterns (subset of input)
    // =========================================================================

    @Test
    @DisplayName("Collection: filter even numbers from array")
    void filterEven() throws IOException {
        String source = """
                public class ArrFilter1 {
                    public int countEven(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] % 2 == 0) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrFilter1", "countEven"));
    }

    @Test
    @DisplayName("Collection: filter values above threshold")
    void filterAboveThreshold() throws IOException {
        String source = """
                public class ArrFilter2 {
                    public int countAbove(int[] arr, int threshold) {
                        if (arr == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > threshold) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrFilter2", "countAbove"));
    }

    @Test
    @DisplayName("Collection: check all elements positive")
    void allPositive() throws IOException {
        String source = """
                public class ArrCheck1 {
                    public boolean allPositive(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] <= 0) return false;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCheck1", "allPositive"));
    }

    @Test
    @DisplayName("Collection: check any element matches")
    void anyMatches() throws IOException {
        String source = """
                public class ArrCheck2 {
                    public boolean anyNegative(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < 0) return true;
                        }
                        return false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCheck2", "anyNegative"));
    }

    @Test
    @DisplayName("Collection: check no duplicates (brute force)")
    void noDuplicates() throws IOException {
        String source = """
                public class ArrCheck3 {
                    public boolean hasNoDuplicates(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            for (int j = i + 1; j < arr.length; j++) {
                                if (arr[i] == arr[j]) return false;
                            }
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrCheck3", "hasNoDuplicates"));
    }

    // =========================================================================
    // Map-like transformations
    // =========================================================================

    @Test
    @DisplayName("Collection: map each element through a formula")
    void mapFormula() throws IOException {
        String source = """
                public class ArrMap1 {
                    public int[] doubleAll(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int[] result = new int[arr.length];
                        for (int i = 0; i < arr.length; i++) {
                            result[i] = arr[i] * 2;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrMap1", "doubleAll"));
    }

    @Test
    @DisplayName("Collection: map to absolute values")
    void mapAbsoluteValues() throws IOException {
        String source = """
                public class ArrMap2 {
                    public int[] absAll(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int[] result = new int[arr.length];
                        for (int i = 0; i < arr.length; i++) {
                            result[i] = arr[i] < 0 ? -arr[i] : arr[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrMap2", "absAll"));
    }

    @Test
    @DisplayName("Collection: map to boolean flags")
    void mapToFlags() throws IOException {
        String source = """
                public class ArrMap3 {
                    public boolean[] isPositive(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        boolean[] flags = new boolean[arr.length];
                        for (int i = 0; i < arr.length; i++) {
                            flags[i] = arr[i] > 0;
                        }
                        return flags;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrMap3", "isPositive"));
    }

    // =========================================================================
    // Reduce / aggregate patterns
    // =========================================================================

    @Test
    @DisplayName("Collection: reduce to sum")
    void reduceSum() throws IOException {
        String source = """
                public class ArrReduce1 {
                    public long sum(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        long sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrReduce1", "sum"));
    }

    @Test
    @DisplayName("Collection: reduce to product")
    void reduceProduct() throws IOException {
        String source = """
                public class ArrReduce2 {
                    public long product(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (arr.length == 0) return 0;
                        long prod = 1;
                        for (int i = 0; i < arr.length; i++) {
                            prod *= arr[i];
                        }
                        return prod;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrReduce2", "product"));
    }

    @Test
    @DisplayName("Collection: find index of maximum")
    void findMaxIndex() throws IOException {
        String source = """
                public class ArrReduce3 {
                    public int maxIndex(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int maxIdx = 0;
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] > arr[maxIdx]) maxIdx = i;
                        }
                        return maxIdx;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrReduce3", "maxIndex"));
    }

    @Test
    @DisplayName("Collection: find index of minimum")
    void findMinIndex() throws IOException {
        String source = """
                public class ArrReduce4 {
                    public int minIndex(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int minIdx = 0;
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] < arr[minIdx]) minIdx = i;
                        }
                        return minIdx;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrReduce4", "minIndex"));
    }

    // =========================================================================
    // Partition / grouping patterns
    // =========================================================================

    @Test
    @DisplayName("Collection: partition array around pivot")
    void partitionAroundPivot() throws IOException {
        String source = """
                public class ArrPartition1 {
                    public int partition(int[] arr, int pivotValue) {
                        if (arr == null) throw new IllegalArgumentException();
                        int writeIdx = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < pivotValue) {
                                int temp = arr[writeIdx];
                                arr[writeIdx] = arr[i];
                                arr[i] = temp;
                                writeIdx++;
                            }
                        }
                        return writeIdx;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrPartition1", "partition"));
    }

    @Test
    @DisplayName("Collection: stable partition preserving order")
    void stablePartition() throws IOException {
        String source = """
                public class ArrPartition2 {
                    public int[] extractNonZero(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] != 0) count++;
                        }
                        int[] result = new int[count];
                        int idx = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] != 0) {
                                result[idx] = arr[i];
                                idx++;
                            }
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrPartition2", "extractNonZero"));
    }

    // =========================================================================
    // Size tracking with field
    // =========================================================================

    @Test
    @DisplayName("Collection: track element count with field")
    void trackElementCount() throws IOException {
        String source = """
                public class Tracked1 {
                    private int[] items;
                    private int count;
                    public void addAll(int[] values) {
                        if (values == null) throw new IllegalArgumentException();
                        for (int i = 0; i < values.length; i++) {
                            if (count >= items.length) break;
                            items[count] = values[i];
                            count++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Tracked1", "addAll"));
    }

    @Test
    @DisplayName("Collection: swap two elements by index")
    void swapByIndex() throws IOException {
        String source = """
                public class ArrSwap1 {
                    public void swap(int[] arr, int i, int j) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (i < 0 || i >= arr.length) throw new IndexOutOfBoundsException();
                        if (j < 0 || j >= arr.length) throw new IndexOutOfBoundsException();
                        int temp = arr[i];
                        arr[i] = arr[j];
                        arr[j] = temp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrSwap1", "swap"));
    }
}
