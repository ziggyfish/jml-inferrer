package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for data structure operations: stacks, queues,
 * linked lists, circular buffers, and custom collections.
 */
class DataStructureVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Array-backed stack operations
    // =========================================================================

    @Test
    @DisplayName("Stack: push increments top and stores element")
    void stackPush() throws IOException {
        String source = """
                public class ArrayStack {
                    private int[] data;
                    private int top;
                    public void push(int value) {
                        if (top >= data.length) throw new IllegalStateException();
                        data[top] = value;
                        top++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayStack", "push"));
    }

    @Test
    @DisplayName("Stack: pop decrements top and returns element")
    void stackPop() throws IOException {
        String source = """
                public class ArrayStack2 {
                    private int[] data;
                    private int top;
                    public int pop() {
                        if (top <= 0) throw new IllegalStateException();
                        top--;
                        return data[top];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayStack2", "pop"));
    }

    @Test
    @DisplayName("Stack: peek returns top element without modification")
    void stackPeek() throws IOException {
        String source = """
                public class ArrayStack3 {
                    private int[] data;
                    private int top;
                    public int peek() {
                        if (top <= 0) throw new IllegalStateException();
                        return data[top - 1];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayStack3", "peek"));
    }

    @Test
    @DisplayName("Stack: isEmpty checks top == 0")
    void stackIsEmpty() throws IOException {
        String source = """
                public class ArrayStack4 {
                    private int top;
                    public boolean isEmpty() {
                        return top == 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayStack4", "isEmpty"));
    }

    @Test
    @DisplayName("Stack: size returns top")
    void stackSize() throws IOException {
        String source = """
                public class ArrayStack5 {
                    private int top;
                    public int size() {
                        return top;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayStack5", "size"));
    }

    // =========================================================================
    // Circular buffer operations
    // =========================================================================

    @Test
    @DisplayName("Circular buffer: enqueue with wrap-around")
    void circularBufferEnqueue() throws IOException {
        String source = """
                public class CircularBuffer {
                    private int[] buffer;
                    private int head;
                    private int tail;
                    private int count;
                    public void enqueue(int value) {
                        if (count >= buffer.length) throw new IllegalStateException();
                        buffer[tail] = value;
                        tail = (tail + 1) % buffer.length;
                        count++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CircularBuffer", "enqueue"));
    }

    @Test
    @DisplayName("Circular buffer: dequeue with wrap-around")
    void circularBufferDequeue() throws IOException {
        String source = """
                public class CircularBuffer2 {
                    private int[] buffer;
                    private int head;
                    private int tail;
                    private int count;
                    public int dequeue() {
                        if (count <= 0) throw new IllegalStateException();
                        int value = buffer[head];
                        head = (head + 1) % buffer.length;
                        count--;
                        return value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CircularBuffer2", "dequeue"));
    }

    @Test
    @DisplayName("Circular buffer: isFull checks count == length")
    void circularBufferIsFull() throws IOException {
        String source = """
                public class CircularBuffer3 {
                    private int[] buffer;
                    private int count;
                    public boolean isFull() {
                        return count == buffer.length;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CircularBuffer3", "isFull"));
    }

    // =========================================================================
    // Matrix operations
    // =========================================================================

    @Test
    @DisplayName("Matrix: get element with bounds check")
    void matrixGet() throws IOException {
        String source = """
                public class Matrix {
                    private int[][] data;
                    private int rows;
                    private int cols;
                    public int get(int row, int col) {
                        if (row < 0 || row >= rows) throw new IndexOutOfBoundsException();
                        if (col < 0 || col >= cols) throw new IndexOutOfBoundsException();
                        return data[row][col];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Matrix", "get"));
    }

    @Test
    @DisplayName("Matrix: set element with bounds check")
    void matrixSet() throws IOException {
        String source = """
                public class Matrix2 {
                    private int[][] data;
                    private int rows;
                    private int cols;
                    public void set(int row, int col, int value) {
                        if (row < 0 || row >= rows) throw new IndexOutOfBoundsException();
                        if (col < 0 || col >= cols) throw new IndexOutOfBoundsException();
                        data[row][col] = value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Matrix2", "set"));
    }

    @Test
    @DisplayName("Matrix: row sum computation")
    void matrixRowSum() throws IOException {
        String source = """
                public class Matrix3 {
                    private int[][] data;
                    private int cols;
                    public int rowSum(int row) {
                        if (data == null) throw new IllegalStateException();
                        int sum = 0;
                        for (int j = 0; j < cols; j++) {
                            sum += data[row][j];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Matrix3", "rowSum"));
    }

    @Test
    @DisplayName("Matrix: trace (sum of diagonal)")
    void matrixTrace() throws IOException {
        String source = """
                public class Matrix4 {
                    private int[][] data;
                    private int size;
                    public int trace() {
                        int sum = 0;
                        for (int i = 0; i < size; i++) {
                            sum += data[i][i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Matrix4", "trace"));
    }

    // =========================================================================
    // Pair / tuple patterns
    // =========================================================================

    @Test
    @DisplayName("Pair: getFirst returns first field")
    void pairGetFirst() throws IOException {
        String source = """
                public class IntPair {
                    private int first;
                    private int second;
                    public int getFirst() {
                        return first;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "IntPair", "getFirst"));
    }

    @Test
    @DisplayName("Pair: swap fields")
    void pairSwap() throws IOException {
        String source = """
                public class IntPair2 {
                    private int first;
                    private int second;
                    public void swap() {
                        int temp = first;
                        first = second;
                        second = temp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "IntPair2", "swap"));
    }

    @Test
    @DisplayName("Pair: sum of both elements")
    void pairSum() throws IOException {
        String source = """
                public class IntPair3 {
                    private int first;
                    private int second;
                    public int sum() {
                        return first + second;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "IntPair3", "sum"));
    }

    // =========================================================================
    // Priority / sorted insert
    // =========================================================================

    @Test
    @DisplayName("Sorted array: find insertion point via binary search")
    void sortedInsertionPoint() throws IOException {
        String source = """
                public class SortedArray {
                    public int findInsertionPoint(int[] arr, int target) {
                        if (arr == null) throw new IllegalArgumentException();
                        int lo = 0;
                        int hi = arr.length;
                        while (lo < hi) {
                            int mid = lo + (hi - lo) / 2;
                            if (arr[mid] < target) {
                                lo = mid + 1;
                            } else {
                                hi = mid;
                            }
                        }
                        return lo;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SortedArray", "findInsertionPoint"));
    }

    @Test
    @DisplayName("Min-heap: sift down operation")
    void heapSiftDown() throws IOException {
        String source = """
                public class MinHeap {
                    private int[] heap;
                    private int size;
                    public void siftDown(int index) {
                        if (index < 0 || index >= size) throw new IllegalArgumentException();
                        while (2 * index + 1 < size) {
                            int child = 2 * index + 1;
                            if (child + 1 < size && heap[child + 1] < heap[child]) {
                                child++;
                            }
                            if (heap[index] <= heap[child]) break;
                            int temp = heap[index];
                            heap[index] = heap[child];
                            heap[child] = temp;
                            index = child;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MinHeap", "siftDown"));
    }

    // =========================================================================
    // Linked list node operations
    // =========================================================================

    @Test
    @DisplayName("Linked list node: set next pointer")
    void linkedListSetNext() throws IOException {
        String source = """
                public class ListNode {
                    private int value;
                    private ListNode next;
                    public void setNext(ListNode node) {
                        this.next = node;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ListNode", "setNext"));
    }

    @Test
    @DisplayName("Linked list node: getValue returns value")
    void linkedListGetValue() throws IOException {
        String source = """
                public class ListNode2 {
                    private int value;
                    private ListNode2 next;
                    public int getValue() {
                        return value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ListNode2", "getValue"));
    }

    @Test
    @DisplayName("Linked list node: hasNext checks null")
    void linkedListHasNext() throws IOException {
        String source = """
                public class ListNode3 {
                    private ListNode3 next;
                    public boolean hasNext() {
                        return next != null;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ListNode3", "hasNext"));
    }

    // =========================================================================
    // Bounded counter / accumulator
    // =========================================================================

    @Test
    @DisplayName("Bounded counter: increment with upper limit")
    void boundedCounterIncrement() throws IOException {
        String source = """
                public class BoundedCounter {
                    private int count;
                    private int max;
                    public boolean increment() {
                        if (count >= max) {
                            return false;
                        }
                        count++;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoundedCounter", "increment"));
    }

    @Test
    @DisplayName("Bounded counter: decrement with lower limit")
    void boundedCounterDecrement() throws IOException {
        String source = """
                public class BoundedCounter2 {
                    private int count;
                    public boolean decrement() {
                        if (count <= 0) {
                            return false;
                        }
                        count--;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoundedCounter2", "decrement"));
    }

    @Test
    @DisplayName("Bounded counter: reset to zero")
    void boundedCounterReset() throws IOException {
        String source = """
                public class BoundedCounter3 {
                    private int count;
                    public void reset() {
                        count = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoundedCounter3", "reset"));
    }
}
