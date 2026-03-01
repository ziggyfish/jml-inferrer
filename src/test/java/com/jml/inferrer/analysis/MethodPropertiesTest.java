package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for method property inference: purity, complexity, thread safety, assignable clauses,
 * loop invariants, and exception specifications.
 */
@DisplayName("Method Properties Inference")
class MethodPropertiesTest extends InferrerTestBase {

    // ==================== PURITY ====================

    @Test
    @DisplayName("Pure method: no field access, no I/O")
    void pureMethod() {
        MethodSpecification spec = infer("""
            class T {
                int add(int a, int b) {
                    return a + b;
                }
            }
            """, "add");
        assertTrue(spec.isPure(), "Expected pure");
        assertFalse(spec.isObserver());
        assertFalse(spec.isMutator());
    }

    @Test
    @DisplayName("Observer method: reads field, doesn't write")
    void observerMethod() {
        MethodSpecification spec = infer("""
            class T {
                private int value;
                int getValue() {
                    return this.value;
                }
            }
            """, "getValue");
        assertTrue(spec.isObserver(), "Expected observer");
        assertFalse(spec.isPure());
    }

    @Test
    @DisplayName("Mutator method: writes field")
    void mutatorMethod() {
        MethodSpecification spec = infer("""
            class T {
                private int value;
                void setValue(int v) {
                    this.value = v;
                }
            }
            """, "setValue");
        assertTrue(spec.isMutator(), "Expected mutator");
        assertFalse(spec.isPure());
    }

    @Test
    @DisplayName("Pure method with only local variables")
    void pureWithLocals() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int x) {
                    int a = x + 1;
                    int b = a * 2;
                    return b;
                }
            }
            """, "compute");
        assertTrue(spec.isPure(), "Expected pure with local vars only");
    }

    @Test
    @DisplayName("Method calling println is not pure (I/O)")
    void printlnNotPure() {
        MethodSpecification spec = infer("""
            class T {
                void log(String msg) {
                    System.out.println(msg);
                }
            }
            """, "log");
        assertFalse(spec.isPure(), "println should make it impure");
    }

    @Test
    @DisplayName("Method calling random is not pure")
    void randomNotPure() {
        MethodSpecification spec = infer("""
            class T {
                int random(int bound) {
                    return new java.util.Random().nextInt(bound);
                }
            }
            """, "random");
        assertFalse(spec.isPure(), "random should make it impure");
    }

    // ==================== COMPLEXITY ====================

    @Test
    @DisplayName("O(1) - no loops, no recursion")
    void constantTime() {
        MethodSpecification spec = infer("""
            class T {
                int add(int a, int b) { return a + b; }
            }
            """, "add");
        assertEquals("O(1)", spec.getTimeComplexity());
        assertEquals("O(1)", spec.getSpaceComplexity());
    }

    @Test
    @DisplayName("O(n) - single loop")
    void linearTime() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int[] arr) {
                    int s = 0;
                    for (int i = 0; i < arr.length; i++) { s += arr[i]; }
                    return s;
                }
            }
            """, "sum");
        assertEquals("O(n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("O(n) - while loop")
    void linearTimeWhile() {
        MethodSpecification spec = infer("""
            class T {
                int count(int n) {
                    int c = 0;
                    int i = 0;
                    while (i < n) { c++; i++; }
                    return c;
                }
            }
            """, "count");
        assertEquals("O(n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("O(n) - for-each loop")
    void linearTimeForEach() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int[] arr) {
                    int s = 0;
                    for (int x : arr) { s += x; }
                    return s;
                }
            }
            """, "sum");
        assertEquals("O(n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("O(n^2) - nested loops")
    void quadraticTime() {
        MethodSpecification spec = infer("""
            class T {
                int nested(int[][] m) {
                    int s = 0;
                    for (int i = 0; i < m.length; i++)
                        for (int j = 0; j < m[i].length; j++)
                            s += m[i][j];
                    return s;
                }
            }
            """, "nested");
        assertEquals("O(n^2)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("O(n^3) - triple nested loops")
    void cubicTime() {
        MethodSpecification spec = infer("""
            class T {
                int tripleNested(int n) {
                    int count = 0;
                    for (int i = 0; i < n; i++)
                        for (int j = 0; j < n; j++)
                            for (int k = 0; k < n; k++)
                                count++;
                    return count;
                }
            }
            """, "tripleNested");
        assertEquals("O(n^3)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("O(2^n) - recursive without divide-and-conquer")
    void exponentialTime() {
        MethodSpecification spec = infer("""
            class T {
                int fib(int n) {
                    if (n <= 1) return n;
                    return fib(n - 1) + fib(n - 2);
                }
            }
            """, "fib");
        assertEquals("O(2^n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("O(n log n) - recursive with divide by 2")
    void logLinearTime() {
        MethodSpecification spec = infer("""
            class T {
                int mergeSort(int[] a, int lo, int hi) {
                    if (lo >= hi) return 0;
                    int mid = (lo + hi) / 2;
                    return mergeSort(a, lo, mid) + mergeSort(a, mid + 1, hi);
                }
            }
            """, "mergeSort");
        assertEquals("O(n log n)", spec.getTimeComplexity());
    }

    @Test
    @DisplayName("Space O(n) when allocating array")
    void spaceLinear() {
        MethodSpecification spec = infer("""
            class T {
                int[] copy(int n) {
                    int[] result = new int[n];
                    return result;
                }
            }
            """, "copy");
        assertEquals("O(n)", spec.getSpaceComplexity());
    }

    @Test
    @DisplayName("Space O(n) when allocating collection")
    void spaceLinearCollection() {
        MethodSpecification spec = infer("""
            import java.util.ArrayList;
            import java.util.List;
            class T {
                List<Integer> make() {
                    List<Integer> list = new ArrayList<>();
                    return list;
                }
            }
            """, "make");
        assertEquals("O(n)", spec.getSpaceComplexity());
    }

    // ==================== THREAD SAFETY ====================

    @Test
    @DisplayName("Synchronized method is thread-safe")
    void synchronizedMethod() {
        MethodSpecification spec = infer("""
            class T {
                private int count;
                synchronized void increment() { count++; }
            }
            """, "increment");
        assertTrue(spec.isThreadSafe());
    }

    @Test
    @DisplayName("Synchronized block is thread-safe")
    void synchronizedBlock() {
        MethodSpecification spec = infer("""
            class T {
                private final Object lock = new Object();
                private int count;
                void increment() {
                    synchronized (lock) { count++; }
                }
            }
            """, "increment");
        assertTrue(spec.isThreadSafe());
    }

    @Test
    @DisplayName("Pure method is thread-safe")
    void pureIsThreadSafe() {
        MethodSpecification spec = infer("""
            class T {
                int add(int a, int b) { return a + b; }
            }
            """, "add");
        assertTrue(spec.isThreadSafe());
    }

    // ==================== ASSIGNABLE CLAUSES ====================

    @Test
    @DisplayName("Pure method: assignable nothing")
    void assignableNothing() {
        MethodSpecification spec = infer("""
            class T {
                int add(int a, int b) { return a + b; }
            }
            """, "add");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("\\nothing")),
                "Expected \\nothing assignable");
    }

    @Test
    @DisplayName("Field write: assignable this.field")
    void assignableField() {
        MethodSpecification spec = infer("""
            class T {
                private int value;
                void setValue(int v) { this.value = v; }
            }
            """, "setValue");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("this.value")),
                "Expected this.value");
    }

    @Test
    @DisplayName("Array element write: assignable arr[*]")
    void assignableArray() {
        MethodSpecification spec = infer("""
            class T {
                void fill(int[] arr) {
                    for (int i = 0; i < arr.length; i++) arr[i] = 0;
                }
            }
            """, "fill");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("arr[*]")),
                "Expected arr[*]");
    }

    @Test
    @DisplayName("Multiple fields written")
    void assignableMultipleFields() {
        MethodSpecification spec = infer("""
            class T {
                private int x;
                private int y;
                void setXY(int a, int b) {
                    this.x = a;
                    this.y = b;
                }
            }
            """, "setXY");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("this.x")),
                "Expected this.x");
        assertTrue(spec.getAssignableClauses().stream().anyMatch(p -> p.contains("this.y")),
                "Expected this.y");
    }

    // ==================== LOOP INVARIANTS ====================

    @Test
    @DisplayName("For loop: i >= 0")
    void forLoopLowerBound() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int[] arr) {
                    int s = 0;
                    for (int i = 0; i < arr.length; i++) { s += arr[i]; }
                    return s;
                }
            }
            """, "sum");
        assertTrue(spec.getLoopInvariants().stream().anyMatch(p -> p.contains("i >= 0")),
                "Expected i >= 0, got: " + spec.getLoopInvariants());
    }

    @Test
    @DisplayName("For loop: upper bound with array length")
    void forLoopUpperBound() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int[] arr) {
                    int s = 0;
                    for (int i = 0; i < arr.length; i++) { s += arr[i]; }
                    return s;
                }
            }
            """, "sum");
        assertTrue(spec.getLoopInvariants().stream()
                .anyMatch(p -> p.contains("i") && p.contains("arr.length")),
                "Expected upper bound invariant");
    }

    // ==================== EXCEPTION SPECIFICATIONS ====================

    @Test
    @DisplayName("Throw under condition -> exception spec")
    void throwUnderCondition() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n < 0) throw new IllegalArgumentException("negative");
                    return n;
                }
            }
            """, "compute");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("IllegalArgumentException")),
                "Expected IllegalArgumentException");
    }

    @Test
    @DisplayName("Declared exception in throws clause")
    void declaredExceptions() {
        MethodSpecification spec = infer("""
            class T {
                void process() throws java.io.IOException { }
            }
            """, "process");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("IOException")),
                "Expected IOException");
    }

    @Test
    @DisplayName("Try-catch with rethrow")
    void tryCatchRethrow() {
        MethodSpecification spec = infer("""
            class T {
                void process() {
                    try { int x = 1; }
                    catch (Exception e) { throw e; }
                }
            }
            """, "process");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("propagates Exception")),
                "Expected propagation spec");
    }

    @Test
    @DisplayName("Try-catch with wrap and rethrow")
    void tryCatchWrapRethrow() {
        MethodSpecification spec = infer("""
            class T {
                void process() {
                    try { int x = 1; }
                    catch (Exception e) { throw new RuntimeException(e); }
                }
            }
            """, "process");
        assertTrue(anyContainsAll(spec.getExceptionSpecifications(), "wraps", "RuntimeException"),
                "Expected wrapping spec");
    }

    @Test
    @DisplayName("Try-catch with return default")
    void tryCatchReturnDefault() {
        MethodSpecification spec = infer("""
            class T {
                int process() {
                    try { return 42; }
                    catch (Exception e) { return -1; }
                }
            }
            """, "process");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("on Exception returns")),
                "Expected return default");
    }

    @Test
    @DisplayName("Empty catch block -> suppresses")
    void emptyCatchBlock() {
        MethodSpecification spec = infer("""
            class T {
                void process() {
                    try { int x = 1; }
                    catch (Exception e) { }
                }
            }
            """, "process");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("suppresses Exception")),
                "Expected suppresses");
    }

    @Test
    @DisplayName("Finally block with close -> resource cleanup")
    void finallyWithClose() {
        MethodSpecification spec = infer("""
            class T {
                void process(java.io.Closeable resource) {
                    try { resource.toString(); }
                    catch (Exception e) { }
                    finally { resource.close(); }
                }
            }
            """, "process");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("ensures resources are closed")),
                "Expected resource cleanup spec");
    }

    @Test
    @DisplayName("Multiple exception types thrown")
    void multipleExceptionTypes() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n, String s) {
                    if (n < 0) throw new IllegalArgumentException("neg");
                    if (s == null) throw new NullPointerException("null");
                    return n;
                }
            }
            """, "compute");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("IllegalArgumentException")),
                "Expected IAE");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("NullPointerException")),
                "Expected NPE");
    }
}
