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
        // Expected annotated method after inference:
        //   @Pure
        //   @ThreadSafe
        //   @Complexity(time = "O(1)", space = "O(1)")
        //   @Assignable("\\nothing")
        //   @Ensures("\\result == a + b")
        //   int add(int a, int b) {
        //       return a + b;
        //   }
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
        // Expected annotated method after inference:
        //   @Observer
        //   @Ensures("\\result == this.value")
        //   int getValue() {
        //       return this.value;
        //   }
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
        // Expected annotated method after inference:
        //   @Mutator
        //   @Assignable("this.value")
        //   @Ensures("this.value == v")
        //   void setValue(int v) {
        //       this.value = v;
        //   }
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
        // Expected annotated method after inference:
        //   @Pure
        //   @Ensures("\\result == ((x + 1) * 2)")
        //   int compute(int x) { ... }
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
        // Expected annotated method after inference:
        //   (no @Pure -- println is I/O)
        //   @Requires("msg != null")
        //   void log(String msg) { ... }
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
        // Expected annotated method after inference:
        //   (no @Pure -- Random is non-deterministic)
        //   int random(int bound) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(1)", space = "O(1)")
        //   @Pure
        //   int add(int a, int b) { return a + b; }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n)")
        //   @Requires("arr != null")
        //   @LoopInvariant("i >= 0")
        //   @LoopInvariant("i <= arr.length")
        //   int sum(int[] arr) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n)")
        //   int count(int n) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n)")
        //   @Requires("arr != null")
        //   int sum(int[] arr) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n^2)")
        //   @Requires("m != null")
        //   int nested(int[][] m) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n^3)")
        //   int tripleNested(int n) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(2^n)")
        //   @Ensures("\\result >= 0")
        //   int fib(int n) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(time = "O(n log n)")
        //   @Requires("a != null")
        //   int mergeSort(int[] a, int lo, int hi) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(space = "O(n)")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length == n")
        //   int[] copy(int n) { ... }
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
        // Expected annotated method after inference:
        //   @Complexity(space = "O(n)")
        //   @Ensures("\\result != null")
        //   List<Integer> make() { ... }
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
        // Expected annotated method after inference:
        //   @ThreadSafe
        //   @Mutator
        //   @Assignable("this.count")
        //   @Ensures("this.count == \\old(this.count) + 1")
        //   synchronized void increment() { count++; }
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
        // Expected annotated method after inference:
        //   @ThreadSafe
        //   @Mutator
        //   @Assignable("this.count")
        //   void increment() { ... }
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
        // Expected annotated method after inference:
        //   @Pure
        //   @ThreadSafe
        //   int add(int a, int b) { return a + b; }
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
        // Expected annotated method after inference:
        //   @Assignable("\\nothing")
        //   @Pure
        //   int add(int a, int b) { return a + b; }
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
        // Expected annotated method after inference:
        //   @Assignable("this.value")
        //   @Mutator
        //   @Ensures("this.value == v")
        //   void setValue(int v) { this.value = v; }
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
        // Expected annotated method after inference:
        //   @Assignable("arr[*]")
        //   @Requires("arr != null")
        //   @LoopInvariant("i >= 0")
        //   void fill(int[] arr) { ... }
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
        // Expected annotated method after inference:
        //   @Assignable("this.x")
        //   @Assignable("this.y")
        //   @Mutator
        //   @Ensures("this.x == a")
        //   @Ensures("this.y == b")
        //   void setXY(int a, int b) { ... }
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
        // Expected annotated method after inference:
        //   @LoopInvariant("i >= 0")
        //   @LoopInvariant("i <= arr.length")
        //   @Requires("arr != null")
        //   int sum(int[] arr) { ... }
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
        // Expected annotated method after inference:
        //   @LoopInvariant("i >= 0")
        //   @LoopInvariant("i <= arr.length")
        //   int sum(int[] arr) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("n >= 0")
        //   @Signals("n < 0 ==> throws IllegalArgumentException")
        //   int compute(int n) { ... }
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
        // Expected annotated method after inference:
        //   @Signals("IOException")
        //   void process() throws java.io.IOException { }
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
        // Expected annotated method after inference:
        //   @Signals("propagates Exception")
        //   void process() { ... }
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
        // Expected annotated method after inference:
        //   @Signals("wraps Exception in RuntimeException")
        //   void process() { ... }
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
        // Expected annotated method after inference:
        //   @Signals("on Exception returns -1")
        //   int process() { ... }
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
        // Expected annotated method after inference:
        //   @Signals("suppresses Exception")
        //   void process() { ... }
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
        // Expected annotated method after inference:
        //   @Requires("resource != null")
        //   @Signals("suppresses Exception")
        //   @Signals("ensures resources are closed")
        //   void process(java.io.Closeable resource) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("n >= 0")
        //   @Requires("s != null")
        //   @Signals("n < 0 ==> throws IllegalArgumentException")
        //   @Signals("s == null ==> throws NullPointerException")
        //   int compute(int n, String s) { ... }
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("IllegalArgumentException")),
                "Expected IAE");
        assertTrue(spec.getExceptionSpecifications().stream()
                .anyMatch(p -> p.contains("NullPointerException")),
                "Expected NPE");
    }
}
