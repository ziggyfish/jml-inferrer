package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests that {@link SumInductionAnalyzer} emits the expected inductive-hypothesis
 * loop invariants for canonical accumulator, counter, and product loops. These are
 * the invariants the SMT solver needs to close a postcondition stated in terms of
 * the same quantifier.
 */
@DisplayName("Sum / product / num_of induction hypotheses")
class SumInductionAnalyzerTest extends InferrerTestBase {

    @Test
    @DisplayName("Array sum emits \\sum induction invariant")
    void arraySumInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int sum(int[] arr) {
                    int total = 0;
                    for (int i = 0; i < arr.length; i++) {
                        total += arr[i];
                    }
                    return total;
                }
            }
            """, "sum");
        assertTrue(
                spec.getLoopInvariants().stream().anyMatch(inv ->
                        inv.contains("total == (\\sum int k;")
                        && inv.contains("0 <= k && k < i")
                        && inv.contains("arr[k]")),
                "Expected accumulator to induce \\sum invariant. Got: " + spec.getLoopInvariants());
    }

    @Test
    @DisplayName("Counter-of-indices emits \\sum k invariant")
    void counterSumInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int sumTo(int n) {
                    int total = 0;
                    for (int j = 0; j < n; j++) {
                        total += j;
                    }
                    return total;
                }
            }
            """, "sumTo");
        assertTrue(
                spec.getLoopInvariants().stream().anyMatch(inv ->
                        inv.contains("total == (\\sum int k;")
                        && inv.contains("0 <= k && k < j")
                        && inv.endsWith("; k)")),
                "Expected \\sum k invariant. Got: " + spec.getLoopInvariants());
    }

    @Test
    @DisplayName("Conditional count emits \\num_of invariant")
    void conditionalCountInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int countPositive(int[] arr) {
                    int c = 0;
                    for (int i = 0; i < arr.length; i++) {
                        if (arr[i] > 0) c++;
                    }
                    return c;
                }
            }
            """, "countPositive");
        assertTrue(
                spec.getLoopInvariants().stream().anyMatch(inv ->
                        inv.contains("c == (\\num_of int k;")
                        && inv.contains("0 <= k && k < i")
                        && inv.contains("arr[k] > 0")),
                "Expected \\num_of invariant for conditional counter. Got: " + spec.getLoopInvariants());
    }

    @Test
    @DisplayName("Factorial emits \\product invariant")
    void factorialProductInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int factorial(int n) {
                    int p = 1;
                    for (int j = 1; j <= n; j++) {
                        p *= j;
                    }
                    return p;
                }
            }
            """, "factorial");
        assertTrue(
                spec.getLoopInvariants().stream().anyMatch(inv ->
                        inv.contains("p == (\\product int k;")
                        && inv.contains("1 <= k && k < j")
                        && inv.endsWith("; k)")),
                "Expected \\product k invariant. Got: " + spec.getLoopInvariants());
    }

    @Test
    @DisplayName("While-loop array accumulator emits \\sum induction invariant")
    void whileLoopAccumulatorInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int sumWhile(int[] arr) {
                    int i = 0;
                    int total = 0;
                    while (i < arr.length) {
                        total += arr[i];
                        i++;
                    }
                    return total;
                }
            }
            """, "sumWhile");
        assertTrue(
                spec.getLoopInvariants().stream().anyMatch(inv ->
                        inv.contains("total == (\\sum int k;")
                        && inv.contains("0 <= k && k < i")
                        && inv.contains("arr[k]")),
                "Expected while-loop \\sum invariant. Got: " + spec.getLoopInvariants());
        assertTrue(
                spec.getPostconditions().stream().anyMatch(post ->
                        post.contains("\\result == (\\sum int k;")
                        && post.contains("0 <= k && k < arr.length")
                        && post.contains("arr[k]")),
                "Expected while-loop matching postcondition. Got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("For-each over array emits \\sum postcondition with arr[k] substitution")
    void forEachAccumulatorPostcondition() {
        MethodSpecification spec = infer("""
            class T {
                int sumArray(int[] arr) {
                    int total = 0;
                    for (int val : arr) {
                        total += val;
                    }
                    return total;
                }
            }
            """, "sumArray");
        assertTrue(
                spec.getPostconditions().stream().anyMatch(post ->
                        post.contains("\\result == (\\sum int k;")
                        && post.contains("0 <= k && k < arr.length")
                        && post.contains("arr[k]")),
                "Expected for-each substituted-summand postcondition. Got: "
                        + spec.getPostconditions());
    }

    @Test
    @DisplayName("Counter-from-zero `total += i` emits quadratic Gauss invariant")
    void counterSumQuadraticGuard() {
        MethodSpecification spec = infer("""
            class T {
                int sumTo(int n) {
                    int total = 0;
                    for (int i = 0; i < n; i++) {
                        total += i;
                    }
                    return total;
                }
            }
            """, "sumTo");
        assertTrue(
                spec.getLoopInvariants().stream().anyMatch(inv ->
                        inv.contains("total == ((\\bigint)i * (i - 1)) / 2")),
                "Expected Gauss closed-form invariant. Got: " + spec.getLoopInvariants());
        assertTrue(
                spec.getPreconditions().stream().anyMatch(pre ->
                        pre.contains("((\\bigint)n * (n + 1)) / 2 <= Integer.MAX_VALUE")),
                "Expected quadratic precondition. Got: " + spec.getPreconditions());
    }

    @Test
    @DisplayName("Accumulator persisting outside outer loop is NOT emitted")
    void nestedLoopPersistenceSuppresses() {
        MethodSpecification spec = infer("""
            class T {
                int sumMatrix(int[][] m) {
                    int total = 0;
                    for (int i = 0; i < m.length; i++) {
                        for (int j = 0; j < m[i].length; j++) {
                            total += m[i][j];
                        }
                    }
                    return total;
                }
            }
            """, "sumMatrix");
        // `total` is declared outside both loops, so it persists across outer
        // iterations. The inner loop's `total == (\sum k; 0 <= k < j; m[i][k])`
        // would be unsound: at the start of outer iteration i=1 (j=0), total
        // already holds row 0's sum, not 0. The analyzer must skip emission.
        long sumCount = spec.getLoopInvariants().stream()
                .filter(inv -> inv.contains("total == (\\sum"))
                .count();
        assertTrue(sumCount == 0,
                "Expected no \\sum invariant for persisting accumulator. Got: "
                        + spec.getLoopInvariants());
    }
}
