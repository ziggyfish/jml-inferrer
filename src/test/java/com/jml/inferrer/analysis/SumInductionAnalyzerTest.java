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
    @DisplayName("Accumulator inside nested loop is emitted once (inner-level)")
    void nestedLoopSingleEmission() {
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
        // The accumulator lives inside the inner loop. The outer loop's
        // isInsideNestedLoop check must suppress its emission there, and the
        // inner loop's analyzer must emit it exactly once.
        long sumCount = spec.getLoopInvariants().stream()
                .filter(inv -> inv.contains("total == (\\sum"))
                .count();
        assertTrue(sumCount == 1,
                "Expected exactly one \\sum invariant (inner loop). Got: "
                        + spec.getLoopInvariants());
    }
}
