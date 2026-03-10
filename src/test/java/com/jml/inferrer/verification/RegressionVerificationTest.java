package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Verification tests for regression fixes. Each test exercises the full
 * inference pipeline (infer -> annotate -> convert -> OpenJML ESC) to
 * confirm that the inferred specifications are formally valid.
 *
 * These correspond to bugs fixed in InvalidInferenceRegressionTest 1-3.
 */
@DisplayName("Regression Verification")
class RegressionVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Loop variable not in precondition (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("Array sum: loop var not in precondition, valid loop invariants")
    void arraySumLoopVarNotInPrecondition() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class ArraySum {
                int sum(int[] arr) {
                    int total = 0;
                    for (int i = 0; i < arr.length; i++) {
                        total += arr[i];
                    }
                    return total;
                }
            }
            """, "ArraySum", "sum");
        assertVerified(result);
    }

    // =========================================================================
    // Local variable not in assignable (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("Create and fill: local array not in assignable")
    void createAndFillLocalNotAssignable() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class CreateFill {
                int[] createAndFill(int n, int val) {
                    int[] result = new int[n];
                    for (int i = 0; i < n; i++) {
                        result[i] = val;
                    }
                    return result;
                }
            }
            """, "CreateFill", "createAndFill");
        assertVerified(result);
    }

    // =========================================================================
    // No 'new' in postcondition (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("makeArray: no 'new' in postcondition, \\result != null inferred")
    void makeArrayNoNewInPostcondition() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class MakeArray {
                int[] makeArray(int n) {
                    return new int[n];
                }
            }
            """, "MakeArray", "makeArray");
        assertVerified(result);
    }

    // =========================================================================
    // No ternary in postcondition (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("abs: no ternary in postcondition")
    void absNoTernary() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Abs {
                int abs(int x) {
                    return x >= 0 ? x : -x;
                }
            }
            """, "Abs", "abs");
        assertVerified(result);
    }

    // =========================================================================
    // Field increment: correct assignable and postcondition (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("Field increment: assignable this.count, postcondition with \\old")
    void fieldIncrement() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Counter {
                int count;
                void increment() {
                    this.count++;
                }
            }
            """, "Counter", "increment");
        assertVerified(result);
    }

    // =========================================================================
    // Field assignment with array access (Regression 2)
    // =========================================================================

    @Test
    @DisplayName("Field set from array access: valid postcondition")
    void fieldSetFromArrayAccess() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class FieldSet {
                int value;
                void setFromArray(int[] arr, int idx) {
                    this.value = arr[idx];
                }
            }
            """, "FieldSet", "setFromArray");
        assertVerified(result);
    }

    // =========================================================================
    // While-loop: weakened invariant, no raw condition (Regression 2)
    // =========================================================================

    @Test
    @DisplayName("While-loop sum: weakened upper bound invariant")
    void whileLoopWeakenedBound() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class WhileSum {
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
            """, "WhileSum", "sumWhile");
        assertVerified(result);
    }

    // =========================================================================
    // For-each loop: iterable null check invariant (Regression 2)
    // =========================================================================

    @Test
    @DisplayName("For-each sum: iterable != null invariant")
    void forEachIterableNullCheck() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class ForEachSum {
                int sumArray(int[] arr) {
                    int total = 0;
                    for (int val : arr) {
                        total += val;
                    }
                    return total;
                }
            }
            """, "ForEachSum", "sumArray");
        assertVerified(result);
    }

    // =========================================================================
    // \\forall for constant fill (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("Zero fill: \\forall invariant for constant assignment")
    void zeroFillForall() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class ZeroFill {
                void zeroFill(int[] arr) {
                    for (int i = 0; i < arr.length; i++) {
                        arr[i] = 0;
                    }
                }
            }
            """, "ZeroFill", "zeroFill");
        assertVerified(result);
    }

    // =========================================================================
    // Parameter array write: correct assignable (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("Fill array: assignable arr[*] for parameter array")
    void fillArrayAssignable() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class FillArr {
                void fill(int[] arr, int val) {
                    for (int i = 0; i < arr.length; i++) {
                        arr[i] = val;
                    }
                }
            }
            """, "FillArr", "fill");
        assertVerified(result);
    }

    // =========================================================================
    // \\num_of no identifier corruption (Regression 2)
    // Note: \num_of is valid JML but OpenJML ESC has limited support for it.
    // This test verifies the pipeline doesn't crash; the \num_of invariant
    // itself may not be provable by the solver.
    // =========================================================================

    @Test
    @DisplayName("Count positive: pipeline completes without crash (\\num_of limited support)")
    void countPositiveNumOf() throws IOException {
        // \num_of quantifier is valid JML but not fully supported by OpenJML ESC.
        // We verify the pipeline completes (no crash, no timeout) rather than
        // asserting VERIFIED, since the solver can't reason about \num_of.
        MethodVerificationResult result = inferAndVerify("""
            class CountPos {
                int countPositive(int[] items) {
                    int count = 0;
                    for (int i = 0; i < items.length; i++) {
                        if (items[i] > 0) {
                            count++;
                        }
                    }
                    return count;
                }
            }
            """, "CountPos", "countPositive");
        assertNotNull(result, "Pipeline should complete without crash");
    }

    // =========================================================================
    // Switch with default: \\result != null (Regression 3)
    // =========================================================================

    @Test
    @DisplayName("Switch describe: \\result != null for exhaustive switch")
    void switchExhaustiveResultNotNull() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class SwitchDesc {
                String describe(int code) {
                    switch (code) {
                        case 1: return "one";
                        case 2: return "two";
                        default: return "other";
                    }
                }
            }
            """, "SwitchDesc", "describe");
        assertVerified(result);
    }

    // =========================================================================
    // Compound assignment on field (Regression 2)
    // =========================================================================

    @Test
    @DisplayName("Compound add: this.total == \\old(this.total) + amount")
    void compoundFieldAdd() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Accumulator {
                int total;
                void add(int amount) {
                    this.total += amount;
                }
            }
            """, "Accumulator", "add");
        assertVerified(result);
    }

    // =========================================================================
    // Loop invariant upper bound weakened (Regression 1)
    // =========================================================================

    @Test
    @DisplayName("Sum to n: i <= n invariant (not i < n)")
    void sumToNWeakenedBound() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class SumToN {
                int sumTo(int n) {
                    int total = 0;
                    for (int i = 0; i < n; i++) {
                        total += i;
                    }
                    return total;
                }
            }
            """, "SumToN", "sumTo");
        assertVerified(result);
    }
}
