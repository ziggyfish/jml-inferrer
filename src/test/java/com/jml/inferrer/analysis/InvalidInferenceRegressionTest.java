package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression tests for cases where the inference engine previously generated
 * invalid JML specifications. Each test verifies that the inferred specs are
 * syntactically valid and semantically correct JML.
 */
@DisplayName("Invalid Inference Regression")
class InvalidInferenceRegressionTest extends InferrerTestBase {

    // =========================================================================
    // Loop variable should not appear in preconditions
    // =========================================================================

    @Test
    @DisplayName("Loop variable i should not appear in requires clause")
    void loopVariableNotInPrecondition() {
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
        // The loop variable 'i' is not a method parameter. The inferrer must not
        // generate "requires arr.length > i" because 'i' is undefined at the call site.
        for (String pre : spec.getPreconditions()) {
            assertFalse(pre.contains("> i") || pre.contains(">= i") || pre.contains("< i"),
                    "Precondition must not reference loop variable 'i': " + pre);
        }
        // Should still infer arr != null
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("arr != null")),
                "Expected arr != null, got: " + spec.getPreconditions());
    }

    @Test
    @DisplayName("Loop variable j from nested loop should not appear in requires clause")
    void nestedLoopVariableNotInPrecondition() {
        MethodSpecification spec = infer("""
            class T {
                int sumMatrix(int[] data, int rows, int cols) {
                    int sum = 0;
                    for (int i = 0; i < rows; i++) {
                        for (int j = 0; j < cols; j++) {
                            sum += data[i * cols + j];
                        }
                    }
                    return sum;
                }
            }
            """, "sumMatrix");
        for (String pre : spec.getPreconditions()) {
            assertFalse(pre.matches(".*[> ](i|j)\\b.*") && !pre.contains("this."),
                    "Precondition must not reference loop variables 'i' or 'j': " + pre);
        }
    }

    // =========================================================================
    // Local variables should not appear in assignable clauses
    // =========================================================================

    @Test
    @DisplayName("Local array variable should not appear in assignable clause")
    void localArrayNotInAssignable() {
        MethodSpecification spec = infer("""
            class T {
                int[] createAndFill(int n, int val) {
                    int[] result = new int[n];
                    for (int i = 0; i < n; i++) {
                        result[i] = val;
                    }
                    return result;
                }
            }
            """, "createAndFill");
        // 'result' is a local variable, not a field or parameter.
        // The assignable clause must not reference it.
        for (String assignable : spec.getAssignableClauses()) {
            assertFalse(assignable.contains("result["),
                    "Assignable must not reference local variable 'result': " + assignable);
        }
    }

    @Test
    @DisplayName("Local array in method returning copy should not be in assignable")
    void localCopyArrayNotInAssignable() {
        MethodSpecification spec = infer("""
            class T {
                int[] copyOf(int[] src) {
                    int[] dst = new int[src.length];
                    for (int i = 0; i < src.length; i++) {
                        dst[i] = src[i];
                    }
                    return dst;
                }
            }
            """, "copyOf");
        for (String assignable : spec.getAssignableClauses()) {
            assertFalse(assignable.contains("dst["),
                    "Assignable must not reference local variable 'dst': " + assignable);
        }
    }

    // =========================================================================
    // Postconditions must not contain 'new' expressions
    // =========================================================================

    @Test
    @DisplayName("Postcondition should not contain 'new' object creation")
    void noNewInPostcondition() {
        MethodSpecification spec = infer("""
            class T {
                int[] makeArray(int n) {
                    return new int[n];
                }
            }
            """, "makeArray");
        // \result == new int[n] is not valid JML. Should infer \result != null instead.
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("new "),
                    "Postcondition must not contain 'new' expression: " + post);
        }
        // Should still infer \result != null
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Postcondition should not contain 'new' for returned local array")
    void noNewInPostconditionForLocal() {
        MethodSpecification spec = infer("""
            class T {
                int[] absArray(int[] arr) {
                    int[] result = new int[arr.length];
                    for (int i = 0; i < arr.length; i++) {
                        result[i] = arr[i] >= 0 ? arr[i] : -arr[i];
                    }
                    return result;
                }
            }
            """, "absArray");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("new "),
                    "Postcondition must not contain 'new' expression: " + post);
        }
    }

    // =========================================================================
    // Loop invariants must be valid JML, not natural language
    // =========================================================================

    @Test
    @DisplayName("Loop invariant must not contain natural language for max tracking")
    void noNaturalLanguageMaxInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int findMax(int[] arr) {
                    int max = arr[0];
                    for (int i = 1; i < arr.length; i++) {
                        if (arr[i] > max) max = arr[i];
                    }
                    return max;
                }
            }
            """, "findMax");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("maximum") || inv.contains("minimum") ||
                        inv.contains("seen so far") || inv.contains("processed"),
                    "Loop invariant must not contain natural language: " + inv);
        }
    }

    @Test
    @DisplayName("Loop invariant must not contain natural language for min tracking")
    void noNaturalLanguageMinInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int findMin(int[] arr) {
                    int min = arr[0];
                    for (int i = 1; i < arr.length; i++) {
                        if (arr[i] < min) min = arr[i];
                    }
                    return min;
                }
            }
            """, "findMin");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("maximum") || inv.contains("minimum") ||
                        inv.contains("seen so far") || inv.contains("processed"),
                    "Loop invariant must not contain natural language: " + inv);
        }
    }

    // =========================================================================
    // Loop invariant upper bound must use <= not < for standard for-loops
    // =========================================================================

    @Test
    @DisplayName("Loop invariant upper bound should use <= for i < arr.length pattern")
    void loopInvariantUpperBoundWeakened() {
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
        // A loop invariant with 'i < arr.length' is incorrect because after the
        // final increment i == arr.length. The correct invariant is 'i <= arr.length'.
        for (String inv : spec.getLoopInvariants()) {
            if (inv.contains("arr.length") && inv.contains("i")) {
                assertFalse(inv.matches(".*i\\s*<\\s*arr\\.length.*"),
                        "Loop invariant should use '<=' not '<' for upper bound: " + inv);
            }
        }
    }

    @Test
    @DisplayName("Loop invariant upper bound should use <= for i < n pattern")
    void loopInvariantUpperBoundWeakenedN() {
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
        for (String inv : spec.getLoopInvariants()) {
            if (inv.contains("n") && inv.contains("i")) {
                assertFalse(inv.matches(".*i\\s*<\\s*n.*"),
                        "Loop invariant should use '<=' not '<' for upper bound: " + inv);
            }
        }
    }

    // =========================================================================
    // Postconditions must not contain ternary expressions (precedence issues)
    // =========================================================================

    @Test
    @DisplayName("Postcondition should not contain raw ternary operator")
    void noTernaryInPostcondition() {
        MethodSpecification spec = infer("""
            class T {
                int abs(int x) {
                    return x >= 0 ? x : -x;
                }
            }
            """, "abs");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("?") && post.contains(":"),
                    "Postcondition must not contain ternary (causes JML precedence issues): " + post);
        }
    }

    @Test
    @DisplayName("Postcondition with ternary from resolved local must be fully parenthesised")
    void noTernaryFromResolvedLocal() {
        MethodSpecification spec = infer("""
            class T {
                int clamp(int val, int lo, int hi) {
                    int result = val < lo ? lo : (val > hi ? hi : val);
                    return result;
                }
            }
            """, "clamp");
        // Ternary postconditions ARE valid JML so long as the whole expression is wrapped
        // in parentheses (otherwise `\result == cond ? a : b` parses as
        // `(\result == cond) ? a : b`). Earlier this test forbade ternary outright; now it
        // enforces the parenthesisation contract instead.
        for (String post : spec.getPostconditions()) {
            if (post.contains("?") && post.contains(":")) {
                assertTrue(post.matches("\\\\result\\s*==\\s*\\(.*\\)"),
                        "Ternary postcondition must be wrapped \\result == (...): " + post);
            }
        }
    }

    // =========================================================================
    // Quantified loop invariants must have correct syntax
    // =========================================================================

    @Test
    @DisplayName("Forall invariant should not be generated for complex values like ternary")
    void noForallWithTernary() {
        MethodSpecification spec = infer("""
            class T {
                int[] absArray(int[] arr) {
                    int[] result = new int[arr.length];
                    for (int i = 0; i < arr.length; i++) {
                        result[i] = arr[i] >= 0 ? arr[i] : -arr[i];
                    }
                    return result;
                }
            }
            """, "absArray");
        for (String inv : spec.getLoopInvariants()) {
            if (inv.contains("\\forall")) {
                // If a \forall is generated, it must not contain ternary operators
                assertFalse(inv.contains("?") && inv.contains(":"),
                        "Forall invariant must not contain ternary expression: " + inv);
            }
        }
    }

    @Test
    @DisplayName("Forall invariant should be generated for simple constant fill")
    void forallForConstantFill() {
        MethodSpecification spec = infer("""
            class T {
                void zeroFill(int[] arr) {
                    for (int i = 0; i < arr.length; i++) {
                        arr[i] = 0;
                    }
                }
            }
            """, "zeroFill");
        // Zero fill is a simple pattern that should generate a valid \forall invariant
        assertTrue(spec.getLoopInvariants().stream()
                        .anyMatch(inv -> inv.contains("\\forall") && inv.contains("== 0")),
                "Expected \\forall invariant for zero fill, got: " + spec.getLoopInvariants());
    }

    // =========================================================================
    // All inferred specs should be syntactically valid JML
    // =========================================================================

    @Test
    @DisplayName("No specs should contain undefined variables (loop vars, block-scoped vars)")
    void noUndefinedVariablesInSpecs() {
        MethodSpecification spec = infer("""
            class T {
                int processArray(int[] data) {
                    int sum = 0;
                    for (int idx = 0; idx < data.length; idx++) {
                        int element = data[idx];
                        sum += element;
                    }
                    return sum;
                }
            }
            """, "processArray");
        // 'idx' and 'element' are local/loop variables and must not appear in specs
        for (String pre : spec.getPreconditions()) {
            assertFalse(pre.contains("idx") || pre.contains("element"),
                    "Precondition references local/loop variable: " + pre);
        }
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("element"),
                    "Postcondition references block-scoped variable: " + post);
        }
    }

    @Test
    @DisplayName("Assignable clause for parameter array write should reference the parameter")
    void assignableForParameterArrayWrite() {
        MethodSpecification spec = infer("""
            class T {
                void fill(int[] arr, int val) {
                    for (int i = 0; i < arr.length; i++) {
                        arr[i] = val;
                    }
                }
            }
            """, "fill");
        // arr is a parameter, so arr[*] is valid in assignable
        assertTrue(spec.getAssignableClauses().stream().anyMatch(a -> a.contains("arr[")),
                "Expected assignable arr[*] for parameter array write, got: " + spec.getAssignableClauses());
    }

    @Test
    @DisplayName("Field increment should have correct assignable and postcondition")
    void fieldIncrementCorrectSpecs() {
        MethodSpecification spec = infer("""
            class T {
                int count;
                void increment() {
                    this.count++;
                }
            }
            """, "increment");
        // Should have assignable this.count
        assertTrue(spec.getAssignableClauses().stream().anyMatch(a -> a.contains("this.count")),
                "Expected assignable this.count, got: " + spec.getAssignableClauses());
        // Should have postcondition about count changing
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("count") && p.contains("\\old")),
                "Expected postcondition with \\old(this.count), got: " + spec.getPostconditions());
    }

    // =========================================================================
    // Integer overflow: x * x can be negative for int/long
    // =========================================================================

    @Test
    @DisplayName("x * x with int return should not infer \\result >= 0 (overflow)")
    void selfMultiplyIntCanOverflow() {
        MethodSpecification spec = infer("""
            class T {
                int square(int x) {
                    return x * x;
                }
            }
            """, "square");
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "int x * x can overflow to negative; must not infer \\result >= 0, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("x * x with double return should infer \\result >= 0 (no overflow)")
    void selfMultiplyDoubleIsNonNegative() {
        MethodSpecification spec = infer("""
            class T {
                double square(double x) {
                    return x * x;
                }
            }
            """, "square");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "double x * x cannot overflow to negative; expected \\result >= 0, got: " + spec.getPostconditions());
    }
}
