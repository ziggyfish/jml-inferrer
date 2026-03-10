package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Tier 2 end-to-end tests: raw source -> infer specs -> inject annotations ->
 * convert to JML comments -> invoke OpenJML -> assert VERIFIED.
 *
 * These exercise the full pipeline including AnnotationToJMLConverter integration.
 * Tests use increasingly complex Java constructs to stress-test the entire inference chain.
 */
class FullPipelineVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Basic single-construct E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: simple addition return a + b")
    void simpleAddE2E() throws IOException {
        String source = """
                public class SimpleAddE2E {
                    public int add(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SimpleAddE2E", "add"));
    }

    @Test
    @DisplayName("E2E: null check on string parameter")
    void nullCheckE2E() throws IOException {
        String source = """
                public class NullCheckE2E {
                    public int getLength(String s) {
                        return s.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NullCheckE2E", "getLength"));
    }

    @Test
    @DisplayName("E2E: field assignment setter")
    void fieldAssignE2E() throws IOException {
        String source = """
                public class FieldAssignE2E {
                    private int value;
                    public void setValue(int v) {
                        this.value = v;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldAssignE2E", "setValue"));
    }

    @Test
    @DisplayName("E2E: guard clause with throw")
    void guardClauseE2E() throws IOException {
        String source = """
                public class GuardClauseE2E {
                    public int process(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        return n * 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardClauseE2E", "process"));
    }

    @Test
    @DisplayName("E2E: for loop with array iteration")
    void loopInvariantE2E() throws IOException {
        String source = """
                public class LoopInvariantE2E {
                    public int sum(int[] arr) {
                        int total = 0;
                        for (int i = 0; i < arr.length; i++) {
                            total += arr[i];
                        }
                        return total;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopInvariantE2E", "sum"));
    }

    // =========================================================================
    // Arithmetic and return-value E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: subtraction")
    void subtractionE2E() throws IOException {
        String source = """
                public class SubtractionE2E {
                    public int subtract(int a, int b) {
                        return a - b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SubtractionE2E", "subtract"));
    }

    @Test
    @DisplayName("E2E: multiplication")
    void multiplicationE2E() throws IOException {
        String source = """
                public class MultiplicationE2E {
                    public int multiply(int a, int b) {
                        return a * b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiplicationE2E", "multiply"));
    }

    @Test
    @DisplayName("E2E: boolean method returns comparison")
    void booleanReturnE2E() throws IOException {
        String source = """
                public class BooleanReturnE2E {
                    public boolean isPositive(int n) {
                        return n > 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BooleanReturnE2E", "isPositive"));
    }

    @Test
    @DisplayName("E2E: new array allocation")
    void newArrayE2E() throws IOException {
        String source = """
                public class NewArrayE2E {
                    public int[] makeArray(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        return new int[n];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NewArrayE2E", "makeArray"));
    }

    // =========================================================================
    // Null checks E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: two string params null check")
    void twoStringParamsE2E() throws IOException {
        String source = """
                public class TwoStringParamsE2E {
                    public int combined(String a, String b) {
                        return a.length() + b.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TwoStringParamsE2E", "combined"));
    }

    @Test
    @DisplayName("E2E: array first element access")
    void arrayFirstE2E() throws IOException {
        String source = """
                public class ArrayFirstE2E {
                    public int first(int[] arr) {
                        return arr[0];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayFirstE2E", "first"));
    }

    @Test
    @DisplayName("E2E: string charAt")
    void stringCharAtE2E() throws IOException {
        String source = """
                public class StringCharAtE2E {
                    public char firstChar(String s) {
                        return s.charAt(0);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StringCharAtE2E", "firstChar"));
    }

    // =========================================================================
    // Field mutation E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: field increment")
    void fieldIncrementE2E() throws IOException {
        String source = """
                public class FieldIncrementE2E {
                    private int count;
                    public void increment() {
                        this.count++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldIncrementE2E", "increment"));
    }

    @Test
    @DisplayName("E2E: field decrement")
    void fieldDecrementE2E() throws IOException {
        String source = """
                public class FieldDecrementE2E {
                    private int count;
                    public void decrement() {
                        this.count--;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldDecrementE2E", "decrement"));
    }

    @Test
    @DisplayName("E2E: set two fields")
    void setTwoFieldsE2E() throws IOException {
        String source = """
                public class SetTwoFieldsE2E {
                    private int x;
                    private int y;
                    public void setCoords(int a, int b) {
                        this.x = a;
                        this.y = b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SetTwoFieldsE2E", "setCoords"));
    }

    @Test
    @DisplayName("E2E: builder returns this")
    void builderE2E() throws IOException {
        String source = """
                public class BuilderE2E {
                    private int value;
                    public BuilderE2E withValue(int v) {
                        this.value = v;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BuilderE2E", "withValue"));
    }

    // =========================================================================
    // Guard clauses + validation E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: division guard clause")
    void divisionGuardE2E() throws IOException {
        String source = """
                public class DivisionGuardE2E {
                    public int divide(int a, int b) {
                        if (b == 0) throw new ArithmeticException();
                        return a / b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DivisionGuardE2E", "divide"));
    }

    @Test
    @DisplayName("E2E: negative guard then computation")
    void negativeGuardComputeE2E() throws IOException {
        String source = """
                public class NegativeGuardComputeE2E {
                    public int sqrt(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int result = 0;
                        while (result * result < n) {
                            result++;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NegativeGuardComputeE2E", "sqrt"));
    }

    @Test
    @DisplayName("E2E: multiple guard clauses")
    void multipleGuardsE2E() throws IOException {
        String source = """
                public class MultipleGuardsE2E {
                    public int safeCompute(int a, int b) {
                        if (a < 0) throw new IllegalArgumentException();
                        if (b <= 0) throw new IllegalArgumentException();
                        return a / b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultipleGuardsE2E", "safeCompute"));
    }

    // =========================================================================
    // Loops E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: while loop countdown")
    void whileCountdownE2E() throws IOException {
        String source = """
                public class WhileCountdownE2E {
                    public int countdown(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int count = 0;
                        int i = n;
                        while (i > 0) {
                            i--;
                            count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "WhileCountdownE2E", "countdown"));
    }

    @Test
    @DisplayName("E2E: loop finding maximum in array")
    void findMaxE2E() throws IOException {
        String source = """
                public class FindMaxE2E {
                    public int findMax(int[] arr) {
                        int max = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            if (arr[i] > max) max = arr[i];
                        }
                        return max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FindMaxE2E", "findMax"));
    }

    @Test
    @DisplayName("E2E: loop counting negatives")
    void countNegativesE2E() throws IOException {
        String source = """
                public class CountNegativesE2E {
                    public int countNeg(int[] arr) {
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < 0) count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CountNegativesE2E", "countNeg"));
    }

    @Test
    @DisplayName("E2E: loop search with early return")
    void linearSearchE2E() throws IOException {
        String source = """
                public class LinearSearchE2E {
                    public int indexOf(int[] arr, int target) {
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return i;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LinearSearchE2E", "indexOf"));
    }

    @Test
    @DisplayName("E2E: nested loops counting")
    void nestedLoopsE2E() throws IOException {
        String source = """
                public class NestedLoopsE2E {
                    public int product(int rows, int cols) {
                        if (rows < 0 || cols < 0) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < rows; i++) {
                            for (int j = 0; j < cols; j++) {
                                count++;
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NestedLoopsE2E", "product"));
    }

    // =========================================================================
    // Complex multi-construct E2E
    // =========================================================================

    @Test
    @DisplayName("E2E: guard + null check + loop + conditional accumulator")
    void guardNullLoopAccumulatorE2E() throws IOException {
        String source = """
                public class GuardNullLoopAccumulatorE2E {
                    public int sumPositive(int[] arr) {
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardNullLoopAccumulatorE2E", "sumPositive"));
    }

    @Test
    @DisplayName("E2E: field + guard + conditional update")
    void fieldGuardConditionalE2E() throws IOException {
        String source = """
                public class FieldGuardConditionalE2E {
                    private int max;
                    public void updateMax(int value) {
                        if (value > this.max) {
                            this.max = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldGuardConditionalE2E", "updateMax"));
    }

    @Test
    @DisplayName("E2E: loop filling array with computation")
    void loopFillArrayE2E() throws IOException {
        String source = """
                public class LoopFillArrayE2E {
                    public int[] squares(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int[] result = new int[n];
                        for (int i = 0; i < n; i++) {
                            result[i] = i * i;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "LoopFillArrayE2E", "squares"));
    }

    @Test
    @DisplayName("E2E: copy array elements")
    void copyArrayE2E() throws IOException {
        String source = """
                public class CopyArrayE2E {
                    public void copy(int[] src, int[] dst) {
                        for (int i = 0; i < src.length; i++) {
                            dst[i] = src[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CopyArrayE2E", "copy"));
    }

    @Test
    @DisplayName("E2E: GCD with while loop and subtraction")
    void gcdE2E() throws IOException {
        String source = """
                public class GCDE2E {
                    public int gcd(int a, int b) {
                        if (a <= 0 || b <= 0) throw new IllegalArgumentException();
                        while (a != b) {
                            if (a > b) a = a - b;
                            else b = b - a;
                        }
                        return a;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GCDE2E", "gcd"));
    }

    @Test
    @DisplayName("E2E: factorial with guard and loop")
    void factorialE2E() throws IOException {
        String source = """
                public class FactorialE2E {
                    public int factorial(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int result = 1;
                        for (int i = 1; i <= n; i++) {
                            result *= i;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FactorialE2E", "factorial"));
    }

    @Test
    @DisplayName("E2E: absolute value with branching")
    void absoluteValueE2E() throws IOException {
        String source = """
                public class AbsoluteValueE2E {
                    public int abs(int x) {
                        if (x >= 0) return x;
                        return -x;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AbsoluteValueE2E", "abs"));
    }

    @Test
    @DisplayName("E2E: multi-field reset")
    void multiFieldResetE2E() throws IOException {
        String source = """
                public class MultiFieldResetE2E {
                    private int x;
                    private int y;
                    private int z;
                    public void reset() {
                        this.x = 0;
                        this.y = 0;
                        this.z = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiFieldResetE2E", "reset"));
    }

    @Test
    @DisplayName("E2E: reverse array in place")
    void reverseE2E() throws IOException {
        String source = """
                public class ReverseE2E {
                    public void reverse(int[] arr) {
                        int left = 0;
                        int right = arr.length - 1;
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
        assertVerified(inferAndVerify(source, "ReverseE2E", "reverse"));
    }

    @Test
    @DisplayName("E2E: dot product of two arrays")
    void dotProductE2E() throws IOException {
        String source = """
                public class DotProductE2E {
                    public int dotProduct(int[] a, int[] b) {
                        int result = 0;
                        for (int i = 0; i < a.length; i++) {
                            result += a[i] * b[i];
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DotProductE2E", "dotProduct"));
    }

    @Test
    @DisplayName("E2E: stack push with field + array mutation")
    void stackPushE2E() throws IOException {
        String source = """
                public class StackPushE2E {
                    private int[] data;
                    private int size;
                    public void push(int value) {
                        this.data[this.size] = value;
                        this.size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StackPushE2E", "push"));
    }

    @Test
    @DisplayName("E2E: boolean check with loop: allPositive")
    void allPositiveE2E() throws IOException {
        String source = """
                public class AllPositiveE2E {
                    public boolean allPositive(int[] arr) {
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] <= 0) return false;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AllPositiveE2E", "allPositive"));
    }
}
