package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Tier 1 formal verification tests for postcondition specifications.
 * Each test writes JML comment syntax directly and invokes OpenJML ESC.
 */
class PostconditionVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Basic arithmetic postconditions
    // =========================================================================

    @Test
    @DisplayName("Simple addition: ensures \\result == a + b")
    void simpleAddition() throws IOException {
        String source = """
                public class SimpleAddition {
                    public int add(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SimpleAddition", "add"));
    }

    @Test
    @DisplayName("Simple subtraction: ensures \\result == a - b")
    void simpleSubtraction() throws IOException {
        String source = """
                public class SimpleSubtraction {
                    public int subtract(int a, int b) {
                        return a - b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SimpleSubtraction", "subtract"));
    }

    @Test
    @DisplayName("Simple multiplication: ensures \\result == a * b")
    void simpleMultiplication() throws IOException {
        String source = """
                public class SimpleMultiplication {
                    public int multiply(int a, int b) {
                        return a * b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SimpleMultiplication", "multiply"));
    }

    @Test
    @DisplayName("Negation: ensures \\result == -x")
    void negation() throws IOException {
        String source = """
                public class Negation {
                    public int negate(int x) {
                        return -x;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Negation", "negate"));
    }

    @Test
    @DisplayName("Compound expression: ensures \\result == a * b + c")
    void compoundExpression() throws IOException {
        String source = """
                public class CompoundExpression {
                    public int multiplyAdd(int a, int b, int c) {
                        return a * b + c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CompoundExpression", "multiplyAdd"));
    }

    @Test
    @DisplayName("Average of two: ensures \\result == (a + b) / 2")
    void averageOfTwo() throws IOException {
        String source = """
                public class AverageOfTwo {
                    public int average(int a, int b) {
                        return (a + b) / 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AverageOfTwo", "average"));
    }

    // =========================================================================
    // Non-negative / bound postconditions
    // =========================================================================

    @Test
    @DisplayName("Self-square non-negative: ensures \\result >= 0")
    void selfSquareNonNeg() throws IOException {
        String source = """
                public class SelfSquareNonNeg {
                    public int square(int x) {
                        return x * x;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SelfSquareNonNeg", "square"));
    }

    @Test
    @DisplayName("Math.abs non-negative: ensures \\result >= 0")
    void mathAbsNonNeg() throws IOException {
        String source = """
                public class MathAbsNonNeg {
                    public int absValue(int x) {
                        return Math.abs(x);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MathAbsNonNeg", "absValue"));
    }

    @Test
    @DisplayName("Max of two: result >= a and result >= b")
    void maxOfTwo() throws IOException {
        String source = """
                public class MaxOfTwo {
                    public int max(int a, int b) {
                        return a >= b ? a : b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MaxOfTwo", "max"));
    }

    @Test
    @DisplayName("Min of two: result <= a and result <= b")
    void minOfTwo() throws IOException {
        String source = """
                public class MinOfTwo {
                    public int min(int a, int b) {
                        return a <= b ? a : b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MinOfTwo", "min"));
    }

    @Test
    @DisplayName("Clamp result within bounds")
    void clampPostcondition() throws IOException {
        String source = """
                public class ClampPostcondition {
                    public int clamp(int val, int lo, int hi) {
                        if (val < lo) return lo;
                        if (val > hi) return hi;
                        return val;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ClampPostcondition", "clamp"));
    }

    @Test
    @DisplayName("Absolute difference: ensures \\result >= 0")
    void absoluteDifference() throws IOException {
        String source = """
                public class AbsoluteDifference {
                    public int absDiff(int a, int b) {
                        if (a >= b) return a - b;
                        return b - a;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AbsoluteDifference", "absDiff"));
    }

    // =========================================================================
    // Field modification postconditions
    // =========================================================================

    @Test
    @DisplayName("Field assignment: ensures this.value == v")
    void fieldAssignment() throws IOException {
        String source = """
                public class FieldAssignment {
                    int value;
                    public void setValue(int v) {
                        this.value = v;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldAssignment", "setValue"));
    }

    @Test
    @DisplayName("Field increment: ensures this.count == \\old(this.count) + 1")
    void fieldIncrement() throws IOException {
        String source = """
                public class FieldIncrement {
                    int count;
                    public void increment() {
                        this.count++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldIncrement", "increment"));
    }

    @Test
    @DisplayName("Field decrement: ensures this.count == \\old(this.count) - 1")
    void fieldDecrement() throws IOException {
        String source = """
                public class FieldDecrement {
                    int count;
                    public void decrement() {
                        this.count--;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldDecrement", "decrement"));
    }

    @Test
    @DisplayName("Multiple field assignment: set x and y")
    void multipleFieldAssignment() throws IOException {
        String source = """
                public class MultipleFieldAssignment {
                    int x;
                    int y;
                    public void setCoords(int a, int b) {
                        this.x = a;
                        this.y = b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultipleFieldAssignment", "setCoords"));
    }

    @Test
    @DisplayName("Swap fields: ensures x == \\old(y) and y == \\old(x)")
    void swapFields() throws IOException {
        String source = """
                public class SwapFields {
                    int x;
                    int y;
                    public void swap() {
                        int tmp = this.x;
                        this.x = this.y;
                        this.y = tmp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwapFields", "swap"));
    }

    @Test
    @DisplayName("Reset all fields to zero")
    void resetFields() throws IOException {
        String source = """
                public class ResetFields {
                    int a;
                    int b;
                    int c;
                    public void reset() {
                        this.a = 0;
                        this.b = 0;
                        this.c = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ResetFields", "reset"));
    }

    // =========================================================================
    // Builder / return-this patterns
    // =========================================================================

    @Test
    @DisplayName("Builder returns this: ensures \\result == this")
    void builderReturnsThis() throws IOException {
        String source = """
                public class BuilderReturnsThis {
                    int value;
                    public BuilderReturnsThis withValue(int v) {
                        this.value = v;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BuilderReturnsThis", "withValue"));
    }

    @Test
    @DisplayName("New object non-null: ensures \\result != null")
    void newObjectNonNull() throws IOException {
        String source = """
                public class NewObjectNonNull {
                    public int[] createArray(int n) {
                        return new int[n];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NewObjectNonNull", "createArray"));
    }

    @Test
    @DisplayName("New object with length: ensures \\result.length == n")
    void newArrayLength() throws IOException {
        String source = """
                public class NewArrayLength {
                    public int[] makeArray(int n) {
                        return new int[n];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NewArrayLength", "makeArray"));
    }

    // =========================================================================
    // Complex: conditional returns + postconditions
    // =========================================================================

    @Test
    @DisplayName("Sign function: returns -1, 0, or 1")
    void signFunction() throws IOException {
        String source = """
                public class SignFunction {
                    public int sign(int x) {
                        if (x > 0) return 1;
                        if (x < 0) return -1;
                        return 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SignFunction", "sign"));
    }

    @Test
    @DisplayName("Boolean to int: returns 0 or 1")
    void booleanToInt() throws IOException {
        String source = """
                public class BooleanToInt {
                    public int toInt(boolean b) {
                        return b ? 1 : 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BooleanToInt", "toInt"));
    }

    @Test
    @DisplayName("Ternary max: result is greater of two values")
    void ternaryMax() throws IOException {
        String source = """
                public class TernaryMax {
                    public int max(int a, int b) {
                        return (a >= b) ? a : b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TernaryMax", "max"));
    }

    @Test
    @DisplayName("Fibonacci-like step: result == a + b")
    void fibonacciStep() throws IOException {
        String source = """
                public class FibonacciStep {
                    public int nextFib(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FibonacciStep", "nextFib"));
    }

    // =========================================================================
    // Complex: loop-computed postconditions
    // =========================================================================

    @Test
    @DisplayName("Array contains check: result is boolean with loop")
    void arrayContains() throws IOException {
        String source = """
                public class ArrayContains {
                    public boolean contains(int[] arr, int target) {
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return true;
                        }
                        return false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayContains", "contains"));
    }

    @Test
    @DisplayName("Count in range: result >= 0")
    void countInRange() throws IOException {
        String source = """
                public class CountInRange {
                    public int countInRange(int[] arr, int lo, int hi) {
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] >= lo && arr[i] <= hi) {
                                count++;
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CountInRange", "countInRange"));
    }

    @Test
    @DisplayName("All positive check with loop and early exit")
    void allPositive() throws IOException {
        String source = """
                public class AllPositive {
                    public boolean allPositive(int[] arr) {
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] <= 0) return false;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AllPositive", "allPositive"));
    }

    // =========================================================================
    // Complex: field state + conditional postconditions
    // =========================================================================

    @Test
    @DisplayName("Bounded counter: increment caps at max")
    void boundedCounterIncrement() throws IOException {
        String source = """
                public class BoundedCounterIncrement {
                    int count;
                    int max;
                    public void increment() {
                        if (this.count < this.max) {
                            this.count++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoundedCounterIncrement", "increment"));
    }

    @Test
    @DisplayName("Toggle boolean field")
    void toggleBoolean() throws IOException {
        String source = """
                public class ToggleBoolean {
                    boolean flag;
                    public void toggle() {
                        this.flag = !this.flag;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ToggleBoolean", "toggle"));
    }

    @Test
    @DisplayName("Accumulate field: addToTotal adds value to running total")
    void accumulateField() throws IOException {
        String source = """
                public class AccumulateField {
                    int total;
                    public void addToTotal(int amount) {
                        this.total += amount;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AccumulateField", "addToTotal"));
    }

    @Test
    @DisplayName("Scale field: multiply field by factor")
    void scaleField() throws IOException {
        String source = """
                public class ScaleField {
                    int value;
                    public void scale(int factor) {
                        this.value *= factor;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ScaleField", "scale"));
    }

    // =========================================================================
    // Complex: combined pre+post on multi-step methods
    // =========================================================================

    @Test
    @DisplayName("Euclidean distance squared: non-negative result")
    void distanceSquared() throws IOException {
        String source = """
                public class DistanceSquared {
                    public int distSq(int x1, int y1, int x2, int y2) {
                        int dx = x2 - x1;
                        int dy = y2 - y1;
                        return dx * dx + dy * dy;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DistanceSquared", "distSq"));
    }

    @Test
    @DisplayName("Midpoint: result between two values")
    void midpoint() throws IOException {
        String source = """
                public class Midpoint {
                    public int midpoint(int a, int b) {
                        return a + (b - a) / 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Midpoint", "midpoint"));
    }

    @Test
    @DisplayName("Safe increment array element: pre+post+frame")
    void safeIncrementArrayElement() throws IOException {
        String source = """
                public class SafeIncrementArrayElement {
                    public void incrementAt(int[] arr, int idx) {
                        arr[idx]++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SafeIncrementArrayElement", "incrementAt"));
    }

    @Test
    @DisplayName("Swap array elements: pre+post with \\old")
    void swapArrayElements() throws IOException {
        String source = """
                public class SwapArrayElements {
                    public void swap(int[] arr, int i, int j) {
                        int tmp = arr[i];
                        arr[i] = arr[j];
                        arr[j] = tmp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwapArrayElements", "swap"));
    }

    @Test
    @DisplayName("Array copy returns same-length non-null array")
    void arrayCopyPostcondition() throws IOException {
        String source = """
                public class ArrayCopyPostcondition {
                    public int[] copyOf(int[] src) {
                        int[] dst = new int[src.length];
                        for (int i = 0; i < src.length; i++) {
                            dst[i] = src[i];
                        }
                        return dst;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayCopyPostcondition", "copyOf"));
    }

    @Test
    @DisplayName("Triple field update: ensures all three changed")
    void tripleFieldUpdate() throws IOException {
        String source = """
                public class TripleFieldUpdate {
                    int r;
                    int g;
                    int b;
                    public void setColor(int red, int green, int blue) {
                        this.r = red;
                        this.g = green;
                        this.b = blue;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TripleFieldUpdate", "setColor"));
    }

    @Test
    @DisplayName("Positive modulo: ensures result >= 0")
    void positiveModuloPostcondition() throws IOException {
        String source = """
                public class PositiveModuloPostcondition {
                    public int posMod(int val, int mod) {
                        int r = val % mod;
                        if (r < 0) r += mod;
                        return r;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PositiveModuloPostcondition", "posMod"));
    }

    @Test
    @DisplayName("Stack push: size increases by 1")
    void stackPushPostcondition() throws IOException {
        String source = """
                public class StackPushPostcondition {
                    int[] data;
                    int size;
                    public void push(int value) {
                        this.data[this.size] = value;
                        this.size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StackPushPostcondition", "push"));
    }

    @Test
    @DisplayName("Saturating add: result capped at max int")
    void saturatingAdd() throws IOException {
        String source = """
                public class SaturatingAdd {
                    public int saturatingAdd(int a, int b) {
                        long sum = (long)a + (long)b;
                        if (sum > Integer.MAX_VALUE) return Integer.MAX_VALUE;
                        return (int)sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SaturatingAdd", "saturatingAdd"));
    }
}
