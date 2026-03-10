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
                    //@ ensures \\result == a + b;
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
                    //@ ensures \\result == a - b;
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
                    //@ ensures \\result == a * b;
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
                    //@ ensures \\result == -x;
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
                    //@ ensures \\result == a * b + c;
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
                    //@ ensures \\result == (a + b) / 2;
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
                    //@ ensures \\result >= 0;
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
                    //@ ensures \\result >= 0;
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
                    //@ ensures \\result >= a;
                    //@ ensures \\result >= b;
                    //@ ensures \\result == a || \\result == b;
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
                    //@ ensures \\result <= a;
                    //@ ensures \\result <= b;
                    //@ ensures \\result == a || \\result == b;
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
                    //@ requires lo <= hi;
                    //@ ensures \\result >= lo;
                    //@ ensures \\result <= hi;
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
                    //@ ensures \\result >= 0;
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
                    //@ assignable this.value;
                    //@ ensures this.value == v;
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
                    //@ assignable this.count;
                    //@ ensures this.count == \\old(this.count) + 1;
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
                    //@ assignable this.count;
                    //@ ensures this.count == \\old(this.count) - 1;
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
                    //@ assignable this.x, this.y;
                    //@ ensures this.x == a;
                    //@ ensures this.y == b;
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
                    //@ assignable this.x, this.y;
                    //@ ensures this.x == \\old(this.y);
                    //@ ensures this.y == \\old(this.x);
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
                    //@ assignable this.a, this.b, this.c;
                    //@ ensures this.a == 0;
                    //@ ensures this.b == 0;
                    //@ ensures this.c == 0;
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
                    //@ assignable this.value;
                    //@ ensures \\result == this;
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
                    //@ requires n >= 0;
                    //@ ensures \\result != null;
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
                    //@ requires n >= 0;
                    //@ ensures \\result != null;
                    //@ ensures \\result.length == n;
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
                    //@ ensures \\result == -1 || \\result == 0 || \\result == 1;
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
                    //@ ensures \\result == 0 || \\result == 1;
                    public int toInt(boolean b) {
                        return b ? 1 : 0;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "BooleanToInt", "toInt"));
    }

    @Test
    @DisplayName("Ternary max: result is greater of two values")
    void ternaryMax() throws IOException {
        String source = """
                public class TernaryMax {
                    //@ ensures \\result >= a;
                    //@ ensures \\result >= b;
                    public int max(int a, int b) {
                        return (a >= b) ? a : b;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "TernaryMax", "max"));
    }

    @Test
    @DisplayName("Fibonacci-like step: result == a + b")
    void fibonacciStep() throws IOException {
        String source = """
                public class FibonacciStep {
                    //@ ensures \\result == a + b;
                    public int nextFib(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "FibonacciStep", "nextFib"));
    }

    // =========================================================================
    // Complex: loop-computed postconditions
    // =========================================================================

    @Test
    @DisplayName("Array contains check: result is boolean with loop")
    void arrayContains() throws IOException {
        String source = """
                public class ArrayContains {
                    //@ requires arr != null;
                    public boolean contains(int[] arr, int target) {
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return true;
                        }
                        return false;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "ArrayContains", "contains"));
    }

    @Test
    @DisplayName("Count in range: result >= 0")
    void countInRange() throws IOException {
        String source = """
                public class CountInRange {
                    //@ requires arr != null;
                    //@ requires lo <= hi;
                    //@ ensures \\result >= 0;
                    //@ ensures \\result <= arr.length;
                    public int countInRange(int[] arr, int lo, int hi) {
                        int count = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        //@ loop_invariant count >= 0 && count <= i;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] >= lo && arr[i] <= hi) {
                                count++;
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "CountInRange", "countInRange"));
    }

    @Test
    @DisplayName("All positive check with loop and early exit")
    void allPositive() throws IOException {
        String source = """
                public class AllPositive {
                    //@ requires arr != null;
                    public boolean allPositive(int[] arr) {
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] <= 0) return false;
                        }
                        return true;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "AllPositive", "allPositive"));
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
                    //@ requires this.count >= 0;
                    //@ requires this.max > 0;
                    //@ assignable this.count;
                    //@ ensures this.count <= this.max;
                    //@ ensures this.count >= \\old(this.count);
                    public void increment() {
                        if (this.count < this.max) {
                            this.count++;
                        }
                    }
                }
                """;
        assertVerified(verifyMethod(source, "BoundedCounterIncrement", "increment"));
    }

    @Test
    @DisplayName("Toggle boolean field")
    void toggleBoolean() throws IOException {
        String source = """
                public class ToggleBoolean {
                    boolean flag;
                    //@ assignable this.flag;
                    //@ ensures this.flag == !\\old(this.flag);
                    public void toggle() {
                        this.flag = !this.flag;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "ToggleBoolean", "toggle"));
    }

    @Test
    @DisplayName("Accumulate field: addToTotal adds value to running total")
    void accumulateField() throws IOException {
        String source = """
                public class AccumulateField {
                    int total;
                    //@ assignable this.total;
                    //@ ensures this.total == \\old(this.total) + amount;
                    public void addToTotal(int amount) {
                        this.total += amount;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "AccumulateField", "addToTotal"));
    }

    @Test
    @DisplayName("Scale field: multiply field by factor")
    void scaleField() throws IOException {
        String source = """
                public class ScaleField {
                    int value;
                    //@ assignable this.value;
                    //@ ensures this.value == \\old(this.value) * factor;
                    public void scale(int factor) {
                        this.value *= factor;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "ScaleField", "scale"));
    }

    // =========================================================================
    // Complex: combined pre+post on multi-step methods
    // =========================================================================

    @Test
    @DisplayName("Euclidean distance squared: non-negative result")
    void distanceSquared() throws IOException {
        String source = """
                public class DistanceSquared {
                    //@ ensures \\result >= 0;
                    public int distSq(int x1, int y1, int x2, int y2) {
                        int dx = x2 - x1;
                        int dy = y2 - y1;
                        return dx * dx + dy * dy;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "DistanceSquared", "distSq"));
    }

    @Test
    @DisplayName("Midpoint: result between two values")
    void midpoint() throws IOException {
        String source = """
                public class Midpoint {
                    //@ requires a <= b;
                    //@ ensures \\result >= a;
                    //@ ensures \\result <= b;
                    public int midpoint(int a, int b) {
                        return a + (b - a) / 2;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "Midpoint", "midpoint"));
    }

    @Test
    @DisplayName("Safe increment array element: pre+post+frame")
    void safeIncrementArrayElement() throws IOException {
        String source = """
                public class SafeIncrementArrayElement {
                    //@ requires arr != null;
                    //@ requires idx >= 0;
                    //@ requires idx < arr.length;
                    //@ assignable arr[idx];
                    //@ ensures arr[idx] == \\old(arr[idx]) + 1;
                    public void incrementAt(int[] arr, int idx) {
                        arr[idx]++;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "SafeIncrementArrayElement", "incrementAt"));
    }

    @Test
    @DisplayName("Swap array elements: pre+post with \\old")
    void swapArrayElements() throws IOException {
        String source = """
                public class SwapArrayElements {
                    //@ requires arr != null;
                    //@ requires i >= 0 && i < arr.length;
                    //@ requires j >= 0 && j < arr.length;
                    //@ assignable arr[i], arr[j];
                    //@ ensures arr[i] == \\old(arr[j]);
                    //@ ensures arr[j] == \\old(arr[i]);
                    public void swap(int[] arr, int i, int j) {
                        int tmp = arr[i];
                        arr[i] = arr[j];
                        arr[j] = tmp;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "SwapArrayElements", "swap"));
    }

    @Test
    @DisplayName("Array copy returns same-length non-null array")
    void arrayCopyPostcondition() throws IOException {
        String source = """
                public class ArrayCopyPostcondition {
                    //@ requires src != null;
                    //@ ensures \\result != null;
                    //@ ensures \\result.length == src.length;
                    public int[] copyOf(int[] src) {
                        int[] dst = new int[src.length];
                        //@ loop_invariant i >= 0 && i <= src.length;
                        for (int i = 0; i < src.length; i++) {
                            dst[i] = src[i];
                        }
                        return dst;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "ArrayCopyPostcondition", "copyOf"));
    }

    @Test
    @DisplayName("Triple field update: ensures all three changed")
    void tripleFieldUpdate() throws IOException {
        String source = """
                public class TripleFieldUpdate {
                    int r;
                    int g;
                    int b;
                    //@ assignable this.r, this.g, this.b;
                    //@ ensures this.r == red;
                    //@ ensures this.g == green;
                    //@ ensures this.b == blue;
                    public void setColor(int red, int green, int blue) {
                        this.r = red;
                        this.g = green;
                        this.b = blue;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "TripleFieldUpdate", "setColor"));
    }

    @Test
    @DisplayName("Positive modulo: ensures result >= 0")
    void positiveModuloPostcondition() throws IOException {
        String source = """
                public class PositiveModuloPostcondition {
                    //@ requires mod > 0;
                    //@ ensures \\result >= 0;
                    //@ ensures \\result < mod;
                    public int posMod(int val, int mod) {
                        int r = val % mod;
                        if (r < 0) r += mod;
                        return r;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "PositiveModuloPostcondition", "posMod"));
    }

    @Test
    @DisplayName("Stack push: size increases by 1")
    void stackPushPostcondition() throws IOException {
        String source = """
                public class StackPushPostcondition {
                    int[] data;
                    int size;
                    //@ requires this.data != null;
                    //@ requires this.size >= 0;
                    //@ requires this.size < this.data.length;
                    //@ assignable this.data[this.size], this.size;
                    //@ ensures this.size == \\old(this.size) + 1;
                    //@ ensures this.data[\\old(this.size)] == value;
                    public void push(int value) {
                        this.data[this.size] = value;
                        this.size++;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "StackPushPostcondition", "push"));
    }

    @Test
    @DisplayName("Saturating add: result capped at max int")
    void saturatingAdd() throws IOException {
        String source = """
                public class SaturatingAdd {
                    //@ requires a >= 0;
                    //@ requires b >= 0;
                    //@ ensures \\result >= a;
                    //@ ensures \\result >= b;
                    public int saturatingAdd(int a, int b) {
                        long sum = (long)a + (long)b;
                        if (sum > Integer.MAX_VALUE) return Integer.MAX_VALUE;
                        return (int)sum;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "SaturatingAdd", "saturatingAdd"));
    }
}
