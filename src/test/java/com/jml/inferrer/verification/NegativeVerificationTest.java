package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Tier 1 negative tests: intentionally wrong JML specs that should FAIL verification.
 * These validate that OpenJML correctly rejects unsound specifications.
 */
class NegativeVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Wrong arithmetic postconditions
    // =========================================================================

    @Test
    @DisplayName("Wrong arithmetic result: ensures \\result == a - b (but returns a + b)")
    void wrongArithmeticResult() throws IOException {
        String source = """
                public class WrongArithmeticResult {
                    //@ ensures \\result == a - b;
                    public int add(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongArithmeticResult", "add"));
    }

    @Test
    @DisplayName("Wrong multiplication: ensures \\result == a + b (but returns a * b)")
    void wrongMultiplication() throws IOException {
        String source = """
                public class WrongMultiplication {
                    //@ ensures \\result == a + b;
                    public int multiply(int a, int b) {
                        return a * b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongMultiplication", "multiply"));
    }

    @Test
    @DisplayName("Wrong negation: ensures \\result == x (but returns -x)")
    void wrongNegation() throws IOException {
        String source = """
                public class WrongNegation {
                    //@ ensures \\result == x;
                    public int negate(int x) {
                        return -x;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongNegation", "negate"));
    }

    @Test
    @DisplayName("Wrong compound: ensures \\result == a * b - c (but returns a * b + c)")
    void wrongCompound() throws IOException {
        String source = """
                public class WrongCompound {
                    //@ ensures \\result == a * b - c;
                    public int compute(int a, int b, int c) {
                        return a * b + c;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongCompound", "compute"));
    }

    // =========================================================================
    // Missing null checks
    // =========================================================================

    @Test
    @DisplayName("Missing null check: s.length() with nullable param")
    void missingNullCheck() throws IOException {
        String source = """
                public class MissingNullCheck {
                    //@ requires s == null || s != null;
                    //@ ensures \\result >= 0;
                    public int getLength(/*@ nullable @*/ String s) {
                        return s.length();
                    }
                }
                """;
        assertFailed(verifyMethod(source, "MissingNullCheck", "getLength"));
    }

    @Test
    @DisplayName("Missing null check on second param: b.length() unguarded")
    void missingSecondNullCheck() throws IOException {
        String source = """
                public class MissingSecondNullCheck {
                    //@ requires a != null;
                    public int totalLength(String a, /*@ nullable @*/ String b) {
                        return a.length() + b.length();
                    }
                }
                """;
        assertFailed(verifyMethod(source, "MissingSecondNullCheck", "totalLength"));
    }

    @Test
    @DisplayName("Missing null check on array: arr[0] with nullable arr")
    void missingArrayNullCheck() throws IOException {
        String source = """
                public class MissingArrayNullCheck {
                    //@ ensures \\result >= 0;
                    public int first(/*@ nullable @*/ int[] arr) {
                        return arr[0];
                    }
                }
                """;
        assertFailed(verifyMethod(source, "MissingArrayNullCheck", "first"));
    }

    // =========================================================================
    // Wrong bound postconditions
    // =========================================================================

    @Test
    @DisplayName("Wrong bound: ensures \\result < 0 (but x*x >= 0)")
    void wrongBound() throws IOException {
        String source = """
                public class WrongBound {
                    //@ ensures \\result < 0;
                    public int square(int x) {
                        return x * x;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongBound", "square"));
    }

    @Test
    @DisplayName("Wrong sign: ensures \\result <= 0 (but abs always >= 0)")
    void wrongSign() throws IOException {
        String source = """
                public class WrongSign {
                    //@ ensures \\result <= 0;
                    public int absVal(int x) {
                        return x >= 0 ? x : -x;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongSign", "absVal"));
    }

    @Test
    @DisplayName("Wrong max postcondition: result <= a but should be >= a")
    void wrongMax() throws IOException {
        String source = """
                public class WrongMax {
                    //@ ensures \\result <= a;
                    //@ ensures \\result <= b;
                    public int max(int a, int b) {
                        return a >= b ? a : b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongMax", "max"));
    }

    @Test
    @DisplayName("Wrong min postcondition: result >= a but should be <= a")
    void wrongMin() throws IOException {
        String source = """
                public class WrongMin {
                    //@ ensures \\result >= a;
                    //@ ensures \\result >= b;
                    public int min(int a, int b) {
                        return a <= b ? a : b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongMin", "min"));
    }

    // =========================================================================
    // Wrong field postconditions
    // =========================================================================

    @Test
    @DisplayName("Wrong field postcondition: ensures count unchanged (but it increments)")
    void wrongFieldPostcondition() throws IOException {
        String source = """
                public class WrongFieldPostcondition {
                    public int count;
                    //@ assignable this.count;
                    //@ ensures this.count == \\old(this.count);
                    public void increment() {
                        this.count++;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongFieldPostcondition", "increment"));
    }

    @Test
    @DisplayName("Wrong field: ensures value == v + 1 (but sets to v)")
    void wrongFieldValue() throws IOException {
        String source = """
                public class WrongFieldValue {
                    public int value;
                    //@ assignable this.value;
                    //@ ensures this.value == v + 1;
                    public void setValue(int v) {
                        this.value = v;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongFieldValue", "setValue"));
    }

    @Test
    @DisplayName("Wrong swap: ensures a == \\old(a) (but actually swapped)")
    void wrongSwap() throws IOException {
        String source = """
                public class WrongSwap {
                    public int a;
                    public int b;
                    //@ assignable this.a, this.b;
                    //@ ensures this.a == \\old(this.a);
                    //@ ensures this.b == \\old(this.b);
                    public void swap() {
                        int tmp = this.a;
                        this.a = this.b;
                        this.b = tmp;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongSwap", "swap"));
    }

    @Test
    @DisplayName("Wrong toggle: ensures flag == \\old(flag) (but it toggles)")
    void wrongToggle() throws IOException {
        String source = """
                public class WrongToggle {
                    public boolean flag;
                    //@ assignable this.flag;
                    //@ ensures this.flag == \\old(this.flag);
                    public void toggle() {
                        this.flag = !this.flag;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongToggle", "toggle"));
    }

    // =========================================================================
    // Wrong loop invariants
    // =========================================================================

    @Test
    @DisplayName("Wrong loop invariant: loop_invariant i < 0 (but i starts at 0)")
    void wrongLoopInvariant() throws IOException {
        String source = """
                public class WrongLoopInvariant {
                    //@ requires n >= 0;
                    public void count(int n) {
                        //@ loop_invariant i < 0;
                        for (int i = 0; i < n; i++) {
                        }
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongLoopInvariant", "count"));
    }

    @Test
    @DisplayName("Wrong loop invariant: i > n (but i starts at 0 and goes up to n)")
    void wrongLoopUpperBound() throws IOException {
        String source = """
                public class WrongLoopUpperBound {
                    //@ requires n >= 0;
                    public void count(int n) {
                        //@ loop_invariant i > n;
                        for (int i = 0; i < n; i++) {
                        }
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongLoopUpperBound", "count"));
    }

    @Test
    @DisplayName("Wrong loop invariant: count < 0 (but count is incremented)")
    void wrongCounterInvariant() throws IOException {
        String source = """
                public class WrongCounterInvariant {
                    //@ requires arr != null;
                    public int countPos(int[] arr) {
                        int count = 0;
                        //@ loop_invariant count < 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) count++;
                        }
                        return count;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongCounterInvariant", "countPos"));
    }

    // =========================================================================
    // Missing array bounds
    // =========================================================================

    @Test
    @DisplayName("Missing array bounds: access arr[5] without length check")
    void missingArrayBounds() throws IOException {
        String source = """
                public class MissingArrayBounds {
                    //@ requires arr != null;
                    public int getFifth(int[] arr) {
                        return arr[5];
                    }
                }
                """;
        assertFailed(verifyMethod(source, "MissingArrayBounds", "getFifth"));
    }

    @Test
    @DisplayName("Missing index bound: arr[idx] without idx < arr.length")
    void missingIndexBound() throws IOException {
        String source = """
                public class MissingIndexBound {
                    //@ requires arr != null;
                    //@ requires idx >= 0;
                    public int getAt(int[] arr, int idx) {
                        return arr[idx];
                    }
                }
                """;
        assertFailed(verifyMethod(source, "MissingIndexBound", "getAt"));
    }

    // =========================================================================
    // Wrong assignable / frame conditions
    // =========================================================================

    @Test
    @DisplayName("Wrong assignable nothing: modifies field")
    void wrongAssignableNothing() throws IOException {
        String source = """
                public class WrongAssignableNothing {
                    public int value;
                    //@ assignable \\nothing;
                    public void setValue(int v) {
                        this.value = v;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongAssignableNothing", "setValue"));
    }

    @Test
    @DisplayName("Wrong assignable: declares x but also modifies y")
    void wrongAssignableIncomplete() throws IOException {
        String source = """
                public class WrongAssignableIncomplete {
                    public int x;
                    public int y;
                    //@ assignable this.x;
                    public void setBoth(int a, int b) {
                        this.x = a;
                        this.y = b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongAssignableIncomplete", "setBoth"));
    }

    // =========================================================================
    // Complex wrong specifications
    // =========================================================================

    @Test
    @DisplayName("Wrong division precondition: allows zero divisor")
    void wrongDivisionPrecondition() throws IOException {
        String source = """
                public class WrongDivisionPrecondition {
                    //@ requires b >= 0;
                    public int divide(int a, int b) {
                        return a / b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongDivisionPrecondition", "divide"));
    }

    @Test
    @DisplayName("Wrong postcondition on branch: only holds for one path")
    void wrongBranchPostcondition() throws IOException {
        String source = """
                public class WrongBranchPostcondition {
                    //@ ensures \\result > 0;
                    public int signBad(int x) {
                        if (x > 0) return 1;
                        if (x < 0) return -1;
                        return 0;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongBranchPostcondition", "signBad"));
    }

    @Test
    @DisplayName("Wrong postcondition: result == a for max (wrong when b > a)")
    void wrongMaxAlwaysA() throws IOException {
        String source = """
                public class WrongMaxAlwaysA {
                    //@ ensures \\result == a;
                    public int max(int a, int b) {
                        return a >= b ? a : b;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongMaxAlwaysA", "max"));
    }

    @Test
    @DisplayName("Wrong stack postcondition: size unchanged after push")
    void wrongStackPush() throws IOException {
        String source = """
                public class WrongStackPush {
                    public int[] data;
                    public int size;
                    //@ requires this.data != null;
                    //@ requires this.size >= 0;
                    //@ requires this.size < this.data.length;
                    //@ assignable this.data[this.size], this.size;
                    //@ ensures this.size == \\old(this.size);
                    public void push(int value) {
                        this.data[this.size] = value;
                        this.size++;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongStackPush", "push"));
    }

    @Test
    @DisplayName("Wrong loop postcondition: count == arr.length (not always true)")
    void wrongLoopPostcondition() throws IOException {
        String source = """
                public class WrongLoopPostcondition {
                    //@ requires arr != null;
                    //@ ensures \\result == arr.length;
                    public int countPositive(int[] arr) {
                        int count = 0;
                        //@ loop_invariant i >= 0 && i <= arr.length;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) count++;
                        }
                        return count;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongLoopPostcondition", "countPositive"));
    }

    @Test
    @DisplayName("Wrong new array postcondition: result.length == n + 1 (should be n)")
    void wrongNewArrayLength() throws IOException {
        String source = """
                public class WrongNewArrayLength {
                    //@ requires n >= 0;
                    //@ ensures \\result != null;
                    //@ ensures \\result.length == n + 1;
                    public int[] makeArray(int n) {
                        return new int[n];
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongNewArrayLength", "makeArray"));
    }

    @Test
    @DisplayName("Wrong midpoint: ensures result > b (impossible when a <= b)")
    void wrongMidpoint() throws IOException {
        String source = """
                public class WrongMidpoint {
                    //@ requires a <= b;
                    //@ ensures \\result > b;
                    public int midpoint(int a, int b) {
                        return a + (b - a) / 2;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongMidpoint", "midpoint"));
    }

    @Test
    @DisplayName("Wrong accumulate: ensures total == \\old(total) - amount")
    void wrongAccumulate() throws IOException {
        String source = """
                public class WrongAccumulate {
                    public int total;
                    //@ assignable this.total;
                    //@ ensures this.total == \\old(this.total) - amount;
                    public void add(int amount) {
                        this.total += amount;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongAccumulate", "add"));
    }

    @Test
    @DisplayName("Wrong builder: ensures result != this (but returns this)")
    void wrongBuilderReturn() throws IOException {
        String source = """
                public class WrongBuilderReturn {
                    public int value;
                    //@ assignable this.value;
                    //@ ensures \\result != this;
                    public WrongBuilderReturn withValue(int v) {
                        this.value = v;
                        return this;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongBuilderReturn", "withValue"));
    }

    @Test
    @DisplayName("Wrong array swap: elements stay in place")
    void wrongArraySwap() throws IOException {
        String source = """
                public class WrongArraySwap {
                    //@ requires arr != null;
                    //@ requires i >= 0 && i < arr.length;
                    //@ requires j >= 0 && j < arr.length;
                    //@ assignable arr[i], arr[j];
                    //@ ensures arr[i] == \\old(arr[i]);
                    //@ ensures arr[j] == \\old(arr[j]);
                    public void swap(int[] arr, int i, int j) {
                        int tmp = arr[i];
                        arr[i] = arr[j];
                        arr[j] = tmp;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongArraySwap", "swap"));
    }

    @Test
    @DisplayName("Wrong percentage: ensures result > 100 (impossible)")
    void wrongPercentage() throws IOException {
        String source = """
                public class WrongPercentage {
                    //@ requires total > 0;
                    //@ requires part >= 0;
                    //@ requires part <= total;
                    //@ ensures \\result > 100;
                    public int percentage(int part, int total) {
                        return (part * 100) / total;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongPercentage", "percentage"));
    }

    @Test
    @DisplayName("Wrong clamp: ensures result > hi (impossible when clamped)")
    void wrongClamp() throws IOException {
        String source = """
                public class WrongClamp {
                    //@ requires lo <= hi;
                    //@ ensures \\result > hi;
                    public int clamp(int val, int lo, int hi) {
                        if (val < lo) return lo;
                        if (val > hi) return hi;
                        return val;
                    }
                }
                """;
        assertFailed(verifyMethod(source, "WrongClamp", "clamp"));
    }
}
