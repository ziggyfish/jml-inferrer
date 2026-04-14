package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for edge cases and tricky patterns: empty inputs,
 * boundary conditions, single-element arrays, overflow-prone code,
 * and unusual but valid Java constructs.
 */
class EdgeCaseVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Empty / single element edge cases
    // =========================================================================

    @Test
    @DisplayName("Single-element array: sum returns that element")
    void singleElementSum() throws IOException {
        String source = """
                public class SingleElem {
                    public int sum(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SingleElem", "sum"));
    }

    @Test
    @DisplayName("Empty string returns empty string")
    void emptyStringReturn() throws IOException {
        String source = """
                public class EmptyStr {
                    public String process(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        if (s.isEmpty()) return "";
                        return s.trim();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "EmptyStr", "process"));
    }

    @Test
    @DisplayName("Zero-length array: no-op loop")
    void zeroLengthArray() throws IOException {
        String source = """
                public class ZeroLen {
                    public int process(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ZeroLen", "process"));
    }

    // =========================================================================
    // Boundary / limit conditions
    // =========================================================================

    @Test
    @DisplayName("Clamp to byte range [0, 255]")
    void clampToByte() throws IOException {
        String source = """
                public class ByteClamp {
                    public int clamp(int value) {
                        if (value < 0) return 0;
                        if (value > 255) return 255;
                        return value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ByteClamp", "clamp"));
    }

    @Test
    @DisplayName("Modular increment: wraps at max")
    void modularIncrement() throws IOException {
        String source = """
                public class ModIncr {
                    private int value;
                    private int max;
                    public void increment() {
                        value = (value + 1) % max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ModIncr", "increment"));
    }

    @Test
    @DisplayName("Safe integer addition with overflow check")
    void safeAdd() throws IOException {
        String source = """
                public class SafeAdd {
                    public int safeAdd(int a, int b) {
                        long result = (long) a + (long) b;
                        if (result > Integer.MAX_VALUE) throw new ArithmeticException();
                        if (result < Integer.MIN_VALUE) throw new ArithmeticException();
                        return (int) result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SafeAdd", "safeAdd"));
    }

    @Test
    @DisplayName("Safe integer multiply with overflow check")
    void safeMultiply() throws IOException {
        String source = """
                public class SafeMul {
                    public int safeMul(int a, int b) {
                        long result = (long) a * (long) b;
                        if (result > Integer.MAX_VALUE || result < Integer.MIN_VALUE) {
                            throw new ArithmeticException();
                        }
                        return (int) result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SafeMul", "safeMul"));
    }

    // =========================================================================
    // Boolean logic edge cases
    // =========================================================================

    @Test
    @DisplayName("De Morgan: !(a && b) equivalent")
    void deMorgan() throws IOException {
        String source = """
                public class BoolLogic {
                    public boolean nandEquiv(boolean a, boolean b) {
                        return !a || !b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoolLogic", "nandEquiv"));
    }

    @Test
    @DisplayName("XOR implementation")
    void xorImpl() throws IOException {
        String source = """
                public class BoolLogic2 {
                    public boolean xor(boolean a, boolean b) {
                        return (a || b) && !(a && b);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoolLogic2", "xor"));
    }

    @Test
    @DisplayName("Implies: !a || b")
    void implies() throws IOException {
        String source = """
                public class BoolLogic3 {
                    public boolean implies(boolean a, boolean b) {
                        return !a || b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoolLogic3", "implies"));
    }

    @Test
    @DisplayName("All three true")
    void allThreeTrue() throws IOException {
        String source = """
                public class BoolLogic4 {
                    public boolean allTrue(boolean a, boolean b, boolean c) {
                        return a && b && c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BoolLogic4", "allTrue"));
    }

    // =========================================================================
    // Type conversion / casting edge cases
    // =========================================================================

    @Test
    @DisplayName("Int to double conversion")
    void intToDouble() throws IOException {
        String source = """
                public class TypeConvert {
                    public double toDouble(int n) {
                        return (double) n;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TypeConvert", "toDouble"));
    }

    @Test
    @DisplayName("Double truncation to int")
    void doubleToInt() throws IOException {
        String source = """
                public class TypeConvert2 {
                    public int toInt(double d) {
                        return (int) d;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TypeConvert2", "toInt"));
    }

    @Test
    @DisplayName("Byte extraction from int")
    void byteExtract() throws IOException {
        String source = """
                public class BitOps {
                    public int lowByte(int value) {
                        return value & 0xFF;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitOps", "lowByte"));
    }

    @Test
    @DisplayName("Bit shift operations")
    void bitShift() throws IOException {
        String source = """
                public class BitOps2 {
                    public int shiftLeft(int value, int amount) {
                        if (amount < 0 || amount >= 32) throw new IllegalArgumentException();
                        return value << amount;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitOps2", "shiftLeft"));
    }

    // =========================================================================
    // Recursive-like patterns (iterative implementations)
    // =========================================================================

    @Test
    @DisplayName("Iterative factorial")
    void iterativeFactorial() throws IOException {
        String source = """
                public class Factorial {
                    public long factorial(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        long result = 1;
                        for (int i = 2; i <= n; i++) {
                            result *= i;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Factorial", "factorial"));
    }

    @Test
    @DisplayName("Iterative integer log base 2")
    void iterativeLog2() throws IOException {
        String source = """
                public class Log2 {
                    public int log2(int n) {
                        if (n <= 0) throw new IllegalArgumentException();
                        int result = 0;
                        int val = n;
                        while (val > 1) {
                            val /= 2;
                            result++;
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Log2", "log2"));
    }

    @Test
    @DisplayName("Collatz sequence length")
    void collatzLength() throws IOException {
        String source = """
                public class Collatz {
                    public int collatzSteps(int n) {
                        if (n <= 0) throw new IllegalArgumentException();
                        int steps = 0;
                        int current = n;
                        while (current != 1) {
                            if (current % 2 == 0) {
                                current /= 2;
                            } else {
                                current = 3 * current + 1;
                            }
                            steps++;
                        }
                        return steps;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Collatz", "collatzSteps"));
    }

    // =========================================================================
    // Unusual but valid constructs
    // =========================================================================

    @Test
    @DisplayName("Method with no parameters returning constant")
    void constantReturn() throws IOException {
        String source = """
                public class Constants {
                    public int getMax() {
                        return Integer.MAX_VALUE;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Constants", "getMax"));
    }

    @Test
    @DisplayName("Method with only side effects and void return")
    void voidSideEffect() throws IOException {
        String source = """
                public class SideEffect {
                    private int a;
                    private int b;
                    private int c;
                    public void clearAll() {
                        a = 0;
                        b = 0;
                        c = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SideEffect", "clearAll"));
    }

    @Test
    @DisplayName("Method calling Math.min and Math.max")
    void mathMinMax() throws IOException {
        String source = """
                public class MathOps {
                    public int clamp(int value, int min, int max) {
                        return Math.max(min, Math.min(value, max));
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MathOps", "clamp"));
    }

    @Test
    @DisplayName("Ternary chain for classification")
    void ternaryChain() throws IOException {
        String source = """
                public class TernaryChain {
                    public int sign(int n) {
                        return n > 0 ? 1 : (n < 0 ? -1 : 0);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TernaryChain", "sign"));
    }

    @Test
    @DisplayName("Compound assignment operators")
    void compoundAssignment() throws IOException {
        String source = """
                public class CompoundOps {
                    private int value;
                    public void applyOps(int a, int b) {
                        value += a;
                        value -= b;
                        value *= 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CompoundOps", "applyOps"));
    }

    @Test
    @DisplayName("Multiple local variable computations before return")
    void multipleLocals() throws IOException {
        String source = """
                public class MultiLocal {
                    public int compute(int x, int y, int z) {
                        int sum = x + y + z;
                        int product = x * y;
                        int diff = sum - product;
                        return diff;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiLocal", "compute"));
    }

    @Test
    @DisplayName("Chained comparisons in boolean return")
    void chainedComparisons() throws IOException {
        String source = """
                public class ChainedCmp {
                    public boolean isSorted(int a, int b, int c) {
                        return a <= b && b <= c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ChainedCmp", "isSorted"));
    }

    @Test
    @DisplayName("Conditional increment with return of old value")
    void conditionalIncrementReturnOld() throws IOException {
        String source = """
                public class PostIncr {
                    private int counter;
                    public int getAndIncrement() {
                        int old = counter;
                        counter++;
                        return old;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PostIncr", "getAndIncrement"));
    }
}
