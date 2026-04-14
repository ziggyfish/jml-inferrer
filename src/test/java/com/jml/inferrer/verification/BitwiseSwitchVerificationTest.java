package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for bitwise operations and switch statement patterns:
 * masks, shifts, flags, bit counting, and switch-based dispatch.
 */
class BitwiseSwitchVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Bitwise AND (masking)
    // =========================================================================

    @Test
    @DisplayName("Bitwise: extract low nibble with AND 0x0F")
    void extractLowNibble() throws IOException {
        String source = """
                public class BitMask1 {
                    public int lowNibble(int value) {
                        return value & 0x0F;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitMask1", "lowNibble"));
    }

    @Test
    @DisplayName("Bitwise: extract high byte with shift and mask")
    void extractHighByte() throws IOException {
        String source = """
                public class BitMask2 {
                    public int highByte(int value) {
                        return (value >> 8) & 0xFF;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitMask2", "highByte"));
    }

    @Test
    @DisplayName("Bitwise: check if bit is set")
    void checkBitSet() throws IOException {
        String source = """
                public class BitCheck1 {
                    public boolean isBitSet(int value, int bit) {
                        if (bit < 0 || bit >= 32) throw new IllegalArgumentException();
                        return (value & (1 << bit)) != 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitCheck1", "isBitSet"));
    }

    @Test
    @DisplayName("Bitwise: check even/odd via AND 1")
    void checkEvenOdd() throws IOException {
        String source = """
                public class BitCheck2 {
                    public boolean isEven(int n) {
                        return (n & 1) == 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitCheck2", "isEven"));
    }

    @Test
    @DisplayName("Bitwise: check power of two")
    void checkPowerOfTwo() throws IOException {
        String source = """
                public class BitCheck3 {
                    public boolean isPowerOfTwo(int n) {
                        if (n <= 0) return false;
                        return (n & (n - 1)) == 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitCheck3", "isPowerOfTwo"));
    }

    // =========================================================================
    // Bitwise OR (flag setting)
    // =========================================================================

    @Test
    @DisplayName("Bitwise: set bit at position")
    void setBit() throws IOException {
        String source = """
                public class BitSet1 {
                    public int setBit(int value, int bit) {
                        if (bit < 0 || bit >= 32) throw new IllegalArgumentException();
                        return value | (1 << bit);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitSet1", "setBit"));
    }

    @Test
    @DisplayName("Bitwise: combine two flag sets")
    void combineFlags() throws IOException {
        String source = """
                public class BitFlags1 {
                    public int combine(int flags1, int flags2) {
                        return flags1 | flags2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitFlags1", "combine"));
    }

    @Test
    @DisplayName("Bitwise: set permission flags on field")
    void setPermissionFlags() throws IOException {
        String source = """
                public class Permissions {
                    private int flags;
                    public static final int READ = 1;
                    public static final int WRITE = 2;
                    public static final int EXEC = 4;
                    public void addPermission(int perm) {
                        flags |= perm;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Permissions", "addPermission"));
    }

    // =========================================================================
    // Bitwise XOR
    // =========================================================================

    @Test
    @DisplayName("Bitwise: XOR swap two fields")
    void xorSwap() throws IOException {
        String source = """
                public class BitXor1 {
                    private int a;
                    private int b;
                    public void xorSwap() {
                        a = a ^ b;
                        b = a ^ b;
                        a = a ^ b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitXor1", "xorSwap"));
    }

    @Test
    @DisplayName("Bitwise: toggle bit at position")
    void toggleBit() throws IOException {
        String source = """
                public class BitXor2 {
                    public int toggleBit(int value, int bit) {
                        if (bit < 0 || bit >= 32) throw new IllegalArgumentException();
                        return value ^ (1 << bit);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitXor2", "toggleBit"));
    }

    // =========================================================================
    // Bitwise shifts
    // =========================================================================

    @Test
    @DisplayName("Bitwise: multiply by power of 2 via left shift")
    void multiplyByShift() throws IOException {
        String source = """
                public class BitShift1 {
                    public int multiplyBy8(int value) {
                        return value << 3;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitShift1", "multiplyBy8"));
    }

    @Test
    @DisplayName("Bitwise: divide by power of 2 via right shift")
    void divideByShift() throws IOException {
        String source = """
                public class BitShift2 {
                    public int divideBy4(int value) {
                        if (value < 0) throw new IllegalArgumentException();
                        return value >>> 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitShift2", "divideBy4"));
    }

    @Test
    @DisplayName("Bitwise: count leading zeros iteratively")
    void countLeadingZeros() throws IOException {
        String source = """
                public class BitCount1 {
                    public int countLeadingZeros(int value) {
                        if (value == 0) return 32;
                        int count = 0;
                        int v = value;
                        while ((v & 0x80000000) == 0) {
                            count++;
                            v <<= 1;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitCount1", "countLeadingZeros"));
    }

    @Test
    @DisplayName("Bitwise: count set bits (popcount)")
    void popcount() throws IOException {
        String source = """
                public class BitCount2 {
                    public int popcount(int value) {
                        int count = 0;
                        int v = value;
                        while (v != 0) {
                            count += v & 1;
                            v >>>= 1;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitCount2", "popcount"));
    }

    // =========================================================================
    // Byte/word packing and unpacking
    // =========================================================================

    @Test
    @DisplayName("Bitwise: pack two shorts into int")
    void packTwoShorts() throws IOException {
        String source = """
                public class BitPack1 {
                    public int pack(short high, short low) {
                        return ((int) high << 16) | (low & 0xFFFF);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitPack1", "pack"));
    }

    @Test
    @DisplayName("Bitwise: unpack high short from int")
    void unpackHighShort() throws IOException {
        String source = """
                public class BitPack2 {
                    public short unpackHigh(int packed) {
                        return (short) (packed >> 16);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BitPack2", "unpackHigh"));
    }

    @Test
    @DisplayName("Bitwise: pack RGB into single int")
    void packRGB() throws IOException {
        String source = """
                public class ColorPack {
                    public int packRGB(int r, int g, int b) {
                        if (r < 0 || r > 255) throw new IllegalArgumentException();
                        if (g < 0 || g > 255) throw new IllegalArgumentException();
                        if (b < 0 || b > 255) throw new IllegalArgumentException();
                        return (r << 16) | (g << 8) | b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ColorPack", "packRGB"));
    }

    // =========================================================================
    // Switch with complex patterns
    // =========================================================================

    @Test
    @DisplayName("Switch: dispatch to different calculations")
    void switchDispatchCalc() throws IOException {
        String source = """
                public class SwitchCalc {
                    public double calculate(double a, double b, String op) {
                        if (op == null) throw new IllegalArgumentException();
                        switch (op) {
                            case "+": return a + b;
                            case "-": return a - b;
                            case "*": return a * b;
                            case "/":
                                if (b == 0.0) throw new ArithmeticException();
                                return a / b;
                            default: throw new IllegalArgumentException();
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchCalc", "calculate"));
    }

    @Test
    @DisplayName("Switch: return string mapping")
    void switchStringMapping() throws IOException {
        String source = """
                public class SwitchMap1 {
                    public String monthName(int month) {
                        switch (month) {
                            case 1: return "January";
                            case 2: return "February";
                            case 3: return "March";
                            case 4: return "April";
                            case 5: return "May";
                            case 6: return "June";
                            case 7: return "July";
                            case 8: return "August";
                            case 9: return "September";
                            case 10: return "October";
                            case 11: return "November";
                            case 12: return "December";
                            default: throw new IllegalArgumentException();
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchMap1", "monthName"));
    }

    @Test
    @DisplayName("Switch: state transition with field update")
    void switchStateTransition() throws IOException {
        String source = """
                public class SwitchState {
                    private int state;
                    public void handleEvent(int event) {
                        switch (state) {
                            case 0:
                                if (event == 1) state = 1;
                                break;
                            case 1:
                                if (event == 2) state = 2;
                                else if (event == 3) state = 0;
                                break;
                            case 2:
                                if (event == 0) state = 0;
                                break;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchState", "handleEvent"));
    }

    @Test
    @DisplayName("Switch expression: arrow syntax with computation")
    void switchExpressionArrow() throws IOException {
        String source = """
                public class SwitchExpr1 {
                    public int fibonacci(int n) {
                        if (n < 0 || n > 6) throw new IllegalArgumentException();
                        return switch (n) {
                            case 0 -> 0;
                            case 1 -> 1;
                            case 2 -> 1;
                            case 3 -> 2;
                            case 4 -> 3;
                            case 5 -> 5;
                            case 6 -> 8;
                            default -> throw new IllegalArgumentException();
                        };
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchExpr1", "fibonacci"));
    }

    @Test
    @DisplayName("Switch: fall-through with shared logic")
    void switchFallThrough() throws IOException {
        String source = """
                public class SwitchFall1 {
                    public boolean isVowel(char c) {
                        switch (c) {
                            case 'a': case 'e': case 'i': case 'o': case 'u':
                            case 'A': case 'E': case 'I': case 'O': case 'U':
                                return true;
                            default:
                                return false;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchFall1", "isVowel"));
    }
}
