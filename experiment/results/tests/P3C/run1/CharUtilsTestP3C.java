package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3CP3C {

    // --- compare(char x, char y) ---
    // @ensures \result == (x - y);
    @ParameterizedTest
    @CsvSource({
            "a, a, 0",
            "a, b, -1",
            "b, a, 1",
            "A, a, -32", // 'A' (65) - 'a' (97) = -32
            "a, A, 32",  // 'a' (97) - 'A' (65) = 32
            "0, 0, 0",
            "0, 1, -1",
            "1, 0, 1",
            "\\u0000, \\u0000, 0", // NUL character
            "\\uFFFF, \\u0000, 65535", // Max char vs Min char
            "\\u0000, \\uFFFF, -65535",
            "\\u007F, \\u007E, 1", // DEL vs ~
            "\\u007E, \\u007F, -1"
    })
    void testCompare(char x, char y, int expected) {
        assertEquals(expected, CharUtils.compare(x, y));
    }

    // --- isAscii(char ch) ---
    // @ensures \result == (ch >= 0 && ch <= 127);
    @ParameterizedTest
    @ValueSource(chars = {'a', 'Z', '0', '9', ' ', '!', '@', '\n', '\t', '\u007F'})
    void testIsAscii_true(char ch) {
        assertTrue(CharUtils.isAscii(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'\u0080', 'é', 'ñ', 'ü', '€', '😂', '\uFFFF'})
    void testIsAscii_false(char ch) {
        assertFalse(CharUtils.isAscii(ch));
    }

    @Test
    void testIsAscii_boundary() {
        assertTrue(CharUtils.isAscii('\u0000')); // NUL
        assertTrue(CharUtils.isAscii('\u007F')); // DEL
        assertFalse(CharUtils.isAscii('\u0080')); // First non-ASCII
    }

    // --- isAsciiAlpha(char ch) ---
    // @ensures \result == ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z'));
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z', 'm', 'P'})
    void testIsAsciiAlpha_true(char ch) {
        assertTrue(CharUtils.isAsciiAlpha(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'0', '9', ' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000'})
    void testIsAsciiAlpha_false(char ch) {
        assertFalse(CharUtils.isAsciiAlpha(ch));
    }

    @Test
    void testIsAsciiAlpha_boundary() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
        assertFalse(CharUtils.isAsciiAlpha('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlpha('{')); // After 'z'
        assertFalse(CharUtils.isAsciiAlpha('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlpha('[')); // After 'Z'
    }

    // --- isAsciiAlphaLower(char ch) ---
    // @ensures \result == (ch >= 'a' && ch <= 'z');
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'm'})
    void testIsAsciiAlphaLower_true(char ch) {
        assertTrue(CharUtils.isAsciiAlphaLower(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'A', 'Z', '0', '9', ' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000'})
    void testIsAsciiAlphaLower_false(char ch) {
        assertFalse(CharUtils.isAsciiAlphaLower(ch));
    }

    @Test
    void testIsAsciiAlphaLower_boundary() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
        assertFalse(CharUtils.isAsciiAlphaLower('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlphaLower('{')); // After 'z'
        assertFalse(CharUtils.isAsciiAlphaLower('A')); // Upper case
    }

    // --- isAsciiAlphanumeric(char ch) ---
    // @ensures \result == ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9'));
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z', '0', '9', 'm', 'P', '5'})
    void testIsAsciiAlphanumeric_true(char ch) {
        assertTrue(CharUtils.isAsciiAlphanumeric(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000', '-', '+'})
    void testIsAsciiAlphanumeric_false(char ch) {
        assertFalse(CharUtils.isAsciiAlphanumeric(ch));
    }

    @Test
    void testIsAsciiAlphanumeric_boundary() {
        assertTrue(CharUtils.isAsciiAlphanumeric('a'));
        assertTrue(CharUtils.isAsciiAlphanumeric('z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('A'));
        assertTrue(CharUtils.isAsciiAlphanumeric('Z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('0'));
        assertTrue(CharUtils.isAsciiAlphanumeric('9'));
        assertFalse(CharUtils.isAsciiAlphanumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiAlphanumeric(':')); // After '9'
        assertFalse(CharUtils.isAsciiAlphanumeric('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlphanumeric('[')); // After 'Z'
        assertFalse(CharUtils.isAsciiAlphanumeric('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlphanumeric('{')); // After 'z'
    }

    // --- isAsciiAlphaUpper(char ch) ---
    // @ensures \result == (ch >= 'A' && ch <= 'Z');
    @ParameterizedTest
    @ValueSource(chars = {'A', 'Z', 'M'})
    void testIsAsciiAlphaUpper_true(char ch) {
        assertTrue(CharUtils.isAsciiAlphaUpper(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', '0', '9', ' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000'})
    void testIsAsciiAlphaUpper_false(char ch) {
        assertFalse(CharUtils.isAsciiAlphaUpper(ch));
    }

    @Test
    void testIsAsciiAlphaUpper_boundary() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlphaUpper('[')); // After 'Z'
        assertFalse(CharUtils.isAsciiAlphaUpper('a')); // Lower case
    }

    // --- isAsciiControl(char ch) ---
    // @ensures \result == (ch < 32 || ch == 127);
    @ParameterizedTest
    @ValueSource(chars = {'\u0000', '\u0001', '\u001F', '\u007F', '\n', '\t', '\r'})
    void testIsAsciiControl_true(char ch) {
        assertTrue(CharUtils.isAsciiControl(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {' ', 'a', 'Z', '0', '9', '!', '@', 'é', '\u0080'})
    void testIsAsciiControl_false(char ch) {
        assertFalse(CharUtils.isAsciiControl(ch));
    }

    @Test
    void testIsAsciiControl_boundary() {
        assertTrue(CharUtils.isAsciiControl('\u0000')); // NUL
        assertTrue(CharUtils.isAsciiControl('\u001F')); // Unit Separator
        assertFalse(CharUtils.isAsciiControl(' ')); // Space (32)
        assertTrue(CharUtils.isAsciiControl('\u007F')); // DEL
        assertFalse(CharUtils.isAsciiControl('\u007E')); // ~
    }

    // --- isAsciiNumeric(char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '9');
    @ParameterizedTest
    @ValueSource(chars = {'0', '1', '5', '9'})
    void testIsAsciiNumeric_true(char ch) {
        assertTrue(CharUtils.isAsciiNumeric(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'Z', ' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000', '/', ':'})
    void testIsAsciiNumeric_false(char ch) {
        assertFalse(CharUtils.isAsciiNumeric(ch));
    }

    @Test
    void testIsAsciiNumeric_boundary() {
        assertTrue(CharUtils.isAsciiNumeric('0'));
        assertTrue(CharUtils.isAsciiNumeric('9'));
        assertFalse(CharUtils.isAsciiNumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiNumeric(':')); // After '9'
        assertFalse(CharUtils.isAsciiNumeric('a')); // Alpha
    }

    // --- isAsciiPrintable(char ch) ---
    // @ensures \result == (ch >= 32 && ch < 127);
    @ParameterizedTest
    @ValueSource(chars = {' ', 'a', 'Z', '0', '9', '!', '@', '~', '\u007E'})
    void testIsAsciiPrintable_true(char ch) {
        assertTrue(CharUtils.isAsciiPrintable(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'\u0000', '\n', '\t', '\u007F', 'é', '\u0080'})
    void testIsAsciiPrintable_false(char ch) {
        assertFalse(CharUtils.isAsciiPrintable(ch));
    }

    @Test
    void testIsAsciiPrintable_boundary() {
        assertFalse(CharUtils.isAsciiPrintable('\u001F')); // Before space
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space (32)
        assertTrue(CharUtils.isAsciiPrintable('\u007E')); // Tilde (126)
        assertFalse(CharUtils.isAsciiPrintable('\u007F')); // DEL (127)
    }

    // --- isHex(char ch) ---
    // @ensures \result == ((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    @ParameterizedTest
    @ValueSource(chars = {'0', '9', 'a', 'f', 'A', 'F', 'c', 'D'})
    void testIsHex_true(char ch) {
        assertTrue(CharUtils.isHex(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'g', 'G', ' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000', '/', ':'})
    void testIsHex_false(char ch) {
        assertFalse(CharUtils.isHex(ch));
    }

    @Test
    void testIsHex_boundary() {
        assertTrue(CharUtils.isHex('0'));
        assertTrue(CharUtils.isHex('9'));
        assertTrue(CharUtils.isHex('a'));
        assertTrue(CharUtils.isHex('f'));
        assertTrue(CharUtils.isHex('A'));
        assertTrue(CharUtils.isHex('F'));

        assertFalse(CharUtils.isHex('/')); // Before '0'
        assertFalse(CharUtils.isHex(':')); // After '9'
        assertFalse(CharUtils.isHex('`')); // Before 'a'
        assertFalse(CharUtils.isHex('g')); // After 'f'
        assertFalse(CharUtils.isHex('@')); // Before 'A'
        assertFalse(CharUtils.isHex('G')); // After 'F'
    }

    // --- isOctal(char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '7');
    @ParameterizedTest
    @ValueSource(chars = {'0', '1', '5', '7'})
    void testIsOctal_true(char ch) {
        assertTrue(CharUtils.isOctal(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'8', '9', 'a', 'Z', ' ', '!', '@', '\n', '\t', '\u007F', 'é', '\u0000', '/', ':'})
    void testIsOctal_false(char ch) {
        assertFalse(CharUtils.isOctal(ch));
    }

    @Test
    void testIsOctal_boundary() {
        assertTrue(CharUtils.isOctal('0'));
        assertTrue(CharUtils.isOctal('7'));
        assertFalse(CharUtils.isOctal('/')); // Before '0'
        assertFalse(CharUtils.isOctal('8')); // After '7'
        assertFalse(CharUtils.isOctal('a')); // Alpha
    }

    // --- toChar(Character ch) ---
    // @requires ch != null;
    // @ensures \result == ch.charValue();
    @Test
    void testToChar_Character_normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('0', CharUtils.toChar(Character.valueOf('0')));
        assertEquals('\u0000', CharUtils.toChar(Character.valueOf('\u0000')));
        assertEquals('\uFFFF', CharUtils.toChar(Character.valueOf('\uFFFF')));
    }

    @Test
    void testToChar_Character_null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(Character ch, char defaultValue) ---
    // @ensures ch == null ? \result == defaultValue : \result == ch.charValue();
    @Test
    void testToChar_Character_defaultValue_normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'y'));
        assertEquals('0', CharUtils.toChar(Character.valueOf('0'), 'z'));
    }

    @Test
    void testToChar_Character_defaultValue_null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\u0000', CharUtils.toChar(null, '\u0000'));
        assertEquals('\uFFFF', CharUtils.toChar(null, '\uFFFF'));
    }

    // --- toChar(String str) ---
    // @requires str != null && str.length() > 0;
    // @ensures \result == str.charAt(0);
    @Test
    void testToChar_String_normal() {
        assertEquals('a', CharUtils.toChar("abc"));
        assertEquals('Z', CharUtils.toChar("Zebra"));
        assertEquals('0', CharUtils.toChar("0123"));
        assertEquals(' ', CharUtils.toChar(" "));
        assertEquals('\u0000', CharUtils.toChar("\u0000test"));
    }

    @Test
    void testToChar_String_empty() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""));
    }

    @Test
    void testToChar_String_null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(String str, char defaultValue) ---
    // @ensures str == null || str.length() == 0 ? \result == defaultValue : \result == str.charAt(0);
    @Test
    void testToChar_String_defaultValue_normal() {
        assertEquals('a', CharUtils.toChar("abc", 'x'));
        assertEquals('Z', CharUtils.toChar("Zebra", 'y'));
        assertEquals('0', CharUtils.toChar("0123", 'z'));
    }

    @Test
    void testToChar_String_defaultValue_empty() {
        assertEquals('x', CharUtils.toChar("", 'x'));
        assertEquals('\u0000', CharUtils.toChar("", '\u0000'));
    }

    @Test
    void testToChar_String_defaultValue_null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\u0000', CharUtils.toChar(null, '\u0000'));
    }

    // --- toCharacterObject(char c) ---
    // @ensures \result != null && \result.charValue() == c;
    @Test
    void testToCharacterObject_char() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('0'), CharUtils.toCharacterObject('0'));
        assertEquals(Character.valueOf('\u0000'), CharUtils.toCharacterObject('\u0000'));
        assertEquals(Character.valueOf('\uFFFF'), CharUtils.toCharacterObject('\uFFFF'));
    }

    // --- toCharacterObject(String str) ---
    // @ensures str == null || str.length() == 0 ? \result == null : \result.charValue() == str.charAt(0);
    @Test
    void testToCharacterObject_String_normal() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("abc"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Zebra"));
        assertEquals(Character.valueOf('0'), CharUtils.toCharacterObject("0123"));
        assertEquals(Character.valueOf(' '), CharUtils.toCharacterObject(" "));
        assertEquals(Character.valueOf('\u0000'), CharUtils.toCharacterObject("\u0000test"));
    }

    @Test
    void testToCharacterObject_String_empty() {
        assertNull(CharUtils.toCharacterObject(""));
    }

    @Test
    void testToCharacterObject_String_null() {
        assertNull(CharUtils.toCharacterObject(null));
    }

    // --- toIntValue(char ch) ---
    // @requires ch >= '0' && ch <= '9';
    // @ensures \result == Character.getNumericValue(ch);
    @Test
    void testToIntValue_char_normal() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(1, CharUtils.toIntValue('1'));
        assertEquals(5, CharUtils.toIntValue('5'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_char_invalid() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('/'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(':'));
    }

    // --- toIntValue(char ch, int defaultValue) ---
    // @ensures (ch >= '0' && ch <= '9') ? \result == Character.getNumericValue(ch) : \result == defaultValue;
    @Test
    void testToIntValue_char_defaultValue_normal() {
        assertEquals(0, CharUtils.toIntValue('0', -1));
        assertEquals(5, CharUtils.toIntValue('5', -1));
        assertEquals(9, CharUtils.toIntValue('9', -1));
    }

    @Test
    void testToIntValue_char_defaultValue_invalid() {
        assertEquals(-1, CharUtils.toIntValue('a', -1));
        assertEquals(99, CharUtils.toIntValue(' ', 99));
        assertEquals(0, CharUtils.toIntValue('/', 0));
        assertEquals(10, CharUtils.toIntValue(':', 10));
    }

    // --- toIntValue(Character ch) ---
    // @requires ch != null && ch.charValue() >= '0' && ch.charValue() <= '9';
    // @ensures \result == Character.getNumericValue(ch.charValue());
    @Test
    void testToIntValue_Character_normal() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(1, CharUtils.toIntValue(Character.valueOf('1')));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5')));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9')));
    }

    @Test
    void testToIntValue_Character_null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(null));
    }

    @Test
    void testToIntValue_Character_invalid() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(' ')));
    }

    // --- toIntValue(Character ch, int defaultValue) ---
    // @ensures ch == null || !(ch.charValue() >= '0' && ch.charValue() <= '9') ? \result == defaultValue : \result == Character.getNumericValue(ch.charValue());
    @Test
    void testToIntValue_Character_defaultValue_normal() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0'), -1));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5'), -1));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9'), -1));
    }

    @Test
    void testToIntValue_Character_defaultValue_null() {
        assertEquals(-1, CharUtils.toIntValue(null, -1));
        assertEquals(99, CharUtils.toIntValue(null, 99));
    }

    @Test
    void testToIntValue_Character_defaultValue_invalid() {
        assertEquals(-1, CharUtils.toIntValue(Character.valueOf('a'), -1));
        assertEquals(99, CharUtils.toIntValue(Character.valueOf(' '), 99));
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('/'), 0));
        assertEquals(10, CharUtils.toIntValue(Character.valueOf(':'), 10));
    }

    // --- toString(char ch) ---
    // @ensures \result != null && \result.length() == 1 && \result.charAt(0) == ch;
    @Test
    void testToString_char() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("0", CharUtils.toString('0'));
        assertEquals(" ", CharUtils.toString(' '));
        assertEquals("\u0000", CharUtils.toString('\u0000'));
        assertEquals("\uFFFF", CharUtils.toString('\uFFFF'));
    }

    // --- toString(Character ch) ---
    // @ensures ch == null ? \result == null : \result.length() == 1 && \result.charAt(0) == ch.charValue();
    @Test
    void testToString_Character_normal() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("0", CharUtils.toString(Character.valueOf('0')));
        assertEquals(" ", CharUtils.toString(Character.valueOf(' ')));
        assertEquals("\u0000", CharUtils.toString(Character.valueOf('\u0000')));
        assertEquals("\uFFFF", CharUtils.toString(Character.valueOf('\uFFFF')));
    }

    @Test
    void testToString_Character_null() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(char ch) ---
    // @ensures \result != null && \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_char() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(' '));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\u0000'));
        assertEquals("\\uffff", CharUtils.unicodeEscaped('\uFFFF'));
        assertEquals("\\u007f", CharUtils.unicodeEscaped('\u007F')); // DEL
        assertEquals("\\u0080", CharUtils.unicodeEscaped('\u0080')); // First non-ASCII
    }

    // --- unicodeEscaped(Character ch) ---
    // @ensures ch == null ? \result == null : \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_Character_normal() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
        assertEquals("\\u0041", CharUtils.unicodeEscaped(Character.valueOf('A')));
        assertEquals("\\u0030", CharUtils.unicodeEscaped(Character.valueOf('0')));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(Character.valueOf(' ')));
        assertEquals("\\u0000", CharUtils.unicodeEscaped(Character.valueOf('\u0000')));
        assertEquals("\\uffff", CharUtils.unicodeEscaped(Character.valueOf('\uFFFF')));
    }

    @Test
    void testUnicodeEscaped_Character_null() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}