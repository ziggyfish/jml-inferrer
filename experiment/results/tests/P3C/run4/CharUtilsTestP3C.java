package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3CP3C {

    // --- compare(char x, char y) ---
    // JML: @ensures \result == (x - y);
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
            "!, !, 0",
            "!, @, -1",
            "~, }, 1",
            "\\u0000, \\u0000, 0",
            "\\u0000, \\u0001, -1",
            "\\uFFFF, \\uFFFE, 1",
            "\\u0000, a, -97",
            "a, \\u0000, 97"
    })
    void testCompare(char x, char y, int expected) {
        assertEquals(expected, CharUtils.compare(x, y));
    }

    // --- isAscii(char ch) ---
    // JML: @ensures \result == (ch >= 0 && ch <= 127);
    @ParameterizedTest
    @ValueSource(chars = {'a', 'Z', '0', '9', '!', '@', '~', ' ', '\n', '\r', '\t', '\u0000', '\u007F'})
    void testIsAscii_true(char ch) {
        assertTrue(CharUtils.isAscii(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'\u0080', '\u00FF', 'é', 'ñ', '€', '😂', '\uFFFF'})
    void testIsAscii_false(char ch) {
        assertFalse(CharUtils.isAscii(ch));
    }

    // --- isAsciiAlpha(char ch) ---
    // JML: @ensures \result == ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z'));
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z'})
    void testIsAsciiAlpha_true(char ch) {
        assertTrue(CharUtils.isAsciiAlpha(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'0', '9', '!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsAsciiAlpha_false(char ch) {
        assertFalse(CharUtils.isAsciiAlpha(ch));
    }

    // --- isAsciiAlphaLower(char ch) ---
    // JML: @ensures \result == (ch >= 'a' && ch <= 'z');
    @ParameterizedTest
    @ValueSource(chars = {'a', 'm', 'z'})
    void testIsAsciiAlphaLower_true(char ch) {
        assertTrue(CharUtils.isAsciiAlphaLower(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'A', 'Z', '0', '9', '!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsAsciiAlphaLower_false(char ch) {
        assertFalse(CharUtils.isAsciiAlphaLower(ch));
    }

    // --- isAsciiAlphanumeric(char ch) ---
    // JML: @ensures \result == ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9'));
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z', '0', '9'})
    void testIsAsciiAlphanumeric_true(char ch) {
        assertTrue(CharUtils.isAsciiAlphanumeric(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsAsciiAlphanumeric_false(char ch) {
        assertFalse(CharUtils.isAsciiAlphanumeric(ch));
    }

    // --- isAsciiAlphaUpper(char ch) ---
    // JML: @ensures \result == (ch >= 'A' && ch <= 'Z');
    @ParameterizedTest
    @ValueSource(chars = {'A', 'M', 'Z'})
    void testIsAsciiAlphaUpper_true(char ch) {
        assertTrue(CharUtils.isAsciiAlphaUpper(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', '0', '9', '!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsAsciiAlphaUpper_false(char ch) {
        assertFalse(CharUtils.isAsciiAlphaUpper(ch));
    }

    // --- isAsciiControl(char ch) ---
    // JML: @ensures \result == (ch < 32 || ch == 127);
    @ParameterizedTest
    @ValueSource(chars = {'\u0000', '\u0001', '\u001F', '\u007F', '\n', '\r', '\t'})
    void testIsAsciiControl_true(char ch) {
        assertTrue(CharUtils.isAsciiControl(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {' ', '!', 'a', 'Z', '0', '9', '\u0020', '\u007E', '\u0080', 'é'})
    void testIsAsciiControl_false(char ch) {
        assertFalse(CharUtils.isAsciiControl(ch));
    }

    // --- isAsciiNumeric(char ch) ---
    // JML: @ensures \result == (ch >= '0' && ch <= '9');
    @ParameterizedTest
    @ValueSource(chars = {'0', '5', '9'})
    void testIsAsciiNumeric_true(char ch) {
        assertTrue(CharUtils.isAsciiNumeric(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z', '!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsAsciiNumeric_false(char ch) {
        assertFalse(CharUtils.isAsciiNumeric(ch));
    }

    // --- isAsciiPrintable(char ch) ---
    // JML: @ensures \result == (ch >= 32 && ch < 127);
    @ParameterizedTest
    @ValueSource(chars = {' ', '!', '@', 'a', 'Z', '0', '9', '~', '\u0020', '\u007E'})
    void testIsAsciiPrintable_true(char ch) {
        assertTrue(CharUtils.isAsciiPrintable(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'\u0000', '\u001F', '\u007F', '\n', '\r', '\t', '\u0080', 'é'})
    void testIsAsciiPrintable_false(char ch) {
        assertFalse(CharUtils.isAsciiPrintable(ch));
    }

    // --- isHex(char ch) ---
    // JML: @ensures \result == ((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    @ParameterizedTest
    @ValueSource(chars = {'0', '9', 'a', 'f', 'A', 'F'})
    void testIsHex_true(char ch) {
        assertTrue(CharUtils.isHex(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'g', 'G', '!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsHex_false(char ch) {
        assertFalse(CharUtils.isHex(ch));
    }

    // --- isOctal(char ch) ---
    // JML: @ensures \result == (ch >= '0' && ch <= '7');
    @ParameterizedTest
    @ValueSource(chars = {'0', '7'})
    void testIsOctal_true(char ch) {
        assertTrue(CharUtils.isOctal(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'8', '9', 'a', 'A', '!', '@', ' ', '\n', '\u0000', '\u007F', 'é', '\u0080'})
    void testIsOctal_false(char ch) {
        assertFalse(CharUtils.isOctal(ch));
    }

    // --- toChar(Character ch) ---
    // JML: @requires ch != null;
    // JML: @ensures \result == ch.charValue();
    @Test
    void testToChar_Character_normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('0', CharUtils.toChar(Character.valueOf('0')));
        assertEquals(' ', CharUtils.toChar(Character.valueOf(' ')));
        assertEquals('\u0000', CharUtils.toChar(Character.valueOf('\u0000')));
        assertEquals('\uFFFF', CharUtils.toChar(Character.valueOf('\uFFFF')));
    }

    @Test
    void testToChar_Character_null() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(Character ch, char defaultValue) ---
    // JML: @ensures ch == null ? \result == defaultValue : \result == ch.charValue();
    @Test
    void testToChar_Character_defaultValue_normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'x'));
        assertEquals('0', CharUtils.toChar(Character.valueOf('0'), 'x'));
    }

    @Test
    void testToChar_Character_defaultValue_null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\u0000', CharUtils.toChar(null, '\u0000'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    // --- toChar(String str) ---
    // JML: @requires str != null && str.length() > 0;
    // JML: @ensures \result == str.charAt(0);
    @Test
    void testToChar_String_normal() {
        assertEquals('a', CharUtils.toChar("abc"));
        assertEquals('Z', CharUtils.toChar("Zebra"));
        assertEquals('0', CharUtils.toChar("0123"));
        assertEquals(' ', CharUtils.toChar(" "));
        assertEquals('\u0000', CharUtils.toChar("\u0000test"));
    }

    @Test
    void testToChar_String_null() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar(null));
    }

    @Test
    void testToChar_String_empty() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""));
    }

    // --- toChar(String str, char defaultValue) ---
    // JML: @ensures str == null || str.length() == 0 ? \result == defaultValue : \result == str.charAt(0);
    @Test
    void testToChar_String_defaultValue_normal() {
        assertEquals('a', CharUtils.toChar("abc", 'x'));
        assertEquals('Z', CharUtils.toChar("Zebra", 'x'));
        assertEquals('0', CharUtils.toChar("0123", 'x'));
    }

    @Test
    void testToChar_String_defaultValue_null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\u0000', CharUtils.toChar(null, '\u0000'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    @Test
    void testToChar_String_defaultValue_empty() {
        assertEquals('x', CharUtils.toChar("", 'x'));
        assertEquals('\u0000', CharUtils.toChar("", '\u0000'));
        assertEquals(' ', CharUtils.toChar("", ' '));
    }

    // --- toCharacterObject(char c) ---
    // JML: @ensures \result != null && \result.charValue() == c;
    @Test
    void testToCharacterObject_char() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('0'), CharUtils.toCharacterObject('0'));
        assertEquals(Character.valueOf(' '), CharUtils.toCharacterObject(' '));
        assertEquals(Character.valueOf('\u0000'), CharUtils.toCharacterObject('\u0000'));
        assertEquals(Character.valueOf('\uFFFF'), CharUtils.toCharacterObject('\uFFFF'));
    }

    // --- toCharacterObject(String str) ---
    // JML: @ensures str == null || str.length() == 0 ? \result == null : \result.charValue() == str.charAt(0);
    @Test
    void testToCharacterObject_String_normal() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("abc"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Zebra"));
        assertEquals(Character.valueOf('0'), CharUtils.toCharacterObject("0123"));
        assertEquals(Character.valueOf(' '), CharUtils.toCharacterObject(" "));
        assertEquals(Character.valueOf('\u0000'), CharUtils.toCharacterObject("\u0000test"));
    }

    @Test
    void testToCharacterObject_String_null() {
        assertNull(CharUtils.toCharacterObject(null));
    }

    @Test
    void testToCharacterObject_String_empty() {
        assertNull(CharUtils.toCharacterObject(""));
    }

    // --- toIntValue(char ch) ---
    // JML: @requires ch >= '0' && ch <= '9';
    // JML: @ensures \result == Character.getNumericValue(ch);
    @ParameterizedTest
    @CsvSource({
            "0, 0",
            "1, 1",
            "5, 5",
            "9, 9"
    })
    void testToIntValue_char_normal(char ch, int expected) {
        assertEquals(expected, CharUtils.toIntValue(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'A', '!', ' '})
    void testToIntValue_char_invalid(char ch) {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(ch));
    }

    // --- toIntValue(char ch, int defaultValue) ---
    // JML: @ensures (ch >= '0' && ch <= '9') ? \result == Character.getNumericValue(ch) : \result == defaultValue;
    @ParameterizedTest
    @CsvSource({
            "0, 99, 0",
            "1, 99, 1",
            "5, 99, 5",
            "9, 99, 9"
    })
    void testToIntValue_char_defaultValue_valid(char ch, int defaultValue, int expected) {
        assertEquals(expected, CharUtils.toIntValue(ch, defaultValue));
    }

    @ParameterizedTest
    @CsvSource({
            "a, 99, 99",
            "A, 99, 99",
            "!, 99, 99",
            " , 99, 99",
            "\\u0000, 99, 99",
            "é, 99, 99"
    })
    void testToIntValue_char_defaultValue_invalid(char ch, int defaultValue, int expected) {
        assertEquals(expected, CharUtils.toIntValue(ch, defaultValue));
    }

    // --- toIntValue(Character ch) ---
    // JML: @requires ch != null && ch >= '0' && ch <= '9';
    // JML: @ensures \result == Character.getNumericValue(ch);
    @ParameterizedTest
    @CsvSource({
            "0, 0",
            "1, 1",
            "5, 5",
            "9, 9"
    })
    void testToIntValue_Character_normal(char ch, int expected) {
        assertEquals(expected, CharUtils.toIntValue(Character.valueOf(ch)));
    }

    @Test
    void testToIntValue_Character_null() {
        assertThrows(NullPointerException.class, () -> CharUtils.toIntValue(null));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'A', '!', ' '})
    void testToIntValue_Character_invalid(char ch) {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(ch)));
    }

    // --- toIntValue(Character ch, int defaultValue) ---
    // JML: @ensures ch == null || !(ch >= '0' && ch <= '9') ? \result == defaultValue : \result == Character.getNumericValue(ch);
    @ParameterizedTest
    @CsvSource({
            "0, 99, 0",
            "1, 99, 1",
            "5, 99, 5",
            "9, 99, 9"
    })
    void testToIntValue_Character_defaultValue_valid(char ch, int defaultValue, int expected) {
        assertEquals(expected, CharUtils.toIntValue(Character.valueOf(ch), defaultValue));
    }

    @Test
    void testToIntValue_Character_defaultValue_null() {
        assertEquals(99, CharUtils.toIntValue(null, 99));
        assertEquals(-1, CharUtils.toIntValue(null, -1));
    }

    @ParameterizedTest
    @CsvSource({
            "a, 99, 99",
            "A, 99, 99",
            "!, 99, 99",
            " , 99, 99",
            "\\u0000, 99, 99",
            "é, 99, 99"
    })
    void testToIntValue_Character_defaultValue_invalid(char ch, int defaultValue, int expected) {
        assertEquals(expected, CharUtils.toIntValue(Character.valueOf(ch), defaultValue));
    }

    // --- toString(char ch) ---
    // JML: @ensures \result != null && \result.length() == 1 && \result.charAt(0) == ch;
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
    // JML: @ensures ch == null ? \result == null : \result.length() == 1 && \result.charAt(0) == ch.charValue();
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
    // JML: @ensures \result != null && \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_char() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(' '));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\u0000'));
        assertEquals("\\uFFFF", CharUtils.unicodeEscaped('\uFFFF'));
        assertEquals("\\u00E9", CharUtils.unicodeEscaped('é')); // Example of non-ASCII
    }

    // --- unicodeEscaped(Character ch) ---
    // JML: @ensures ch == null ? \result == null : \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_Character_normal() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
        assertEquals("\\u0041", CharUtils.unicodeEscaped(Character.valueOf('A')));
        assertEquals("\\u0030", CharUtils.unicodeEscaped(Character.valueOf('0')));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(Character.valueOf(' ')));
        assertEquals("\\u0000", CharUtils.unicodeEscaped(Character.valueOf('\u0000')));
        assertEquals("\\uFFFF", CharUtils.unicodeEscaped(Character.valueOf('\uFFFF')));
        assertEquals("\\u00E9", CharUtils.unicodeEscaped(Character.valueOf('é')));
    }

    @Test
    void testUnicodeEscaped_Character_null() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}