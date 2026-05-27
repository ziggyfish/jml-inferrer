package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3CP3C {

    // --- compare(final char x, final char y) ---
    // @ensures \result == (x - y);
    @Test
    void testCompare_EqualChars() {
        assertEquals(0, CharUtils.compare('a', 'a'));
        assertEquals(0, CharUtils.compare('Z', 'Z'));
        assertEquals(0, CharUtils.compare('5', '5'));
        assertEquals(0, CharUtils.compare('\0', '\0'));
        assertEquals(0, CharUtils.compare('\uFFFF', '\uFFFF'));
    }

    @Test
    void testCompare_XGreaterThanY() {
        assertTrue(CharUtils.compare('b', 'a') > 0);
        assertTrue(CharUtils.compare('Z', 'A') > 0);
        assertTrue(CharUtils.compare('9', '0') > 0);
        assertTrue(CharUtils.compare('\u0001', '\0') > 0);
        assertTrue(CharUtils.compare('\uFFFF', '\uFFFE') > 0);
    }

    @Test
    void testCompare_XLessThanY() {
        assertTrue(CharUtils.compare('a', 'b') < 0);
        assertTrue(CharUtils.compare('A', 'Z') < 0);
        assertTrue(CharUtils.compare('0', '9') < 0);
        assertTrue(CharUtils.compare('\0', '\u0001') < 0);
        assertTrue(CharUtils.compare('\uFFFE', '\uFFFF') < 0);
    }

    @Test
    void testCompare_BoundaryChars() {
        assertEquals(1, CharUtils.compare('\u0001', '\u0000'));
        assertEquals(-1, CharUtils.compare('\u0000', '\u0001'));
        assertEquals(1, CharUtils.compare('\uFFFF', '\uFFFE'));
        assertEquals(-1, CharUtils.compare('\uFFFE', '\uFFFF'));
    }

    // --- isAscii(final char ch) ---
    // @ensures \result == (ch < 128);
    @ParameterizedTest
    @ValueSource(chars = {'a', 'Z', '0', ' ', '\n', '\t', '\0', '\u007F'})
    void testIsAscii_True(char ch) {
        assertTrue(CharUtils.isAscii(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'\u0080', 'é', 'ñ', '€', '\uFFFF'})
    void testIsAscii_False(char ch) {
        assertFalse(CharUtils.isAscii(ch));
    }

    @Test
    void testIsAscii_BoundaryValues() {
        assertTrue(CharUtils.isAscii('\u007F')); // DEL
        assertFalse(CharUtils.isAscii('\u0080')); // First non-ASCII
        assertTrue(CharUtils.isAscii('\0')); // NUL
    }

    // --- isAsciiAlpha(final char ch) ---
    // @ensures \result == (isAsciiAlphaLower(ch) || isAsciiAlphaUpper(ch));
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z'})
    void testIsAsciiAlpha_True(char ch) {
        assertTrue(CharUtils.isAsciiAlpha(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'0', '9', ' ', '\n', '\t', '!', '@', '[', '{', '\u007F', '\u0080'})
    void testIsAsciiAlpha_False(char ch) {
        assertFalse(CharUtils.isAsciiAlpha(ch));
    }

    @Test
    void testIsAsciiAlpha_BoundaryValues() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
        assertFalse(CharUtils.isAsciiAlpha('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlpha('{')); // After 'z'
        assertFalse(CharUtils.isAsciiAlpha('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlpha('[')); // After 'Z'
    }

    // --- isAsciiAlphaLower(final char ch) ---
    // @ensures \result == (ch >= 'a' && ch <= 'z');
    @ParameterizedTest
    @ValueSource(chars = {'a', 'm', 'z'})
    void testIsAsciiAlphaLower_True(char ch) {
        assertTrue(CharUtils.isAsciiAlphaLower(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'A', 'Z', '0', '9', ' ', '\n', '\t', '!', '@', '`', '{', '\u007F', '\u0080'})
    void testIsAsciiAlphaLower_False(char ch) {
        assertFalse(CharUtils.isAsciiAlphaLower(ch));
    }

    @Test
    void testIsAsciiAlphaLower_BoundaryValues() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
        assertFalse(CharUtils.isAsciiAlphaLower('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlphaLower('{')); // After 'z'
    }

    // --- isAsciiAlphanumeric(final char ch) ---
    // @ensures \result == (isAsciiAlpha(ch) || isAsciiNumeric(ch));
    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', 'A', 'Z', '0', '9'})
    void testIsAsciiAlphanumeric_True(char ch) {
        assertTrue(CharUtils.isAsciiAlphanumeric(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {' ', '\n', '\t', '!', '@', '[', '{', '/', ':', '\u007F', '\u0080'})
    void testIsAsciiAlphanumeric_False(char ch) {
        assertFalse(CharUtils.isAsciiAlphanumeric(ch));
    }

    @Test
    void testIsAsciiAlphanumeric_BoundaryValues() {
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

    // --- isAsciiAlphaUpper(final char ch) ---
    // @ensures \result == (ch >= 'A' && ch <= 'Z');
    @ParameterizedTest
    @ValueSource(chars = {'A', 'M', 'Z'})
    void testIsAsciiAlphaUpper_True(char ch) {
        assertTrue(CharUtils.isAsciiAlphaUpper(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'z', '0', '9', ' ', '\n', '\t', '!', '@', '[', '{', '\u007F', '\u0080'})
    void testIsAsciiAlphaUpper_False(char ch) {
        assertFalse(CharUtils.isAsciiAlphaUpper(ch));
    }

    @Test
    void testIsAsciiAlphaUpper_BoundaryValues() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlphaUpper('[')); // After 'Z'
    }

    // --- isAsciiControl(final char ch) ---
    // @ensures \result == (ch < 32 || ch == 127);
    @ParameterizedTest
    @ValueSource(chars = {'\0', '\u0001', '\u001F', '\u007F'}) // NUL, SOH, US, DEL
    void testIsAsciiControl_True(char ch) {
        assertTrue(CharUtils.isAsciiControl(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {' ', 'a', 'Z', '0', '!', '\u0020', '\u007E', '\u0080'}) // SPACE, 'a', '~', non-ASCII
    void testIsAsciiControl_False(char ch) {
        assertFalse(CharUtils.isAsciiControl(ch));
    }

    @Test
    void testIsAsciiControl_BoundaryValues() {
        assertTrue(CharUtils.isAsciiControl('\0')); // NUL
        assertTrue(CharUtils.isAsciiControl('\u001F')); // US (Unit Separator)
        assertFalse(CharUtils.isAsciiControl(' ')); // Space (0x20)
        assertTrue(CharUtils.isAsciiControl('\u007F')); // DEL
        assertFalse(CharUtils.isAsciiControl('\u007E')); // Tilde
    }

    // --- isAsciiNumeric(final char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '9');
    @ParameterizedTest
    @ValueSource(chars = {'0', '5', '9'})
    void testIsAsciiNumeric_True(char ch) {
        assertTrue(CharUtils.isAsciiNumeric(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'a', 'Z', ' ', '\n', '\t', '!', '@', '/', ':', '\u007F', '\u0080'})
    void testIsAsciiNumeric_False(char ch) {
        assertFalse(CharUtils.isAsciiNumeric(ch));
    }

    @Test
    void testIsAsciiNumeric_BoundaryValues() {
        assertTrue(CharUtils.isAsciiNumeric('0'));
        assertTrue(CharUtils.isAsciiNumeric('9'));
        assertFalse(CharUtils.isAsciiNumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiNumeric(':')); // After '9'
    }

    // --- isAsciiPrintable(final char ch) ---
    // @ensures \result == (ch >= 32 && ch < 127);
    @ParameterizedTest
    @ValueSource(chars = {' ', 'a', 'Z', '0', '!', '~'})
    void testIsAsciiPrintable_True(char ch) {
        assertTrue(CharUtils.isAsciiPrintable(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'\0', '\n', '\t', '\u001F', '\u007F', '\u0080'}) // NUL, LF, TAB, US, DEL, non-ASCII
    void testIsAsciiPrintable_False(char ch) {
        assertFalse(CharUtils.isAsciiPrintable(ch));
    }

    @Test
    void testIsAsciiPrintable_BoundaryValues() {
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space (0x20)
        assertTrue(CharUtils.isAsciiPrintable('~')); // Tilde (0x7E)
        assertFalse(CharUtils.isAsciiPrintable('\u001F')); // US (0x1F)
        assertFalse(CharUtils.isAsciiPrintable('\u007F')); // DEL (0x7F)
    }

    // --- isHex(final char ch) ---
    // @ensures \result == (isAsciiNumeric(ch) || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    @ParameterizedTest
    @ValueSource(chars = {'0', '9', 'a', 'f', 'A', 'F'})
    void testIsHex_True(char ch) {
        assertTrue(CharUtils.isHex(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'g', 'G', 'z', 'Z', ' ', '\n', '\t', '!', '@', '/', ':', '[', '{', '\u007F', '\u0080'})
    void testIsHex_False(char ch) {
        assertFalse(CharUtils.isHex(ch));
    }

    @Test
    void testIsHex_BoundaryValues() {
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

    // --- isOctal(final char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '7');
    @ParameterizedTest
    @ValueSource(chars = {'0', '3', '7'})
    void testIsOctal_True(char ch) {
        assertTrue(CharUtils.isOctal(ch));
    }

    @ParameterizedTest
    @ValueSource(chars = {'8', '9', 'a', 'A', ' ', '\n', '\t', '!', '@', '/', ':', '\u007F', '\u0080'})
    void testIsOctal_False(char ch) {
        assertFalse(CharUtils.isOctal(ch));
    }

    @Test
    void testIsOctal_BoundaryValues() {
        assertTrue(CharUtils.isOctal('0'));
        assertTrue(CharUtils.isOctal('7'));
        assertFalse(CharUtils.isOctal('/')); // Before '0'
        assertFalse(CharUtils.isOctal('8')); // After '7'
    }

    // --- toChar(final Character ch) ---
    // @requires ch != null;
    // @ensures \result == ch.charValue();
    @Test
    void testToChar_Character_Normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('5', CharUtils.toChar(Character.valueOf('5')));
        assertEquals('\0', CharUtils.toChar(Character.valueOf('\0')));
        assertEquals('\uFFFF', CharUtils.toChar(Character.valueOf('\uFFFF')));
    }

    @Test
    void testToChar_Character_NullInput() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(final Character ch, final char defaultValue) ---
    // @ensures ch == null ? \result == defaultValue : \result == ch.charValue();
    @Test
    void testToChar_CharacterWithDefault_Normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'y'));
    }

    @Test
    void testToChar_CharacterWithDefault_NullInput() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\0', CharUtils.toChar(null, '\0'));
    }

    // --- toChar(final String str) ---
    // @requires str != null && str.length() == 1;
    // @ensures \result == str.charAt(0);
    @Test
    void testToChar_String_Normal() {
        assertEquals('a', CharUtils.toChar("a"));
        assertEquals('Z', CharUtils.toChar("Z"));
        assertEquals('5', CharUtils.toChar("5"));
        assertEquals('\0', CharUtils.toChar("\0"));
        assertEquals('\uFFFF', CharUtils.toChar("\uFFFF"));
    }

    @Test
    void testToChar_String_NullInput() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar(null));
    }

    @Test
    void testToChar_String_EmptyInput() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""));
    }

    @Test
    void testToChar_String_MultiCharInput() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("ab"));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("abc"));
    }

    // --- toChar(final String str, final char defaultValue) ---
    // @ensures str == null || str.length() != 1 ? \result == defaultValue : \result == str.charAt(0);
    @Test
    void testToChar_StringWithDefault_Normal() {
        assertEquals('a', CharUtils.toChar("a", 'x'));
        assertEquals('Z', CharUtils.toChar("Z", 'y'));
    }

    @Test
    void testToChar_StringWithDefault_NullInput() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\0', CharUtils.toChar(null, '\0'));
    }

    @Test
    void testToChar_StringWithDefault_EmptyInput() {
        assertEquals('x', CharUtils.toChar("", 'x'));
        assertEquals('\0', CharUtils.toChar("", '\0'));
    }

    @Test
    void testToChar_StringWithDefault_MultiCharInput() {
        assertEquals('x', CharUtils.toChar("ab", 'x'));
        assertEquals('\0', CharUtils.toChar("abc", '\0'));
    }

    // --- toCharacterObject(final char c) ---
    // @ensures \result != null && \result.charValue() == c;
    @Test
    void testToCharacterObject_Char_Normal() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject('5'));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject('\0'));
        assertEquals(Character.valueOf('\uFFFF'), CharUtils.toCharacterObject('\uFFFF'));
    }

    // --- toCharacterObject(final String str) ---
    // @ensures str == null || str.length() != 1 ? \result == null : \result.charValue() == str.charAt(0);
    @Test
    void testToCharacterObject_String_Normal() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("a"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Z"));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject("5"));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject("\0"));
        assertEquals(Character.valueOf('\uFFFF'), CharUtils.toCharacterObject("\uFFFF"));
    }

    @Test
    void testToCharacterObject_String_NullInput() {
        assertNull(CharUtils.toCharacterObject(null));
    }

    @Test
    void testToCharacterObject_String_EmptyInput() {
        assertNull(CharUtils.toCharacterObject(""));
    }

    @Test
    void testToCharacterObject_String_MultiCharInput() {
        assertNull(CharUtils.toCharacterObject("ab"));
        assertNull(CharUtils.toCharacterObject("abc"));
    }

    // --- toIntValue(final char ch) ---
    // @requires ch >= '0' && ch <= '9';
    // @ensures \result == Character.getNumericValue(ch);
    @Test
    void testToIntValue_Char_Normal() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(5, CharUtils.toIntValue('5'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_Char_InvalidInput() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('/')); // Before '0'
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(':')); // After '9'
    }

    // --- toIntValue(final char ch, final int defaultValue) ---
    // @ensures (ch >= '0' && ch <= '9') ? \result == Character.getNumericValue(ch) : \result == defaultValue;
    @Test
    void testToIntValue_CharWithDefault_Normal() {
        assertEquals(0, CharUtils.toIntValue('0', -1));
        assertEquals(5, CharUtils.toIntValue('5', -1));
        assertEquals(9, CharUtils.toIntValue('9', -1));
    }

    @Test
    void testToIntValue_CharWithDefault_InvalidInput() {
        assertEquals(-1, CharUtils.toIntValue('a', -1));
        assertEquals(99, CharUtils.toIntValue(' ', 99));
        assertEquals(0, CharUtils.toIntValue('/', 0));
        assertEquals(10, CharUtils.toIntValue(':', 10));
    }

    // --- toIntValue(final Character ch) ---
    // @requires ch != null && ch.charValue() >= '0' && ch.charValue() <= '9';
    // @ensures \result == Character.getNumericValue(ch.charValue());
    @Test
    void testToIntValue_Character_Normal() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5')));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9')));
    }

    @Test
    void testToIntValue_Character_NullInput() {
        assertThrows(NullPointerException.class, () -> CharUtils.toIntValue(null));
    }

    @Test
    void testToIntValue_Character_InvalidInput() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(' ')));
    }

    // --- toIntValue(final Character ch, final int defaultValue) ---
    // @ensures ch == null || !(ch.charValue() >= '0' && ch.charValue() <= '9') ? \result == defaultValue : \result == Character.getNumericValue(ch.charValue());
    @Test
    void testToIntValue_CharacterWithDefault_Normal() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0'), -1));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5'), -1));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9'), -1));
    }

    @Test
    void testToIntValue_CharacterWithDefault_NullInput() {
        assertEquals(-1, CharUtils.toIntValue(null, -1));
        assertEquals(0, CharUtils.toIntValue(null, 0));
    }

    @Test
    void testToIntValue_CharacterWithDefault_InvalidInput() {
        assertEquals(-1, CharUtils.toIntValue(Character.valueOf('a'), -1));
        assertEquals(99, CharUtils.toIntValue(Character.valueOf(' '), 99));
    }

    // --- toString(final char ch) ---
    // @ensures \result != null && \result.length() == 1 && \result.charAt(0) == ch;
    @Test
    void testToString_Char_Normal() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("5", CharUtils.toString('5'));
        assertEquals("\0", CharUtils.toString('\0'));
        assertEquals("\uFFFF", CharUtils.toString('\uFFFF'));
    }

    // --- toString(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.length() == 1 && \result.charAt(0) == ch.charValue();
    @Test
    void testToString_Character_Normal() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("5", CharUtils.toString(Character.valueOf('5')));
        assertEquals("\0", CharUtils.toString(Character.valueOf('\0')));
        assertEquals("\uFFFF", CharUtils.toString(Character.valueOf('\uFFFF')));
    }

    @Test
    void testToString_Character_NullInput() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(final char ch) ---
    // @ensures \result != null && \result.startsWith("\\u") && \result.length() == 6;
    @ParameterizedTest
    @CsvSource({
            "a, \\u0061",
            "Z, \\u005A",
            "0, \\u0030",
            " , \\u0020",
            "\\, \\u005C", // Backslash itself
            "\0, \\u0000", // NUL
            "\uFFFF, \\uFFFF" // Max Unicode char
    })
    void testUnicodeEscaped_Char_Normal(char ch, String expected) {
        assertEquals(expected, CharUtils.unicodeEscaped(ch));
    }

    // --- unicodeEscaped(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.startsWith("\\u") && \result.length() == 6;
    @ParameterizedTest
    @CsvSource({
            "a, \\u0061",
            "Z, \\u005A",
            "0, \\u0030",
            " , \\u0020",
            "\\, \\u005C",
            "\0, \\u0000",
            "\uFFFF, \\uFFFF"
    })
    void testUnicodeEscaped_Character_Normal(char ch, String expected) {
        assertEquals(expected, CharUtils.unicodeEscaped(Character.valueOf(ch)));
    }

    @Test
    void testUnicodeEscaped_Character_NullInput() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}