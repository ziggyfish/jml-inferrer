package org.apache.commons.lang3.p3;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3P3 {

    // --- compare(final char x, final char y) ---
    // @ensures \result == (x - y);
    @Test
    void testCompare_EqualChars() {
        assertEquals(0, CharUtils.compare('a', 'a'));
        assertEquals(0, CharUtils.compare('Z', 'Z'));
        assertEquals(0, CharUtils.compare('5', '5'));
        assertEquals(0, CharUtils.compare('\0', '\0'));
        assertEquals(0, CharUtils.compare(' ', ' '));
    }

    @Test
    void testCompare_XGreaterThanY() {
        assertTrue(CharUtils.compare('b', 'a') > 0);
        assertTrue(CharUtils.compare('Z', 'A') > 0);
        assertTrue(CharUtils.compare('9', '0') > 0);
        assertTrue(CharUtils.compare('~', ' ') > 0);
        assertTrue(CharUtils.compare('a', '\0') > 0);
    }

    @Test
    void testCompare_XLessThanY() {
        assertTrue(CharUtils.compare('a', 'b') < 0);
        assertTrue(CharUtils.compare('A', 'Z') < 0);
        assertTrue(CharUtils.compare('0', '9') < 0);
        assertTrue(CharUtils.compare(' ', '~') < 0);
        assertTrue(CharUtils.compare('\0', 'a') < 0);
    }

    @Test
    void testCompare_EdgeCases_MinMaxChar() {
        assertEquals(0, CharUtils.compare(Character.MIN_VALUE, Character.MIN_VALUE));
        assertEquals(0, CharUtils.compare(Character.MAX_VALUE, Character.MAX_VALUE));
        assertTrue(CharUtils.compare(Character.MAX_VALUE, Character.MIN_VALUE) > 0);
        assertTrue(CharUtils.compare(Character.MIN_VALUE, Character.MAX_VALUE) < 0);
    }

    // --- isAscii(final char ch) ---
    // @ensures \result == (ch >= 0 && ch <= 127);
    @Test
    void testIsAscii_AsciiChars() {
        assertTrue(CharUtils.isAscii('a'));
        assertTrue(CharUtils.isAscii('Z'));
        assertTrue(CharUtils.isAscii('0'));
        assertTrue(CharUtils.isAscii(' '));
        assertTrue(CharUtils.isAscii('\n')); // Newline is ASCII
        assertTrue(CharUtils.isAscii('\0')); // Null char is ASCII
        assertTrue(CharUtils.isAscii((char) 127)); // DEL is ASCII
    }

    @Test
    void testIsAscii_NonAsciiChars() {
        assertFalse(CharUtils.isAscii('é')); // Latin-1
        assertFalse(CharUtils.isAscii('€')); // Euro symbol
        assertFalse(CharUtils.isAscii('你')); // Chinese character
        assertFalse(CharUtils.isAscii((char) 128)); // First non-ASCII char
        assertFalse(CharUtils.isAscii(Character.MAX_VALUE));
    }

    @Test
    void testIsAscii_EdgeCases() {
        assertTrue(CharUtils.isAscii((char) 0));
        assertTrue(CharUtils.isAscii((char) 127));
        assertFalse(CharUtils.isAscii((char) 128));
    }

    // --- isAsciiAlpha(final char ch) ---
    // @ensures \result == ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z'));
    @Test
    void testIsAsciiAlpha_AlphaChars() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
        assertTrue(CharUtils.isAsciiAlpha('m'));
        assertTrue(CharUtils.isAsciiAlpha('M'));
    }

    @Test
    void testIsAsciiAlpha_NonAlphaChars() {
        assertFalse(CharUtils.isAsciiAlpha('0'));
        assertFalse(CharUtils.isAsciiAlpha('9'));
        assertFalse(CharUtils.isAsciiAlpha(' '));
        assertFalse(CharUtils.isAsciiAlpha('$'));
        assertFalse(CharUtils.isAsciiAlpha('\n'));
        assertFalse(CharUtils.isAsciiAlpha('é')); // Non-ASCII alpha
        assertFalse(CharUtils.isAsciiAlpha('\0'));
        assertFalse(CharUtils.isAsciiAlpha((char) 127));
    }

    @Test
    void testIsAsciiAlpha_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlpha('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlpha('[')); // After 'Z'
        assertFalse(CharUtils.isAsciiAlpha('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlpha('{')); // After 'z'
    }

    // --- isAsciiAlphaLower(final char ch) ---
    // @ensures \result == (ch >= 'a' && ch <= 'z');
    @Test
    void testIsAsciiAlphaLower_LowerAlphaChars() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
        assertTrue(CharUtils.isAsciiAlphaLower('m'));
    }

    @Test
    void testIsAsciiAlphaLower_NonLowerAlphaChars() {
        assertFalse(CharUtils.isAsciiAlphaLower('A'));
        assertFalse(CharUtils.isAsciiAlphaLower('Z'));
        assertFalse(CharUtils.isAsciiAlphaLower('0'));
        assertFalse(CharUtils.isAsciiAlphaLower(' '));
        assertFalse(CharUtils.isAsciiAlphaLower('$'));
        assertFalse(CharUtils.isAsciiAlphaLower('é')); // Non-ASCII
    }

    @Test
    void testIsAsciiAlphaLower_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlphaLower('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlphaLower('{')); // After 'z'
    }

    // --- isAsciiAlphanumeric(final char ch) ---
    // @ensures \result == ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9'));
    @Test
    void testIsAsciiAlphanumeric_AlphanumericChars() {
        assertTrue(CharUtils.isAsciiAlphanumeric('a'));
        assertTrue(CharUtils.isAsciiAlphanumeric('Z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('0'));
        assertTrue(CharUtils.isAsciiAlphanumeric('9'));
        assertTrue(CharUtils.isAsciiAlphanumeric('k'));
        assertTrue(CharUtils.isAsciiAlphanumeric('K'));
        assertTrue(CharUtils.isAsciiAlphanumeric('5'));
    }

    @Test
    void testIsAsciiAlphanumeric_NonAlphanumericChars() {
        assertFalse(CharUtils.isAsciiAlphanumeric(' '));
        assertFalse(CharUtils.isAsciiAlphanumeric('$'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\n'));
        assertFalse(CharUtils.isAsciiAlphanumeric('é'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\0'));
    }

    @Test
    void testIsAsciiAlphanumeric_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlphanumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiAlphanumeric(':')); // After '9'
        assertFalse(CharUtils.isAsciiAlphanumeric('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlphanumeric('[')); // After 'Z'
        assertFalse(CharUtils.isAsciiAlphanumeric('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlphanumeric('{')); // After 'z'
    }

    // --- isAsciiAlphaUpper(final char ch) ---
    // @ensures \result == (ch >= 'A' && ch <= 'Z');
    @Test
    void testIsAsciiAlphaUpper_UpperAlphaChars() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
        assertTrue(CharUtils.isAsciiAlphaUpper('M'));
    }

    @Test
    void testIsAsciiAlphaUpper_NonUpperAlphaChars() {
        assertFalse(CharUtils.isAsciiAlphaUpper('a'));
        assertFalse(CharUtils.isAsciiAlphaUpper('z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('0'));
        assertFalse(CharUtils.isAsciiAlphaUpper(' '));
        assertFalse(CharUtils.isAsciiAlphaUpper('$'));
        assertFalse(CharUtils.isAsciiAlphaUpper('É')); // Non-ASCII
    }

    @Test
    void testIsAsciiAlphaUpper_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlphaUpper('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlphaUpper('[')); // After 'Z'
    }

    // --- isAsciiControl(final char ch) ---
    // @ensures \result == ((ch >= 0 && ch <= 31) || ch == 127);
    @Test
    void testIsAsciiControl_ControlChars() {
        assertTrue(CharUtils.isAsciiControl('\0')); // NUL
        assertTrue(CharUtils.isAsciiControl('\t')); // HT
        assertTrue(CharUtils.isAsciiControl('\n')); // LF
        assertTrue(CharUtils.isAsciiControl('\r')); // CR
        assertTrue(CharUtils.isAsciiControl((char) 31)); // US
        assertTrue(CharUtils.isAsciiControl((char) 127)); // DEL
    }

    @Test
    void testIsAsciiControl_NonControlChars() {
        assertFalse(CharUtils.isAsciiControl(' ')); // Space
        assertFalse(CharUtils.isAsciiControl('A'));
        assertFalse(CharUtils.isAsciiControl('0'));
        assertFalse(CharUtils.isAsciiControl('~')); // Tilde
        assertFalse(CharUtils.isAsciiControl((char) 32)); // Space
        assertFalse(CharUtils.isAsciiControl((char) 126)); // Tilde
        assertFalse(CharUtils.isAsciiControl('é')); // Non-ASCII
    }

    @Test
    void testIsAsciiControl_EdgeCases() {
        assertTrue(CharUtils.isAsciiControl((char) 0));
        assertTrue(CharUtils.isAsciiControl((char) 31));
        assertFalse(CharUtils.isAsciiControl((char) 32));
        assertTrue(CharUtils.isAsciiControl((char) 127));
        assertFalse(CharUtils.isAsciiControl((char) 128));
    }

    // --- isAsciiNumeric(final char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '9');
    @Test
    void testIsAsciiNumeric_NumericChars() {
        assertTrue(CharUtils.isAsciiNumeric('0'));
        assertTrue(CharUtils.isAsciiNumeric('9'));
        assertTrue(CharUtils.isAsciiNumeric('5'));
    }

    @Test
    void testIsAsciiNumeric_NonNumericChars() {
        assertFalse(CharUtils.isAsciiNumeric('a'));
        assertFalse(CharUtils.isAsciiNumeric('Z'));
        assertFalse(CharUtils.isAsciiNumeric(' '));
        assertFalse(CharUtils.isAsciiNumeric('$'));
        assertFalse(CharUtils.isAsciiNumeric('½')); // Non-ASCII
    }

    @Test
    void testIsAsciiNumeric_EdgeCases() {
        assertFalse(CharUtils.isAsciiNumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiNumeric(':')); // After '9'
    }

    // --- isAsciiPrintable(final char ch) ---
    // @ensures \result == (ch >= 32 && ch <= 126);
    @Test
    void testIsAsciiPrintable_PrintableChars() {
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space
        assertTrue(CharUtils.isAsciiPrintable('A'));
        assertTrue(CharUtils.isAsciiPrintable('z'));
        assertTrue(CharUtils.isAsciiPrintable('0'));
        assertTrue(CharUtils.isAsciiPrintable('~')); // Tilde
        assertTrue(CharUtils.isAsciiPrintable((char) 32));
        assertTrue(CharUtils.isAsciiPrintable((char) 126));
    }

    @Test
    void testIsAsciiPrintable_NonPrintableChars() {
        assertFalse(CharUtils.isAsciiPrintable('\0')); // NUL
        assertFalse(CharUtils.isAsciiPrintable('\n')); // LF
        assertFalse(CharUtils.isAsciiPrintable((char) 31)); // US
        assertFalse(CharUtils.isAsciiPrintable((char) 127)); // DEL
        assertFalse(CharUtils.isAsciiPrintable('é')); // Non-ASCII
        assertFalse(CharUtils.isAsciiPrintable(Character.MAX_VALUE));
    }

    @Test
    void testIsAsciiPrintable_EdgeCases() {
        assertFalse(CharUtils.isAsciiPrintable((char) 31));
        assertTrue(CharUtils.isAsciiPrintable((char) 32));
        assertTrue(CharUtils.isAsciiPrintable((char) 126));
        assertFalse(CharUtils.isAsciiPrintable((char) 127));
    }

    // --- isHex(final char ch) ---
    // @ensures \result == ((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    @Test
    void testIsHex_HexChars() {
        assertTrue(CharUtils.isHex('0'));
        assertTrue(CharUtils.isHex('9'));
        assertTrue(CharUtils.isHex('a'));
        assertTrue(CharUtils.isHex('f'));
        assertTrue(CharUtils.isHex('A'));
        assertTrue(CharUtils.isHex('F'));
        assertTrue(CharUtils.isHex('5'));
        assertTrue(CharUtils.isHex('c'));
        assertTrue(CharUtils.isHex('E'));
    }

    @Test
    void testIsHex_NonHexChars() {
        assertFalse(CharUtils.isHex('g'));
        assertFalse(CharUtils.isHex('G'));
        assertFalse(CharUtils.isHex(' '));
        assertFalse(CharUtils.isHex('$'));
        assertFalse(CharUtils.isHex('\0'));
        assertFalse(CharUtils.isHex('é'));
    }

    @Test
    void testIsHex_EdgeCases() {
        assertFalse(CharUtils.isHex('/')); // Before '0'
        assertFalse(CharUtils.isHex(':')); // After '9'
        assertFalse(CharUtils.isHex('@')); // Before 'A'
        assertFalse(CharUtils.isHex('G')); // After 'F'
        assertFalse(CharUtils.isHex('`')); // Before 'a'
        assertFalse(CharUtils.isHex('g')); // After 'f'
    }

    // --- isOctal(final char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '7');
    @Test
    void testIsOctal_OctalChars() {
        assertTrue(CharUtils.isOctal('0'));
        assertTrue(CharUtils.isOctal('7'));
        assertTrue(CharUtils.isOctal('3'));
    }

    @Test
    void testIsOctal_NonOctalChars() {
        assertFalse(CharUtils.isOctal('8'));
        assertFalse(CharUtils.isOctal('9'));
        assertFalse(CharUtils.isOctal('a'));
        assertFalse(CharUtils.isOctal('A'));
        assertFalse(CharUtils.isOctal(' '));
        assertFalse(CharUtils.isOctal('$'));
        assertFalse(CharUtils.isOctal('\0'));
        assertFalse(CharUtils.isOctal('é'));
    }

    @Test
    void testIsOctal_EdgeCases() {
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
        assertEquals('\n', CharUtils.toChar(Character.valueOf('\n')));
    }

    @Test
    void testToChar_Character_NullThrowsNPE() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar((Character) null));
    }

    // --- toChar(final Character ch, final char defaultValue) ---
    // @ensures ch == null ? \result == defaultValue : \result == ch.charValue();
    @Test
    void testToChar_CharacterWithDefault_Normal() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'x'));
        assertEquals('5', CharUtils.toChar(Character.valueOf('5'), 'x'));
    }

    @Test
    void testToChar_CharacterWithDefault_Null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
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
        assertEquals('\n', CharUtils.toChar("\n"));
    }

    @Test
    void testToChar_String_NullThrowsNPE() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar((String) null));
    }

    @Test
    void testToChar_String_EmptyThrowsIAE() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""));
    }

    @Test
    void testToChar_String_TooLongThrowsIAE() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("ab"));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("abc"));
    }

    // --- toChar(final String str, final char defaultValue) ---
    // @ensures str == null || str.length() != 1 ? \result == defaultValue : \result == str.charAt(0);
    @Test
    void testToChar_StringWithDefault_Normal() {
        assertEquals('a', CharUtils.toChar("a", 'x'));
        assertEquals('Z', CharUtils.toChar("Z", 'x'));
        assertEquals('5', CharUtils.toChar("5", 'x'));
    }

    @Test
    void testToChar_StringWithDefault_Null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    @Test
    void testToChar_StringWithDefault_Empty() {
        assertEquals('x', CharUtils.toChar("", 'x'));
        assertEquals(' ', CharUtils.toChar("", ' '));
    }

    @Test
    void testToChar_StringWithDefault_TooLong() {
        assertEquals('x', CharUtils.toChar("ab", 'x'));
        assertEquals(' ', CharUtils.toChar("abc", ' '));
    }

    // --- toCharacterObject(final char c) ---
    // @ensures \result != null && \result.charValue() == c;
    @Test
    void testToCharacterObject_char_Normal() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject('5'));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject('\0'));
        assertEquals(Character.valueOf(Character.MIN_VALUE), CharUtils.toCharacterObject(Character.MIN_VALUE));
        assertEquals(Character.valueOf(Character.MAX_VALUE), CharUtils.toCharacterObject(Character.MAX_VALUE));
    }

    // --- toCharacterObject(final String str) ---
    // @ensures str == null || str.length() != 1 ? \result == null : \result.charValue() == str.charAt(0);
    @Test
    void testToCharacterObject_String_Normal() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("a"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Z"));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject("5"));
    }

    @Test
    void testToCharacterObject_String_Null() {
        assertNull(CharUtils.toCharacterObject(null));
    }

    @Test
    void testToCharacterObject_String_Empty() {
        assertNull(CharUtils.toCharacterObject(""));
    }

    @Test
    void testToCharacterObject_String_TooLong() {
        assertNull(CharUtils.toCharacterObject("ab"));
        assertNull(CharUtils.toCharacterObject("abc"));
    }

    // --- toIntValue(final char ch) ---
    // @requires ch >= '0' && ch <= '9';
    // @ensures \result == (ch - '0');
    @Test
    void testToIntValue_char_Normal() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(1, CharUtils.toIntValue('1'));
        assertEquals(5, CharUtils.toIntValue('5'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_char_InvalidCharThrowsIAE() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('/'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(':'));
    }

    // --- toIntValue(final char ch, final int defaultValue) ---
    // @ensures (ch >= '0' && ch <= '9') ? \result == (ch - '0') : \result == defaultValue;
    @Test
    void testToIntValue_charWithDefault_Normal() {
        assertEquals(0, CharUtils.toIntValue('0', -1));
        assertEquals(5, CharUtils.toIntValue('5', -1));
        assertEquals(9, CharUtils.toIntValue('9', -1));
    }

    @Test
    void testToIntValue_charWithDefault_InvalidChar() {
        assertEquals(-1, CharUtils.toIntValue('a', -1));
        assertEquals(100, CharUtils.toIntValue(' ', 100));
        assertEquals(0, CharUtils.toIntValue('/', 0));
        assertEquals(0, CharUtils.toIntValue(':', 0));
    }

    // --- toIntValue(final Character ch) ---
    // @requires ch != null && ch.charValue() >= '0' && ch.charValue() <= '9';
    // @ensures \result == (ch.charValue() - '0');
    @Test
    void testToIntValue_Character_Normal() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5')));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9')));
    }

    @Test
    void testToIntValue_Character_NullThrowsNPE() {
        assertThrows(NullPointerException.class, () -> CharUtils.toIntValue((Character) null));
    }

    @Test
    void testToIntValue_Character_InvalidCharThrowsIAE() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(' ')));
    }

    // --- toIntValue(final Character ch, final int defaultValue) ---
    // @ensures ch == null || !(ch.charValue() >= '0' && ch.charValue() <= '9') ? \result == defaultValue : \result == (ch.charValue() - '0');
    @Test
    void testToIntValue_CharacterWithDefault_Normal() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0'), -1));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5'), -1));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9'), -1));
    }

    @Test
    void testToIntValue_CharacterWithDefault_Null() {
        assertEquals(-1, CharUtils.toIntValue(null, -1));
        assertEquals(0, CharUtils.toIntValue(null, 0));
    }

    @Test
    void testToIntValue_CharacterWithDefault_InvalidChar() {
        assertEquals(-1, CharUtils.toIntValue(Character.valueOf('a'), -1));
        assertEquals(100, CharUtils.toIntValue(Character.valueOf(' '), 100));
    }

    // --- toString(final char ch) ---
    // @ensures \result != null && \result.length() == 1 && \result.charAt(0) == ch;
    @Test
    void testToString_char_Normal() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("5", CharUtils.toString('5'));
        assertEquals("\n", CharUtils.toString('\n'));
        assertEquals("\0", CharUtils.toString('\0'));
    }

    // --- toString(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.length() == 1 && \result.charAt(0) == ch.charValue();
    @Test
    void testToString_Character_Normal() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("5", CharUtils.toString(Character.valueOf('5')));
    }

    @Test
    void testToString_Character_Null() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(final char ch) ---
    // @ensures \result != null && \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_char_Normal() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\0'));
        assertEquals("\\u000a", CharUtils.unicodeEscaped('\n'));
        assertEquals("\\uffff", CharUtils.unicodeEscaped(Character.MAX_VALUE));
    }

    // --- unicodeEscaped(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_Character_Normal() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
        assertEquals("\\u0041", CharUtils.unicodeEscaped(Character.valueOf('A')));
        assertEquals("\\u0030", CharUtils.unicodeEscaped(Character.valueOf('0')));
    }

    @Test
    void testUnicodeEscaped_Character_Null() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}