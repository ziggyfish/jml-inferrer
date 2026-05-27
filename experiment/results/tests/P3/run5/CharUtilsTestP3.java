package org.apache.commons.lang3.p3;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class CharUtilsTestP3P3 {

    // --- compare(final char x, final char y) ---
    // @ensures \result == (x - y);
    @Test
    void testCompare_EqualChars() {
        assertEquals(0, CharUtils.compare('a', 'a'));
        assertEquals(0, CharUtils.compare('Z', 'Z'));
        assertEquals(0, CharUtils.compare('5', '5'));
        assertEquals(0, CharUtils.compare('\0', '\0'));
        assertEquals(0, CharUtils.compare('€', '€')); // Non-ASCII
    }

    @Test
    void testCompare_XGreaterThanY() {
        assertTrue(CharUtils.compare('b', 'a') > 0);
        assertTrue(CharUtils.compare('Z', 'A') > 0);
        assertTrue(CharUtils.compare('9', '0') > 0);
        assertTrue(CharUtils.compare('b', '\0') > 0);
        assertTrue(CharUtils.compare('€', 'a') > 0); // Non-ASCII vs ASCII
    }

    @Test
    void testCompare_XLessThanY() {
        assertTrue(CharUtils.compare('a', 'b') < 0);
        assertTrue(CharUtils.compare('A', 'Z') < 0);
        assertTrue(CharUtils.compare('0', '9') < 0);
        assertTrue(CharUtils.compare('\0', 'b') < 0);
        assertTrue(CharUtils.compare('a', '€') < 0); // ASCII vs Non-ASCII
    }

    @Test
    void testCompare_MinMaxChars() {
        assertEquals(0, CharUtils.compare(Character.MIN_VALUE, Character.MIN_VALUE));
        assertEquals(0, CharUtils.compare(Character.MAX_VALUE, Character.MAX_VALUE));
        assertTrue(CharUtils.compare(Character.MAX_VALUE, Character.MIN_VALUE) > 0);
        assertTrue(CharUtils.compare(Character.MIN_VALUE, Character.MAX_VALUE) < 0);
    }

    // --- isAscii(final char ch) ---
    // @ensures \result == (ch < 128);
    @Test
    void testIsAscii_AsciiChars() {
        assertTrue(CharUtils.isAscii('a'));
        assertTrue(CharUtils.isAscii('Z'));
        assertTrue(CharUtils.isAscii('0'));
        assertTrue(CharUtils.isAscii(' '));
        assertTrue(CharUtils.isAscii('\n'));
        assertTrue(CharUtils.isAscii('\0')); // NUL character is ASCII
        assertTrue(CharUtils.isAscii((char) 127)); // DEL character is ASCII
    }

    @Test
    void testIsAscii_NonAsciiChars() {
        assertFalse(CharUtils.isAscii('€')); // Euro sign (U+20AC)
        assertFalse(CharUtils.isAscii('é')); // e acute (U+00E9)
        assertFalse(CharUtils.isAscii('ñ')); // n tilde (U+00F1)
        assertFalse(CharUtils.isAscii('你好')); // Chinese character
        assertFalse(CharUtils.isAscii((char) 128)); // First non-ASCII char
        assertFalse(CharUtils.isAscii(Character.MAX_VALUE));
    }

    // --- isAsciiAlpha(final char ch) ---
    // @ensures \result == (isAsciiAlphaLower(ch) || isAsciiAlphaUpper(ch));
    @Test
    void testIsAsciiAlpha_LowerCases() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('m'));
    }

    @Test
    void testIsAsciiAlpha_UpperCases() {
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
        assertTrue(CharUtils.isAsciiAlpha('M'));
    }

    @Test
    void testIsAsciiAlpha_NonAlphaChars() {
        assertFalse(CharUtils.isAsciiAlpha('0'));
        assertFalse(CharUtils.isAsciiAlpha('9'));
        assertFalse(CharUtils.isAsciiAlpha(' '));
        assertFalse(CharUtils.isAsciiAlpha('$'));
        assertFalse(CharUtils.isAsciiAlpha('\n'));
        assertFalse(CharUtils.isAsciiAlpha('€'));
        assertFalse(CharUtils.isAsciiAlpha('\0'));
        assertFalse(CharUtils.isAsciiAlpha((char) 128));
    }

    // --- isAsciiAlphaLower(final char ch) ---
    // @ensures \result == (ch >= 'a' && ch <= 'z');
    @Test
    void testIsAsciiAlphaLower_LowerCases() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
        assertTrue(CharUtils.isAsciiAlphaLower('m'));
    }

    @Test
    void testIsAsciiAlphaLower_NonLowerCases() {
        assertFalse(CharUtils.isAsciiAlphaLower('A'));
        assertFalse(CharUtils.isAsciiAlphaLower('Z'));
        assertFalse(CharUtils.isAsciiAlphaLower('0'));
        assertFalse(CharUtils.isAsciiAlphaLower('9'));
        assertFalse(CharUtils.isAsciiAlphaLower(' '));
        assertFalse(CharUtils.isAsciiAlphaLower('$'));
        assertFalse(CharUtils.isAsciiAlphaLower('\n'));
        assertFalse(CharUtils.isAsciiAlphaLower('€'));
        assertFalse(CharUtils.isAsciiAlphaLower('\0'));
        assertFalse(CharUtils.isAsciiAlphaLower((char) 128));
    }

    // --- isAsciiAlphanumeric(final char ch) ---
    // @ensures \result == (isAsciiAlpha(ch) || isAsciiNumeric(ch));
    @Test
    void testIsAsciiAlphanumeric_AlphaChars() {
        assertTrue(CharUtils.isAsciiAlphanumeric('a'));
        assertTrue(CharUtils.isAsciiAlphanumeric('Z'));
    }

    @Test
    void testIsAsciiAlphanumeric_NumericChars() {
        assertTrue(CharUtils.isAsciiAlphanumeric('0'));
        assertTrue(CharUtils.isAsciiAlphanumeric('9'));
    }

    @Test
    void testIsAsciiAlphanumeric_NonAlphanumericChars() {
        assertFalse(CharUtils.isAsciiAlphanumeric(' '));
        assertFalse(CharUtils.isAsciiAlphanumeric('$'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\n'));
        assertFalse(CharUtils.isAsciiAlphanumeric('€'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\0'));
        assertFalse(CharUtils.isAsciiAlphanumeric((char) 128));
    }

    // --- isAsciiAlphaUpper(final char ch) ---
    // @ensures \result == (ch >= 'A' && ch <= 'Z');
    @Test
    void testIsAsciiAlphaUpper_UpperCases() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
        assertTrue(CharUtils.isAsciiAlphaUpper('M'));
    }

    @Test
    void testIsAsciiAlphaUpper_NonUpperCases() {
        assertFalse(CharUtils.isAsciiAlphaUpper('a'));
        assertFalse(CharUtils.isAsciiAlphaUpper('z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('0'));
        assertFalse(CharUtils.isAsciiAlphaUpper('9'));
        assertFalse(CharUtils.isAsciiAlphaUpper(' '));
        assertFalse(CharUtils.isAsciiAlphaUpper('$'));
        assertFalse(CharUtils.isAsciiAlphaUpper('\n'));
        assertFalse(CharUtils.isAsciiAlphaUpper('€'));
        assertFalse(CharUtils.isAsciiAlphaUpper('\0'));
        assertFalse(CharUtils.isAsciiAlphaUpper((char) 128));
    }

    // --- isAsciiControl(final char ch) ---
    // @ensures \result == (ch < 32 || ch == 127);
    @Test
    void testIsAsciiControl_ControlChars() {
        assertTrue(CharUtils.isAsciiControl('\0')); // NUL
        assertTrue(CharUtils.isAsciiControl('\u0001')); // SOH
        assertTrue(CharUtils.isAsciiControl('\u001F')); // US
        assertTrue(CharUtils.isAsciiControl((char) 31)); // US
        assertTrue(CharUtils.isAsciiControl((char) 127)); // DEL
    }

    @Test
    void testIsAsciiControl_NonControlChars() {
        assertFalse(CharUtils.isAsciiControl(' ')); // Space (32)
        assertFalse(CharUtils.isAsciiControl('a'));
        assertFalse(CharUtils.isAsciiControl('Z'));
        assertFalse(CharUtils.isAsciiControl('0'));
        assertFalse(CharUtils.isAsciiControl('€'));
        assertFalse(CharUtils.isAsciiControl((char) 32));
        assertFalse(CharUtils.isAsciiControl((char) 126)); // Tilde
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
        assertFalse(CharUtils.isAsciiNumeric('\n'));
        assertFalse(CharUtils.isAsciiNumeric('€'));
        assertFalse(CharUtils.isAsciiNumeric('\0'));
        assertFalse(CharUtils.isAsciiNumeric((char) 128));
    }

    // --- isAsciiPrintable(final char ch) ---
    // @ensures \result == (ch >= 32 && ch < 127);
    @Test
    void testIsAsciiPrintable_PrintableChars() {
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space
        assertTrue(CharUtils.isAsciiPrintable('a'));
        assertTrue(CharUtils.isAsciiPrintable('Z'));
        assertTrue(CharUtils.isAsciiPrintable('0'));
        assertTrue(CharUtils.isAsciiPrintable('$'));
        assertTrue(CharUtils.isAsciiPrintable('~')); // Tilde (126)
        assertTrue(CharUtils.isAsciiPrintable((char) 32));
        assertTrue(CharUtils.isAsciiPrintable((char) 126));
    }

    @Test
    void testIsAsciiPrintable_NonPrintableChars() {
        assertFalse(CharUtils.isAsciiPrintable('\0')); // NUL (0)
        assertFalse(CharUtils.isAsciiPrintable('\n')); // Newline (10)
        assertFalse(CharUtils.isAsciiPrintable((char) 31)); // US
        assertFalse(CharUtils.isAsciiPrintable((char) 127)); // DEL
        assertFalse(CharUtils.isAsciiPrintable('€'));
        assertFalse(CharUtils.isAsciiPrintable((char) 128));
    }

    // --- isHex(final char ch) ---
    // @ensures \result == (isAsciiNumeric(ch) || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    @Test
    void testIsHex_NumericChars() {
        assertTrue(CharUtils.isHex('0'));
        assertTrue(CharUtils.isHex('9'));
    }

    @Test
    void testIsHex_LowerHexChars() {
        assertTrue(CharUtils.isHex('a'));
        assertTrue(CharUtils.isHex('f'));
        assertTrue(CharUtils.isHex('c'));
    }

    @Test
    void testIsHex_UpperHexChars() {
        assertTrue(CharUtils.isHex('A'));
        assertTrue(CharUtils.isHex('F'));
        assertTrue(CharUtils.isHex('C'));
    }

    @Test
    void testIsHex_NonHexChars() {
        assertFalse(CharUtils.isHex('g'));
        assertFalse(CharUtils.isHex('G'));
        assertFalse(CharUtils.isHex(' '));
        assertFalse(CharUtils.isHex('$'));
        assertFalse(CharUtils.isHex('\n'));
        assertFalse(CharUtils.isHex('€'));
        assertFalse(CharUtils.isHex('\0'));
        assertFalse(CharUtils.isHex((char) 128));
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
        assertFalse(CharUtils.isOctal('\n'));
        assertFalse(CharUtils.isOctal('€'));
        assertFalse(CharUtils.isOctal('\0'));
        assertFalse(CharUtils.isOctal((char) 128));
    }

    // --- toChar(final Character ch) ---
    // @requires ch != null;
    // @ensures \result == ch.charValue();
    @Test
    void testToChar_Character_NonNull() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('5', CharUtils.toChar(Character.valueOf('5')));
        assertEquals('\0', CharUtils.toChar(Character.valueOf('\0')));
        assertEquals('€', CharUtils.toChar(Character.valueOf('€')));
    }

    @Test
    void testToChar_Character_Null() {
        assertThrows(NullPointerException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(final Character ch, final char defaultValue) ---
    // @ensures ch == null ? \result == defaultValue : \result == ch.charValue();
    @Test
    void testToChar_CharacterWithDefault_NonNull() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'y'));
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
    void testToChar_String_Valid() {
        assertEquals('a', CharUtils.toChar("a"));
        assertEquals('Z', CharUtils.toChar("Z"));
        assertEquals('5', CharUtils.toChar("5"));
        assertEquals('\0', CharUtils.toChar("\0"));
        assertEquals('€', CharUtils.toChar("€"));
    }

    @Test
    void testToChar_String_Null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null));
    }

    @Test
    void testToChar_String_Empty() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""));
    }

    @Test
    void testToChar_String_MultipleChars() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("ab"));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("abc"));
    }

    // --- toChar(final String str, final char defaultValue) ---
    // @ensures str == null || str.length() != 1 ? \result == defaultValue : \result == str.charAt(0);
    @Test
    void testToChar_StringWithDefault_Valid() {
        assertEquals('a', CharUtils.toChar("a", 'x'));
        assertEquals('Z', CharUtils.toChar("Z", 'y'));
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
    void testToChar_StringWithDefault_MultipleChars() {
        assertEquals('x', CharUtils.toChar("ab", 'x'));
        assertEquals(' ', CharUtils.toChar("abc", ' '));
    }

    // --- toCharacterObject(final char c) ---
    // @ensures \result != null && \result.charValue() == c;
    @Test
    void testToCharacterObject_char() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject('5'));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject('\0'));
        assertEquals(Character.valueOf('€'), CharUtils.toCharacterObject('€'));
    }

    // --- toCharacterObject(final String str) ---
    // @ensures str == null || str.length() != 1 ? \result == null : \result.charValue() == str.charAt(0);
    @Test
    void testToCharacterObject_String_Valid() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("a"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Z"));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject("5"));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject("\0"));
        assertEquals(Character.valueOf('€'), CharUtils.toCharacterObject("€"));
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
    void testToCharacterObject_String_MultipleChars() {
        assertNull(CharUtils.toCharacterObject("ab"));
        assertNull(CharUtils.toCharacterObject("abc"));
    }

    // --- toIntValue(final char ch) ---
    // @requires isAsciiNumeric(ch);
    // @ensures \result == (ch - '0');
    @Test
    void testToIntValue_char_ValidNumeric() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(1, CharUtils.toIntValue('1'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_char_NonNumeric() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('€'));
    }

    // --- toIntValue(final char ch, final int defaultValue) ---
    // @ensures isAsciiNumeric(ch) ? \result == (ch - '0') : \result == defaultValue;
    @Test
    void testToIntValue_charWithDefault_ValidNumeric() {
        assertEquals(0, CharUtils.toIntValue('0', 99));
        assertEquals(5, CharUtils.toIntValue('5', 99));
    }

    @Test
    void testToIntValue_charWithDefault_NonNumeric() {
        assertEquals(99, CharUtils.toIntValue('a', 99));
        assertEquals(-1, CharUtils.toIntValue(' ', -1));
        assertEquals(0, CharUtils.toIntValue('€', 0));
    }

    // --- toIntValue(final Character ch) ---
    // @requires ch != null && isAsciiNumeric(ch.charValue());
    // @ensures \result == (ch.charValue() - '0');
    @Test
    void testToIntValue_Character_ValidNumeric() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(1, CharUtils.toIntValue(Character.valueOf('1')));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9')));
    }

    @Test
    void testToIntValue_Character_Null() {
        assertThrows(NullPointerException.class, () -> CharUtils.toIntValue(null));
    }

    @Test
    void testToIntValue_Character_NonNumeric() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(' ')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('€')));
    }

    // --- toIntValue(final Character ch, final int defaultValue) ---
    // @ensures ch == null || !isAsciiNumeric(ch.charValue()) ? \result == defaultValue : \result == (ch.charValue() - '0');
    @Test
    void testToIntValue_CharacterWithDefault_ValidNumeric() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0'), 99));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5'), 99));
    }

    @Test
    void testToIntValue_CharacterWithDefault_Null() {
        assertEquals(99, CharUtils.toIntValue(null, 99));
        assertEquals(-1, CharUtils.toIntValue(null, -1));
    }

    @Test
    void testToIntValue_CharacterWithDefault_NonNumeric() {
        assertEquals(99, CharUtils.toIntValue(Character.valueOf('a'), 99));
        assertEquals(-1, CharUtils.toIntValue(Character.valueOf(' '), -1));
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('€'), 0));
    }

    // --- toString(final char ch) ---
    // @ensures \result != null && \result.length() == 1 && \result.charAt(0) == ch;
    @Test
    void testToString_char() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("5", CharUtils.toString('5'));
        assertEquals("\0", CharUtils.toString('\0'));
        assertEquals("€", CharUtils.toString('€'));
    }

    // --- toString(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.length() == 1 && \result.charAt(0) == ch.charValue();
    @Test
    void testToString_Character_NonNull() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("5", CharUtils.toString(Character.valueOf('5')));
        assertEquals("\0", CharUtils.toString(Character.valueOf('\0')));
        assertEquals("€", CharUtils.toString(Character.valueOf('€')));
    }

    @Test
    void testToString_Character_Null() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(final char ch) ---
    // @ensures \result != null && \result.length() == 6 && \result.startsWith("\\u");
    @Test
    void testUnicodeEscaped_char() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\0'));
        assertEquals("\\u20AC", CharUtils.unicodeEscaped('€'));
        assertEquals("\\uFFFF", CharUtils.unicodeEscaped(Character.MAX_VALUE));
    }

    // --- unicodeEscaped(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.length() == 6 && \result.startsWith("\\u");
    @Test
    void testUnicodeEscaped_Character_NonNull() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
        assertEquals("\\u0041", CharUtils.unicodeEscaped(Character.valueOf('A')));
        assertEquals("\\u0030", CharUtils.unicodeEscaped(Character.valueOf('0')));
        assertEquals("\\u0000", CharUtils.unicodeEscaped(Character.valueOf('\0')));
        assertEquals("\\u20AC", CharUtils.unicodeEscaped(Character.valueOf('€')));
        assertEquals("\\uFFFF", CharUtils.unicodeEscaped(Character.MAX_VALUE));
    }

    @Test
    void testUnicodeEscaped_Character_Null() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}