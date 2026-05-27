package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3CP3C {

    // --- compare(final char x, final char y) ---
    @Test
    void testCompare_EqualChars() {
        assertEquals(0, CharUtils.compare('a', 'a'));
        assertEquals(0, CharUtils.compare('Z', 'Z'));
        assertEquals(0, CharUtils.compare('5', '5'));
        assertEquals(0, CharUtils.compare('\0', '\0')); // Null char
        assertEquals(0, CharUtils.compare(' ', ' '));
        assertEquals(0, CharUtils.compare('é', 'é')); // Non-ASCII
    }

    @Test
    void testCompare_XGreaterThanY() {
        assertTrue(CharUtils.compare('b', 'a') > 0);
        assertTrue(CharUtils.compare('Z', 'A') > 0);
        assertTrue(CharUtils.compare('9', '0') > 0);
        assertTrue(CharUtils.compare(' ', '\0') > 0);
        assertTrue(CharUtils.compare('é', 'a') > 0); // Non-ASCII vs ASCII
    }

    @Test
    void testCompare_XLessThanY() {
        assertTrue(CharUtils.compare('a', 'b') < 0);
        assertTrue(CharUtils.compare('A', 'Z') < 0);
        assertTrue(CharUtils.compare('0', '9') < 0);
        assertTrue(CharUtils.compare('\0', ' ') < 0);
        assertTrue(CharUtils.compare('a', 'é') < 0); // ASCII vs Non-ASCII
    }

    // --- isAscii(final char ch) ---
    @Test
    void testIsAscii_AsciiChars() {
        assertTrue(CharUtils.isAscii('a'));
        assertTrue(CharUtils.isAscii('Z'));
        assertTrue(CharUtils.isAscii('0'));
        assertTrue(CharUtils.isAscii(' '));
        assertTrue(CharUtils.isAscii('\n')); // Control character
        assertTrue(CharUtils.isAscii('\0')); // Null character
        assertTrue(CharUtils.isAscii((char) 127)); // DEL character
    }

    @Test
    void testIsAscii_NonAsciiChars() {
        assertFalse(CharUtils.isAscii('é'));
        assertFalse(CharUtils.isAscii('ñ'));
        assertFalse(CharUtils.isAscii('€'));
        assertFalse(CharUtils.isAscii('你好')); // Chinese character
        assertFalse(CharUtils.isAscii((char) 128)); // First non-ASCII char
        assertFalse(CharUtils.isAscii((char) 255)); // Last char in extended ASCII range
    }

    // --- isAsciiAlpha(final char ch) ---
    @Test
    void testIsAsciiAlpha_AlphaChars() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
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
    }

    // --- isAsciiAlphaLower(final char ch) ---
    @Test
    void testIsAsciiAlphaLower_LowercaseAlphaChars() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
    }

    @Test
    void testIsAsciiAlphaLower_NonLowercaseAlphaChars() {
        assertFalse(CharUtils.isAsciiAlphaLower('A'));
        assertFalse(CharUtils.isAsciiAlphaLower('Z'));
        assertFalse(CharUtils.isAsciiAlphaLower('0'));
        assertFalse(CharUtils.isAsciiAlphaLower(' '));
        assertFalse(CharUtils.isAsciiAlphaLower('$'));
        assertFalse(CharUtils.isAsciiAlphaLower('é'));
        assertFalse(CharUtils.isAsciiAlphaLower('\0'));
    }

    // --- isAsciiAlphanumeric(final char ch) ---
    @Test
    void testIsAsciiAlphanumeric_AlphanumericChars() {
        assertTrue(CharUtils.isAsciiAlphanumeric('a'));
        assertTrue(CharUtils.isAsciiAlphanumeric('z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('A'));
        assertTrue(CharUtils.isAsciiAlphanumeric('Z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('0'));
        assertTrue(CharUtils.isAsciiAlphanumeric('9'));
    }

    @Test
    void testIsAsciiAlphanumeric_NonAlphanumericChars() {
        assertFalse(CharUtils.isAsciiAlphanumeric(' '));
        assertFalse(CharUtils.isAsciiAlphanumeric('$'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\n'));
        assertFalse(CharUtils.isAsciiAlphanumeric('é'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\0'));
    }

    // --- isAsciiAlphaUpper(final char ch) ---
    @Test
    void testIsAsciiAlphaUpper_UppercaseAlphaChars() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
    }

    @Test
    void testIsAsciiAlphaUpper_NonUppercaseAlphaChars() {
        assertFalse(CharUtils.isAsciiAlphaUpper('a'));
        assertFalse(CharUtils.isAsciiAlphaUpper('z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('0'));
        assertFalse(CharUtils.isAsciiAlphaUpper(' '));
        assertFalse(CharUtils.isAsciiAlphaUpper('$'));
        assertFalse(CharUtils.isAsciiAlphaUpper('É')); // Non-ASCII upper
        assertFalse(CharUtils.isAsciiAlphaUpper('\0'));
    }

    // --- isAsciiControl(final char ch) ---
    @Test
    void testIsAsciiControl_ControlChars() {
        assertTrue(CharUtils.isAsciiControl('\0')); // NUL
        assertTrue(CharUtils.isAsciiControl('\u0001')); // SOH
        assertTrue(CharUtils.isAsciiControl('\u001F')); // US
        assertTrue(CharUtils.isAsciiControl('\u007F')); // DEL
        assertTrue(CharUtils.isAsciiControl('\n')); // LF
        assertTrue(CharUtils.isAsciiControl('\r')); // CR
        assertTrue(CharUtils.isAsciiControl('\t')); // TAB
    }

    @Test
    void testIsAsciiControl_NonControlChars() {
        assertFalse(CharUtils.isAsciiControl(' ')); // Space is printable
        assertFalse(CharUtils.isAsciiControl('a'));
        assertFalse(CharUtils.isAsciiControl('Z'));
        assertFalse(CharUtils.isAsciiControl('0'));
        assertFalse(CharUtils.isAsciiControl('é'));
        assertFalse(CharUtils.isAsciiControl((char) 32)); // Space
        assertFalse(CharUtils.isAsciiControl((char) 126)); // Tilde
    }

    // --- isAsciiNumeric(final char ch) ---
    @Test
    void testIsAsciiNumeric_NumericChars() {
        assertTrue(CharUtils.isAsciiNumeric('0'));
        assertTrue(CharUtils.isAsciiNumeric('9'));
    }

    @Test
    void testIsAsciiNumeric_NonNumericChars() {
        assertFalse(CharUtils.isAsciiNumeric('a'));
        assertFalse(CharUtils.isAsciiNumeric('Z'));
        assertFalse(CharUtils.isAsciiNumeric(' '));
        assertFalse(CharUtils.isAsciiNumeric('$'));
        assertFalse(CharUtils.isAsciiNumeric('\n'));
        assertFalse(CharUtils.isAsciiNumeric('é'));
        assertFalse(CharUtils.isAsciiNumeric('\0'));
    }

    // --- isAsciiPrintable(final char ch) ---
    @Test
    void testIsAsciiPrintable_PrintableChars() {
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space
        assertTrue(CharUtils.isAsciiPrintable('!'));
        assertTrue(CharUtils.isAsciiPrintable('~')); // Tilde
        assertTrue(CharUtils.isAsciiPrintable('a'));
        assertTrue(CharUtils.isAsciiPrintable('Z'));
        assertTrue(CharUtils.isAsciiPrintable('0'));
    }

    @Test
    void testIsAsciiPrintable_NonPrintableChars() {
        assertFalse(CharUtils.isAsciiPrintable('\0')); // NUL
        assertFalse(CharUtils.isAsciiPrintable('\n')); // LF
        assertFalse(CharUtils.isAsciiPrintable('\r')); // CR
        assertFalse(CharUtils.isAsciiPrintable('\u001F')); // US
        assertFalse(CharUtils.isAsciiPrintable('\u007F')); // DEL
        assertFalse(CharUtils.isAsciiPrintable('é')); // Non-ASCII
    }

    // --- isHex(final char ch) ---
    @Test
    void testIsHex_HexChars() {
        assertTrue(CharUtils.isHex('0'));
        assertTrue(CharUtils.isHex('9'));
        assertTrue(CharUtils.isHex('a'));
        assertTrue(CharUtils.isHex('f'));
        assertTrue(CharUtils.isHex('A'));
        assertTrue(CharUtils.isHex('F'));
    }

    @Test
    void testIsHex_NonHexChars() {
        assertFalse(CharUtils.isHex('g'));
        assertFalse(CharUtils.isHex('G'));
        assertFalse(CharUtils.isHex(' '));
        assertFalse(CharUtils.isHex('$'));
        assertFalse(CharUtils.isHex('\n'));
        assertFalse(CharUtils.isHex('é'));
        assertFalse(CharUtils.isHex('\0'));
    }

    // --- isOctal(final char ch) ---
    @Test
    void testIsOctal_OctalChars() {
        assertTrue(CharUtils.isOctal('0'));
        assertTrue(CharUtils.isOctal('7'));
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
        assertFalse(CharUtils.isOctal('é'));
        assertFalse(CharUtils.isOctal('\0'));
    }

    // --- toChar(final Character ch) ---
    @Test
    void testToChar_Character_NonNull() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('5', CharUtils.toChar(Character.valueOf('5')));
        assertEquals('\0', CharUtils.toChar(Character.valueOf('\0')));
    }

    @Test
    void testToChar_Character_Null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(final Character ch, final char defaultValue) ---
    @Test
    void testToChar_CharacterWithDefault_NonNull() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'y'));
    }

    @Test
    void testToChar_CharacterWithDefault_Null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    // --- toChar(final String str) ---
    @Test
    void testToChar_String_SingleChar() {
        assertEquals('a', CharUtils.toChar("a"));
        assertEquals('Z', CharUtils.toChar("Z"));
        assertEquals('5', CharUtils.toChar("5"));
        assertEquals(' ', CharUtils.toChar(" "));
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
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("abc"));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("ab"));
    }

    // --- toChar(final String str, final char defaultValue) ---
    @Test
    void testToChar_StringWithDefault_SingleChar() {
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
        assertEquals('x', CharUtils.toChar("abc", 'x'));
        assertEquals('y', CharUtils.toChar("ab", 'y'));
    }

    // --- toCharacterObject(final char c) ---
    @Test
    void testToCharacterObject_char() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject('5'));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject('\0'));
    }

    // --- toCharacterObject(final String str) ---
    @Test
    void testToCharacterObject_String_SingleChar() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("a"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Z"));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject("5"));
        assertEquals(Character.valueOf(' '), CharUtils.toCharacterObject(" "));
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
        assertNull(CharUtils.toCharacterObject("abc"));
        assertNull(CharUtils.toCharacterObject("ab"));
    }

    // --- toIntValue(final char ch) ---
    @Test
    void testToIntValue_char_Numeric() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(5, CharUtils.toIntValue('5'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_char_NonNumeric() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('$'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('\0'));
    }

    // --- toIntValue(final char ch, final int defaultValue) ---
    @Test
    void testToIntValue_charWithDefault_Numeric() {
        assertEquals(0, CharUtils.toIntValue('0', 99));
        assertEquals(5, CharUtils.toIntValue('5', 99));
    }

    @Test
    void testToIntValue_charWithDefault_NonNumeric() {
        assertEquals(99, CharUtils.toIntValue('a', 99));
        assertEquals(-1, CharUtils.toIntValue(' ', -1));
        assertEquals(0, CharUtils.toIntValue('$', 0));
    }

    // --- toIntValue(final Character ch) ---
    @Test
    void testToIntValue_Character_Numeric() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5')));
    }

    @Test
    void testToIntValue_Character_NonNumeric() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(' ')));
    }

    @Test
    void testToIntValue_Character_Null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(null));
    }

    // --- toIntValue(final Character ch, final int defaultValue) ---
    @Test
    void testToIntValue_CharacterWithDefault_Numeric() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0'), 99));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5'), 99));
    }

    @Test
    void testToIntValue_CharacterWithDefault_NonNumeric() {
        assertEquals(99, CharUtils.toIntValue(Character.valueOf('a'), 99));
        assertEquals(-1, CharUtils.toIntValue(Character.valueOf(' '), -1));
    }

    @Test
    void testToIntValue_CharacterWithDefault_Null() {
        assertEquals(99, CharUtils.toIntValue(null, 99));
        assertEquals(-1, CharUtils.toIntValue(null, -1));
    }

    // --- toString(final char ch) ---
    @Test
    void testToString_char() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("5", CharUtils.toString('5'));
        assertEquals(" ", CharUtils.toString(' '));
        assertEquals("\0", CharUtils.toString('\0')); // Null char
        assertEquals("é", CharUtils.toString('é')); // Non-ASCII
    }

    // --- toString(final Character ch) ---
    @Test
    void testToString_Character_NonNull() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("5", CharUtils.toString(Character.valueOf('5')));
        assertEquals(" ", CharUtils.toString(Character.valueOf(' ')));
        assertEquals("\0", CharUtils.toString(Character.valueOf('\0')));
        assertEquals("é", CharUtils.toString(Character.valueOf('é')));
    }

    @Test
    void testToString_Character_Null() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(final char ch) ---
    @Test
    void testUnicodeEscaped_char_Ascii() {
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(' '));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\0'));
    }

    @Test
    void testUnicodeEscaped_char_NonAscii() {
        assertEquals("\\u00E9", CharUtils.unicodeEscaped('é'));
        assertEquals("\\u00F1", CharUtils.unicodeEscaped('ñ'));
        assertEquals("\\u20AC", CharUtils.unicodeEscaped('€'));
        assertEquals("\\u4F60", CharUtils.unicodeEscaped('你'));
    }

    // --- unicodeEscaped(final Character ch) ---
    @Test
    void testUnicodeEscaped_Character_NonNullAscii() {
        assertEquals("\\u0041", CharUtils.unicodeEscaped(Character.valueOf('A')));
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
    }

    @Test
    void testUnicodeEscaped_Character_NonNullNonAscii() {
        assertEquals("\\u00E9", CharUtils.unicodeEscaped(Character.valueOf('é')));
        assertEquals("\\u20AC", CharUtils.unicodeEscaped(Character.valueOf('€')));
    }

    @Test
    void testUnicodeEscaped_Character_Null() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}