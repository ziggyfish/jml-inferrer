package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3CP3C {

    // --- compare(char x, char y) ---
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

    // --- isAscii(char ch) ---
    @Test
    void testIsAscii_AsciiChars() {
        assertTrue(CharUtils.isAscii('a'));
        assertTrue(CharUtils.isAscii('Z'));
        assertTrue(CharUtils.isAscii('0'));
        assertTrue(CharUtils.isAscii('9'));
        assertTrue(CharUtils.isAscii(' '));
        assertTrue(CharUtils.isAscii('!'));
        assertTrue(CharUtils.isAscii('~')); // Max ASCII
        assertTrue(CharUtils.isAscii('\0')); // Min ASCII
    }

    @Test
    void testIsAscii_NonAsciiChars() {
        assertFalse(CharUtils.isAscii('é'));
        assertFalse(CharUtils.isAscii('ü'));
        assertFalse(CharUtils.isAscii('€'));
        assertFalse(CharUtils.isAscii('水'));
        assertFalse(CharUtils.isAscii('\u0080')); // First non-ASCII
        assertFalse(CharUtils.isAscii(Character.MAX_VALUE));
    }

    // --- isAsciiAlpha(char ch) ---
    @Test
    void testIsAsciiAlpha_AsciiLetters() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
    }

    @Test
    void testIsAsciiAlpha_NonAsciiLetters() {
        assertFalse(CharUtils.isAsciiAlpha('0'));
        assertFalse(CharUtils.isAsciiAlpha('9'));
        assertFalse(CharUtils.isAsciiAlpha(' '));
        assertFalse(CharUtils.isAsciiAlpha('!'));
        assertFalse(CharUtils.isAsciiAlpha('@'));
        assertFalse(CharUtils.isAsciiAlpha('{')); // After 'z'
        assertFalse(CharUtils.isAsciiAlpha('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlpha('é'));
        assertFalse(CharUtils.isAsciiAlpha('\0'));
        assertFalse(CharUtils.isAsciiAlpha('\u0080'));
    }

    // --- isAsciiAlphaLower(char ch) ---
    @Test
    void testIsAsciiAlphaLower_LowercaseAsciiLetters() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
    }

    @Test
    void testIsAsciiAlphaLower_NonLowercaseAsciiLetters() {
        assertFalse(CharUtils.isAsciiAlphaLower('A'));
        assertFalse(CharUtils.isAsciiAlphaLower('Z'));
        assertFalse(CharUtils.isAsciiAlphaLower('0'));
        assertFalse(CharUtils.isAsciiAlphaLower(' '));
        assertFalse(CharUtils.isAsciiAlphaLower('!'));
        assertFalse(CharUtils.isAsciiAlphaLower('{'));
        assertFalse(CharUtils.isAsciiAlphaLower('`'));
        assertFalse(CharUtils.isAsciiAlphaLower('é'));
    }

    // --- isAsciiAlphanumeric(char ch) ---
    @Test
    void testIsAsciiAlphanumeric_AlphanumericAscii() {
        assertTrue(CharUtils.isAsciiAlphanumeric('a'));
        assertTrue(CharUtils.isAsciiAlphanumeric('z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('A'));
        assertTrue(CharUtils.isAsciiAlphanumeric('Z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('0'));
        assertTrue(CharUtils.isAsciiAlphanumeric('9'));
    }

    @Test
    void testIsAsciiAlphanumeric_NonAlphanumericAscii() {
        assertFalse(CharUtils.isAsciiAlphanumeric(' '));
        assertFalse(CharUtils.isAsciiAlphanumeric('!'));
        assertFalse(CharUtils.isAsciiAlphanumeric('@'));
        assertFalse(CharUtils.isAsciiAlphanumeric('{'));
        assertFalse(CharUtils.isAsciiAlphanumeric('`'));
        assertFalse(CharUtils.isAsciiAlphanumeric('/'));
        assertFalse(CharUtils.isAsciiAlphanumeric(':'));
        assertFalse(CharUtils.isAsciiAlphanumeric('é'));
    }

    // --- isAsciiAlphaUpper(char ch) ---
    @Test
    void testIsAsciiAlphaUpper_UppercaseAsciiLetters() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
    }

    @Test
    void testIsAsciiAlphaUpper_NonUppercaseAsciiLetters() {
        assertFalse(CharUtils.isAsciiAlphaUpper('a'));
        assertFalse(CharUtils.isAsciiAlphaUpper('z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('0'));
        assertFalse(CharUtils.isAsciiAlphaUpper(' '));
        assertFalse(CharUtils.isAsciiAlphaUpper('!'));
        assertFalse(CharUtils.isAsciiAlphaUpper('['));
        assertFalse(CharUtils.isAsciiAlphaUpper('@'));
        assertFalse(CharUtils.isAsciiAlphaUpper('é'));
    }

    // --- isAsciiControl(char ch) ---
    @Test
    void testIsAsciiControl_ControlChars() {
        assertTrue(CharUtils.isAsciiControl('\0')); // NUL
        assertTrue(CharUtils.isAsciiControl('\u0001')); // SOH
        assertTrue(CharUtils.isAsciiControl('\u001F')); // US
        assertTrue(CharUtils.isAsciiControl('\u007F')); // DEL
    }

    @Test
    void testIsAsciiControl_NonControlChars() {
        assertFalse(CharUtils.isAsciiControl(' ')); // Space is printable
        assertFalse(CharUtils.isAsciiControl('A'));
        assertFalse(CharUtils.isAsciiControl('0'));
        assertFalse(CharUtils.isAsciiControl('~'));
        assertFalse(CharUtils.isAsciiControl('\u0020')); // Space
        assertFalse(CharUtils.isAsciiControl('\u0080')); // Non-ASCII
    }

    // --- isAsciiNumeric(char ch) ---
    @Test
    void testIsAsciiNumeric_NumericAscii() {
        assertTrue(CharUtils.isAsciiNumeric('0'));
        assertTrue(CharUtils.isAsciiNumeric('9'));
    }

    @Test
    void testIsAsciiNumeric_NonNumericAscii() {
        assertFalse(CharUtils.isAsciiNumeric('a'));
        assertFalse(CharUtils.isAsciiNumeric('A'));
        assertFalse(CharUtils.isAsciiNumeric(' '));
        assertFalse(CharUtils.isAsciiNumeric('!'));
        assertFalse(CharUtils.isAsciiNumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiNumeric(':')); // After '9'
        assertFalse(CharUtils.isAsciiNumeric('é'));
    }

    // --- isAsciiPrintable(char ch) ---
    @Test
    void testIsAsciiPrintable_PrintableAscii() {
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space
        assertTrue(CharUtils.isAsciiPrintable('!'));
        assertTrue(CharUtils.isAsciiPrintable('~')); // Tilde
        assertTrue(CharUtils.isAsciiPrintable('a'));
        assertTrue(CharUtils.isAsciiPrintable('Z'));
        assertTrue(CharUtils.isAsciiPrintable('5'));
    }

    @Test
    void testIsAsciiPrintable_NonPrintableAscii() {
        assertFalse(CharUtils.isAsciiPrintable('\0')); // NUL
        assertFalse(CharUtils.isAsciiPrintable('\u001F')); // US
        assertFalse(CharUtils.isAsciiPrintable('\u007F')); // DEL
        assertFalse(CharUtils.isAsciiPrintable('é'));
        assertFalse(CharUtils.isAsciiPrintable('\u0080'));
    }

    // --- isHex(char ch) ---
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
        assertFalse(CharUtils.isHex('!'));
        assertFalse(CharUtils.isHex('/'));
        assertFalse(CharUtils.isHex(':'));
        assertFalse(CharUtils.isHex('@'));
        assertFalse(CharUtils.isHex('`'));
        assertFalse(CharUtils.isHex('é'));
    }

    // --- isOctal(char ch) ---
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
        assertFalse(CharUtils.isOctal('!'));
        assertFalse(CharUtils.isOctal('/'));
        assertFalse(CharUtils.isOctal(':'));
        assertFalse(CharUtils.isOctal('é'));
    }

    // --- toChar(Character ch) ---
    @Test
    void testToChar_CharacterObject_NonNull() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('5', CharUtils.toChar(Character.valueOf('5')));
        assertEquals('\0', CharUtils.toChar(Character.valueOf('\0')));
    }

    @Test
    void testToChar_CharacterObject_Null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(Character ch, char defaultValue) ---
    @Test
    void testToChar_CharacterObjectWithDefault_NonNull() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'y'));
    }

    @Test
    void testToChar_CharacterObjectWithDefault_Null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    // --- toChar(String str) ---
    @Test
    void testToChar_String_SingleChar() {
        assertEquals('a', CharUtils.toChar("a"));
        assertEquals('Z', CharUtils.toChar("Z"));
        assertEquals('5', CharUtils.toChar("5"));
        assertEquals('\0', CharUtils.toChar("\0"));
    }

    @Test
    void testToChar_String_Empty() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""));
    }

    @Test
    void testToChar_String_MultipleChars() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("abc"));
    }

    @Test
    void testToChar_String_Null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null));
    }

    // --- toChar(String str, char defaultValue) ---
    @Test
    void testToChar_StringWithDefault_SingleChar() {
        assertEquals('a', CharUtils.toChar("a", 'x'));
        assertEquals('Z', CharUtils.toChar("Z", 'y'));
    }

    @Test
    void testToChar_StringWithDefault_Empty() {
        assertEquals('x', CharUtils.toChar("", 'x'));
        assertEquals(' ', CharUtils.toChar("", ' '));
    }

    @Test
    void testToChar_StringWithDefault_MultipleChars() {
        assertEquals('x', CharUtils.toChar("abc", 'x'));
        assertEquals(' ', CharUtils.toChar("hello", ' '));
    }

    @Test
    void testToChar_StringWithDefault_Null() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    // --- toCharacterObject(char c) ---
    @Test
    void testToCharacterObject_PrimitiveChar() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject('5'));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject('\0'));
        assertEquals(Character.valueOf(Character.MIN_VALUE), CharUtils.toCharacterObject(Character.MIN_VALUE));
        assertEquals(Character.valueOf(Character.MAX_VALUE), CharUtils.toCharacterObject(Character.MAX_VALUE));
    }

    // --- toCharacterObject(String str) ---
    @Test
    void testToCharacterObject_String_SingleChar() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("a"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Z"));
        assertEquals(Character.valueOf('5'), CharUtils.toCharacterObject("5"));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject("\0"));
    }

    @Test
    void testToCharacterObject_String_Empty() {
        assertNull(CharUtils.toCharacterObject(""));
    }

    @Test
    void testToCharacterObject_String_MultipleChars() {
        assertNull(CharUtils.toCharacterObject("abc"));
    }

    @Test
    void testToCharacterObject_String_Null() {
        assertNull(CharUtils.toCharacterObject(null));
    }

    // --- toIntValue(char ch) ---
    @Test
    void testToIntValue_Char_Numeric() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(5, CharUtils.toIntValue('5'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_Char_NonNumeric() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('!'));
    }

    // --- toIntValue(char ch, int defaultValue) ---
    @Test
    void testToIntValue_CharWithDefault_Numeric() {
        assertEquals(0, CharUtils.toIntValue('0', 99));
        assertEquals(5, CharUtils.toIntValue('5', 99));
    }

    @Test
    void testToIntValue_CharWithDefault_NonNumeric() {
        assertEquals(99, CharUtils.toIntValue('a', 99));
        assertEquals(-1, CharUtils.toIntValue(' ', -1));
    }

    // --- toIntValue(Character ch) ---
    @Test
    void testToIntValue_Character_Numeric() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5')));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9')));
    }

    @Test
    void testToIntValue_Character_NonNumeric() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf(' ')));
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('!')));
    }

    @Test
    void testToIntValue_Character_Null() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(null));
    }

    // --- toIntValue(Character ch, int defaultValue) ---
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

    // --- toString(char ch) ---
    @Test
    void testToString_PrimitiveChar() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("5", CharUtils.toString('5'));
        assertEquals("\0", CharUtils.toString('\0'));
        assertEquals(" ", CharUtils.toString(' '));
    }

    // --- toString(Character ch) ---
    @Test
    void testToString_CharacterObject_NonNull() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("5", CharUtils.toString(Character.valueOf('5')));
        assertEquals("\0", CharUtils.toString(Character.valueOf('\0')));
        assertEquals(" ", CharUtils.toString(Character.valueOf(' ')));
    }

    @Test
    void testToString_CharacterObject_Null() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(char ch) ---
    @Test
    void testUnicodeEscaped_AsciiChars() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(' '));
        assertEquals("\\u007e", CharUtils.unicodeEscaped('~'));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\0'));
    }

    @Test
    void testUnicodeEscaped_NonAsciiChars() {
        assertEquals("\\u00e9", CharUtils.unicodeEscaped('é'));
        assertEquals("\\u00fc", CharUtils.unicodeEscaped('ü'));
        assertEquals("\\u20ac", CharUtils.unicodeEscaped('€'));
        assertEquals("\\u6c34", CharUtils.unicodeEscaped('水'));
        assertEquals("\\uffff", CharUtils.unicodeEscaped(Character.MAX_VALUE));
    }

    // --- unicodeEscaped(Character ch) ---
    @Test
    void testUnicodeEscaped_CharacterObject_NonNull() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
        assertEquals("\\u00e9", CharUtils.unicodeEscaped(Character.valueOf('é')));
        assertEquals("\\u0000", CharUtils.unicodeEscaped(Character.valueOf('\0')));
    }

    @Test
    void testUnicodeEscaped_CharacterObject_Null() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}