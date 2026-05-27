package org.apache.commons.lang3.p3;

import org.apache.commons.lang3.CharUtils;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class CharUtilsTestP3P3 {

    // --- compare(final char x, final char y) ---
    // @ensures \result == (x - y);
    @Test
    void testCompare_NormalBehavior() {
        assertEquals(0, CharUtils.compare('a', 'a'));
        assertEquals(1, CharUtils.compare('b', 'a'));
        assertEquals(-1, CharUtils.compare('a', 'b'));
        assertEquals(25, CharUtils.compare('z', 'a'));
        assertEquals(-25, CharUtils.compare('a', 'z'));
        assertEquals(1, CharUtils.compare('1', '0'));
        assertEquals(-1, CharUtils.compare('0', '1'));
        assertEquals(0, CharUtils.compare('\0', '\0')); // Null character
        assertEquals(1, CharUtils.compare('\u0001', '\0'));
        assertEquals(-1, CharUtils.compare('\0', '\u0001'));
        assertEquals(100, CharUtils.compare('d', '\0')); // 'd' (100) - '\0' (0)
        assertEquals(-100, CharUtils.compare('\0', 'd'));
        assertEquals(1, CharUtils.compare('A', '@')); // 'A' (65) - '@' (64)
    }

    // --- isAscii(final char ch) ---
    // @ensures \result == (ch < 128);
    @Test
    void testIsAscii_NormalBehavior() {
        assertTrue(CharUtils.isAscii('a'));
        assertTrue(CharUtils.isAscii('Z'));
        assertTrue(CharUtils.isAscii('0'));
        assertTrue(CharUtils.isAscii(' '));
        assertTrue(CharUtils.isAscii('\n'));
        assertTrue(CharUtils.isAscii('\0')); // Null character is ASCII
        assertTrue(CharUtils.isAscii('\u007F')); // DEL character is ASCII (127)
    }

    @Test
    void testIsAscii_EdgeCases() {
        assertFalse(CharUtils.isAscii('\u0080')); // First non-ASCII character
        assertFalse(CharUtils.isAscii('é'));
        assertFalse(CharUtils.isAscii('€'));
        assertFalse(CharUtils.isAscii('你好')); // Multi-byte character, but char is single code point
        assertFalse(CharUtils.isAscii('\uFFFF')); // Max char value
    }

    // --- isAsciiAlpha(final char ch) ---
    // @ensures \result == (isAsciiAlphaUpper(ch) || isAsciiAlphaLower(ch));
    @Test
    void testIsAsciiAlpha_NormalBehavior() {
        assertTrue(CharUtils.isAsciiAlpha('a'));
        assertTrue(CharUtils.isAsciiAlpha('z'));
        assertTrue(CharUtils.isAsciiAlpha('A'));
        assertTrue(CharUtils.isAsciiAlpha('Z'));
    }

    @Test
    void testIsAsciiAlpha_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlpha('0'));
        assertFalse(CharUtils.isAsciiAlpha('9'));
        assertFalse(CharUtils.isAsciiAlpha(' '));
        assertFalse(CharUtils.isAsciiAlpha('\n'));
        assertFalse(CharUtils.isAsciiAlpha('@'));
        assertFalse(CharUtils.isAsciiAlpha('['));
        assertFalse(CharUtils.isAsciiAlpha('`'));
        assertFalse(CharUtils.isAsciiAlpha('{'));
        assertFalse(CharUtils.isAsciiAlpha('\0'));
        assertFalse(CharUtils.isAsciiAlpha('\u0080'));
    }

    // --- isAsciiAlphaLower(final char ch) ---
    // @ensures \result == (ch >= 'a' && ch <= 'z');
    @Test
    void testIsAsciiAlphaLower_NormalBehavior() {
        assertTrue(CharUtils.isAsciiAlphaLower('a'));
        assertTrue(CharUtils.isAsciiAlphaLower('m'));
        assertTrue(CharUtils.isAsciiAlphaLower('z'));
    }

    @Test
    void testIsAsciiAlphaLower_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlphaLower('A'));
        assertFalse(CharUtils.isAsciiAlphaLower('Z'));
        assertFalse(CharUtils.isAsciiAlphaLower('0'));
        assertFalse(CharUtils.isAsciiAlphaLower('9'));
        assertFalse(CharUtils.isAsciiAlphaLower(' '));
        assertFalse(CharUtils.isAsciiAlphaLower('@'));
        assertFalse(CharUtils.isAsciiAlphaLower('['));
        assertFalse(CharUtils.isAsciiAlphaLower('`')); // Before 'a'
        assertFalse(CharUtils.isAsciiAlphaLower('{')); // After 'z'
        assertFalse(CharUtils.isAsciiAlphaLower('\0'));
        assertFalse(CharUtils.isAsciiAlphaLower('\u0080'));
    }

    // --- isAsciiAlphanumeric(final char ch) ---
    // @ensures \result == (isAsciiAlpha(ch) || isAsciiNumeric(ch));
    @Test
    void testIsAsciiAlphanumeric_NormalBehavior() {
        assertTrue(CharUtils.isAsciiAlphanumeric('a'));
        assertTrue(CharUtils.isAsciiAlphanumeric('Z'));
        assertTrue(CharUtils.isAsciiAlphanumeric('0'));
        assertTrue(CharUtils.isAsciiAlphanumeric('9'));
    }

    @Test
    void testIsAsciiAlphanumeric_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlphanumeric(' '));
        assertFalse(CharUtils.isAsciiAlphanumeric('\n'));
        assertFalse(CharUtils.isAsciiAlphanumeric('@'));
        assertFalse(CharUtils.isAsciiAlphanumeric('['));
        assertFalse(CharUtils.isAsciiAlphanumeric('`'));
        assertFalse(CharUtils.isAsciiAlphanumeric('{'));
        assertFalse(CharUtils.isAsciiAlphanumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiAlphanumeric(':')); // After '9'
        assertFalse(CharUtils.isAsciiAlphanumeric('\0'));
        assertFalse(CharUtils.isAsciiAlphanumeric('\u0080'));
    }

    // --- isAsciiAlphaUpper(final char ch) ---
    // @ensures \result == (ch >= 'A' && ch <= 'Z');
    @Test
    void testIsAsciiAlphaUpper_NormalBehavior() {
        assertTrue(CharUtils.isAsciiAlphaUpper('A'));
        assertTrue(CharUtils.isAsciiAlphaUpper('M'));
        assertTrue(CharUtils.isAsciiAlphaUpper('Z'));
    }

    @Test
    void testIsAsciiAlphaUpper_EdgeCases() {
        assertFalse(CharUtils.isAsciiAlphaUpper('a'));
        assertFalse(CharUtils.isAsciiAlphaUpper('z'));
        assertFalse(CharUtils.isAsciiAlphaUpper('0'));
        assertFalse(CharUtils.isAsciiAlphaUpper('9'));
        assertFalse(CharUtils.isAsciiAlphaUpper(' '));
        assertFalse(CharUtils.isAsciiAlphaUpper('@')); // Before 'A'
        assertFalse(CharUtils.isAsciiAlphaUpper('[')); // After 'Z'
        assertFalse(CharUtils.isAsciiAlphaUpper('`'));
        assertFalse(CharUtils.isAsciiAlphaUpper('{'));
        assertFalse(CharUtils.isAsciiAlphaUpper('\0'));
        assertFalse(CharUtils.isAsciiAlphaUpper('\u0080'));
    }

    // --- isAsciiControl(final char ch) ---
    // @ensures \result == (ch < 32 || ch == 127);
    @Test
    void testIsAsciiControl_NormalBehavior() {
        assertTrue(CharUtils.isAsciiControl('\0')); // NUL
        assertTrue(CharUtils.isAsciiControl('\u0001')); // SOH
        assertTrue(CharUtils.isAsciiControl('\u001F')); // US (Unit Separator)
        assertTrue(CharUtils.isAsciiControl('\u007F')); // DEL
    }

    @Test
    void testIsAsciiControl_EdgeCases() {
        assertFalse(CharUtils.isAsciiControl(' ')); // Space (32) is not control
        assertFalse(CharUtils.isAsciiControl('a'));
        assertFalse(CharUtils.isAsciiControl('Z'));
        assertFalse(CharUtils.isAsciiControl('0'));
        assertFalse(CharUtils.isAsciiControl('\u0020')); // Space
        assertFalse(CharUtils.isAsciiControl('\u007E')); // Tilde
        assertFalse(CharUtils.isAsciiControl('\u0080')); // Non-ASCII
    }

    // --- isAsciiNumeric(final char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '9');
    @Test
    void testIsAsciiNumeric_NormalBehavior() {
        assertTrue(CharUtils.isAsciiNumeric('0'));
        assertTrue(CharUtils.isAsciiNumeric('5'));
        assertTrue(CharUtils.isAsciiNumeric('9'));
    }

    @Test
    void testIsAsciiNumeric_EdgeCases() {
        assertFalse(CharUtils.isAsciiNumeric('a'));
        assertFalse(CharUtils.isAsciiNumeric('Z'));
        assertFalse(CharUtils.isAsciiNumeric(' '));
        assertFalse(CharUtils.isAsciiNumeric('/')); // Before '0'
        assertFalse(CharUtils.isAsciiNumeric(':')); // After '9'
        assertFalse(CharUtils.isAsciiNumeric('\0'));
        assertFalse(CharUtils.isAsciiNumeric('\u0080'));
    }

    // --- isAsciiPrintable(final char ch) ---
    // @ensures \result == (ch >= 32 && ch < 127);
    @Test
    void testIsAsciiPrintable_NormalBehavior() {
        assertTrue(CharUtils.isAsciiPrintable(' ')); // Space
        assertTrue(CharUtils.isAsciiPrintable('a'));
        assertTrue(CharUtils.isAsciiPrintable('Z'));
        assertTrue(CharUtils.isAsciiPrintable('0'));
        assertTrue(CharUtils.isAsciiPrintable('!'));
        assertTrue(CharUtils.isAsciiPrintable('~')); // Tilde (126)
    }

    @Test
    void testIsAsciiPrintable_EdgeCases() {
        assertFalse(CharUtils.isAsciiPrintable('\0')); // NUL (0)
        assertFalse(CharUtils.isAsciiPrintable('\u001F')); // US (31)
        assertFalse(CharUtils.isAsciiPrintable('\u007F')); // DEL (127)
        assertFalse(CharUtils.isAsciiPrintable('\n')); // Newline (10)
        assertFalse(CharUtils.isAsciiPrintable('\u0080')); // Non-ASCII
    }

    // --- isHex(final char ch) ---
    // @ensures \result == (isAsciiNumeric(ch) || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F'));
    @Test
    void testIsHex_NormalBehavior() {
        assertTrue(CharUtils.isHex('0'));
        assertTrue(CharUtils.isHex('9'));
        assertTrue(CharUtils.isHex('a'));
        assertTrue(CharUtils.isHex('f'));
        assertTrue(CharUtils.isHex('A'));
        assertTrue(CharUtils.isHex('F'));
    }

    @Test
    void testIsHex_EdgeCases() {
        assertFalse(CharUtils.isHex('g')); // After 'f'
        assertFalse(CharUtils.isHex('G')); // After 'F'
        assertFalse(CharUtils.isHex('/')); // Before '0'
        assertFalse(CharUtils.isHex(':')); // After '9'
        assertFalse(CharUtils.isHex('@')); // Before 'A'
        assertFalse(CharUtils.isHex('[')); // After 'Z'
        assertFalse(CharUtils.isHex('`')); // Before 'a'
        assertFalse(CharUtils.isHex('{')); // After 'z'
        assertFalse(CharUtils.isHex(' '));
        assertFalse(CharUtils.isHex('\0'));
        assertFalse(CharUtils.isHex('\u0080'));
    }

    // --- isOctal(final char ch) ---
    // @ensures \result == (ch >= '0' && ch <= '7');
    @Test
    void testIsOctal_NormalBehavior() {
        assertTrue(CharUtils.isOctal('0'));
        assertTrue(CharUtils.isOctal('1'));
        assertTrue(CharUtils.isOctal('7'));
    }

    @Test
    void testIsOctal_EdgeCases() {
        assertFalse(CharUtils.isOctal('8')); // After '7'
        assertFalse(CharUtils.isOctal('9'));
        assertFalse(CharUtils.isOctal('a'));
        assertFalse(CharUtils.isOctal('A'));
        assertFalse(CharUtils.isOctal('/')); // Before '0'
        assertFalse(CharUtils.isOctal(':')); // After '9'
        assertFalse(CharUtils.isOctal(' '));
        assertFalse(CharUtils.isOctal('\0'));
        assertFalse(CharUtils.isOctal('\u0080'));
    }

    // --- toChar(final Character ch) ---
    // @requires ch != null;
    // @ensures \result == ch.charValue();
    @Test
    void testToChar_Character_NormalBehavior() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a')));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z')));
        assertEquals('0', CharUtils.toChar(Character.valueOf('0')));
        assertEquals(' ', CharUtils.toChar(Character.valueOf(' ')));
        assertEquals('\0', CharUtils.toChar(Character.valueOf('\0')));
    }

    @Test
    void testToChar_Character_FailureScenario_NullInput() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null),
                "Expected IllegalArgumentException for null Character input");
    }

    // --- toChar(final Character ch, final char defaultValue) ---
    // @ensures ch == null ? \result == defaultValue : \result == ch.charValue();
    @Test
    void testToChar_CharacterWithDefault_NormalBehavior() {
        assertEquals('a', CharUtils.toChar(Character.valueOf('a'), 'x'));
        assertEquals('Z', CharUtils.toChar(Character.valueOf('Z'), 'y'));
        assertEquals('0', CharUtils.toChar(Character.valueOf('0'), 'z'));
    }

    @Test
    void testToChar_CharacterWithDefault_NullInput() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('\0', CharUtils.toChar(null, '\0'));
        assertEquals(' ', CharUtils.toChar(null, ' '));
    }

    // --- toChar(final String str) ---
    // @requires str != null && str.length() == 1;
    // @ensures \result == str.charAt(0);
    @Test
    void testToChar_String_NormalBehavior() {
        assertEquals('a', CharUtils.toChar("a"));
        assertEquals('Z', CharUtils.toChar("Z"));
        assertEquals('0', CharUtils.toChar("0"));
        assertEquals(' ', CharUtils.toChar(" "));
        assertEquals('\0', CharUtils.toChar("\0"));
    }

    @Test
    void testToChar_String_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(null),
                "Expected IllegalArgumentException for null String input");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(""),
                "Expected IllegalArgumentException for empty String input");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar("ab"),
                "Expected IllegalArgumentException for multi-character String input");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toChar(" abc "),
                "Expected IllegalArgumentException for multi-character String with spaces");
    }

    // --- toChar(final String str, final char defaultValue) ---
    // @ensures str == null || str.length() != 1 ? \result == defaultValue : \result == str.charAt(0);
    @Test
    void testToChar_StringWithDefault_NormalBehavior() {
        assertEquals('a', CharUtils.toChar("a", 'x'));
        assertEquals('Z', CharUtils.toChar("Z", 'y'));
        assertEquals('0', CharUtils.toChar("0", 'z'));
    }

    @Test
    void testToChar_StringWithDefault_NullOrInvalidInput() {
        assertEquals('x', CharUtils.toChar(null, 'x'));
        assertEquals('y', CharUtils.toChar("", 'y'));
        assertEquals('z', CharUtils.toChar("ab", 'z'));
        assertEquals('d', CharUtils.toChar(" test ", 'd'));
        assertEquals('\0', CharUtils.toChar(null, '\0'));
    }

    // --- toCharacterObject(final char c) ---
    // @ensures \result.charValue() == c;
    @Test
    void testToCharacterObject_char_NormalBehavior() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject('a'));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject('Z'));
        assertEquals(Character.valueOf('0'), CharUtils.toCharacterObject('0'));
        assertEquals(Character.valueOf(' '), CharUtils.toCharacterObject(' '));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject('\0'));
        assertEquals(Character.valueOf('\uFFFF'), CharUtils.toCharacterObject('\uFFFF'));
    }

    // --- toCharacterObject(final String str) ---
    // @ensures str == null || str.length() != 1 ? \result == null : \result.charValue() == str.charAt(0);
    @Test
    void testToCharacterObject_String_NormalBehavior() {
        assertEquals(Character.valueOf('a'), CharUtils.toCharacterObject("a"));
        assertEquals(Character.valueOf('Z'), CharUtils.toCharacterObject("Z"));
        assertEquals(Character.valueOf('0'), CharUtils.toCharacterObject("0"));
        assertEquals(Character.valueOf(' '), CharUtils.toCharacterObject(" "));
        assertEquals(Character.valueOf('\0'), CharUtils.toCharacterObject("\0"));
    }

    @Test
    void testToCharacterObject_String_NullOrInvalidInput() {
        assertNull(CharUtils.toCharacterObject(null));
        assertNull(CharUtils.toCharacterObject(""));
        assertNull(CharUtils.toCharacterObject("ab"));
        assertNull(CharUtils.toCharacterObject(" abc "));
    }

    // --- toIntValue(final char ch) ---
    // @requires isAsciiNumeric(ch);
    // @ensures \result == (ch - '0');
    @Test
    void testToIntValue_char_NormalBehavior() {
        assertEquals(0, CharUtils.toIntValue('0'));
        assertEquals(1, CharUtils.toIntValue('1'));
        assertEquals(5, CharUtils.toIntValue('5'));
        assertEquals(9, CharUtils.toIntValue('9'));
    }

    @Test
    void testToIntValue_char_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('a'),
                "Expected IllegalArgumentException for non-numeric char 'a'");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(' '),
                "Expected IllegalArgumentException for non-numeric char ' '");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue('/'),
                "Expected IllegalArgumentException for char '/' (before '0')");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(':'),
                "Expected IllegalArgumentException for char ':' (after '9')");
    }

    // --- toIntValue(final char ch, final int defaultValue) ---
    // @ensures isAsciiNumeric(ch) ? \result == (ch - '0') : \result == defaultValue;
    @Test
    void testToIntValue_charWithDefault_NormalBehavior() {
        assertEquals(0, CharUtils.toIntValue('0', 99));
        assertEquals(5, CharUtils.toIntValue('5', 99));
        assertEquals(9, CharUtils.toIntValue('9', 99));
    }

    @Test
    void testToIntValue_charWithDefault_InvalidInput() {
        assertEquals(99, CharUtils.toIntValue('a', 99));
        assertEquals(-1, CharUtils.toIntValue(' ', -1));
        assertEquals(0, CharUtils.toIntValue('/', 0));
        assertEquals(10, CharUtils.toIntValue(':', 10));
    }

    // --- toIntValue(final Character ch) ---
    // @requires ch != null && isAsciiNumeric(ch.charValue());
    // @ensures \result == (ch.charValue() - '0');
    @Test
    void testToIntValue_Character_NormalBehavior() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0')));
        assertEquals(1, CharUtils.toIntValue(Character.valueOf('1')));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5')));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9')));
    }

    @Test
    void testToIntValue_Character_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(null),
                "Expected IllegalArgumentException for null Character input");
        assertThrows(IllegalArgumentException.class, () -> CharUtils.toIntValue(Character.valueOf('a')),
                "Expected IllegalArgumentException for non-numeric Character 'a'");
    }

    // --- toIntValue(final Character ch, final int defaultValue) ---
    // @ensures ch == null || !isAsciiNumeric(ch.charValue()) ? \result == defaultValue : \result == (ch.charValue() - '0');
    @Test
    void testToIntValue_CharacterWithDefault_NormalBehavior() {
        assertEquals(0, CharUtils.toIntValue(Character.valueOf('0'), 99));
        assertEquals(5, CharUtils.toIntValue(Character.valueOf('5'), 99));
        assertEquals(9, CharUtils.toIntValue(Character.valueOf('9'), 99));
    }

    @Test
    void testToIntValue_CharacterWithDefault_NullOrInvalidInput() {
        assertEquals(99, CharUtils.toIntValue(null, 99));
        assertEquals(-1, CharUtils.toIntValue(Character.valueOf('a'), -1));
        assertEquals(0, CharUtils.toIntValue(Character.valueOf(' '), 0));
    }

    // --- toString(final char ch) ---
    // @ensures \result.length() == 1 && \result.charAt(0) == ch;
    @Test
    void testToString_char_NormalBehavior() {
        assertEquals("a", CharUtils.toString('a'));
        assertEquals("Z", CharUtils.toString('Z'));
        assertEquals("0", CharUtils.toString('0'));
        assertEquals(" ", CharUtils.toString(' '));
        assertEquals("\0", CharUtils.toString('\0'));
        assertEquals("\uFFFF", CharUtils.toString('\uFFFF'));
    }

    // --- toString(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.length() == 1 && \result.charAt(0) == ch.charValue();
    @Test
    void testToString_Character_NormalBehavior() {
        assertEquals("a", CharUtils.toString(Character.valueOf('a')));
        assertEquals("Z", CharUtils.toString(Character.valueOf('Z')));
        assertEquals("0", CharUtils.toString(Character.valueOf('0')));
        assertEquals(" ", CharUtils.toString(Character.valueOf(' ')));
        assertEquals("\0", CharUtils.toString(Character.valueOf('\0')));
    }

    @Test
    void testToString_Character_NullInput() {
        assertNull(CharUtils.toString(null));
    }

    // --- unicodeEscaped(final char ch) ---
    // @ensures \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_char_NormalBehavior() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped('a'));
        assertEquals("\\u0041", CharUtils.unicodeEscaped('A'));
        assertEquals("\\u0030", CharUtils.unicodeEscaped('0'));
        assertEquals("\\u0020", CharUtils.unicodeEscaped(' '));
        assertEquals("\\u0000", CharUtils.unicodeEscaped('\0'));
        assertEquals("\\u007F", CharUtils.unicodeEscaped('\u007F')); // DEL
        assertEquals("\\u0080", CharUtils.unicodeEscaped('\u0080')); // First non-ASCII
        assertEquals("\\uFFFF", CharUtils.unicodeEscaped('\uFFFF')); // Max char value
        assertEquals("\\u00E9", CharUtils.unicodeEscaped('é'));
        assertEquals("\\u20AC", CharUtils.unicodeEscaped('€'));
    }

    // --- unicodeEscaped(final Character ch) ---
    // @ensures ch == null ? \result == null : \result.startsWith("\\u") && \result.length() == 6;
    @Test
    void testUnicodeEscaped_Character_NormalBehavior() {
        assertEquals("\\u0061", CharUtils.unicodeEscaped(Character.valueOf('a')));
        assertEquals("\\u0041", CharUtils.unicodeEscaped(Character.valueOf('A')));
        assertEquals("\\u0030", CharUtils.unicodeEscaped(Character.valueOf('0')));
        assertEquals("\\u0000", CharUtils.unicodeEscaped(Character.valueOf('\0')));
        assertEquals("\\uFFFF", CharUtils.unicodeEscaped(Character.valueOf('\uFFFF')));
    }

    @Test
    void testUnicodeEscaped_Character_NullInput() {
        assertNull(CharUtils.unicodeEscaped(null));
    }
}