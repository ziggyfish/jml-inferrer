package org.apache.commons.lang3.p3;

import org.apache.commons.lang3.BooleanUtils;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

public class BooleanUtilsTestP3P3 {

    // --- and(final boolean... array) ---
    @Test
    void testAndPrimitive_NormalCases() {
        assertTrue(BooleanUtils.and(true, true, true));
        assertFalse(BooleanUtils.and(true, false, true));
        assertFalse(BooleanUtils.and(false, false, false));
        assertTrue(BooleanUtils.and(true));
        assertFalse(BooleanUtils.and(false));
    }

    @Test
    void testAndPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.and((boolean[]) null)); // Null array
    }

    // --- and(final Boolean... array) ---
    @Test
    void testAndObject_NormalCases() {
        assertTrue(BooleanUtils.and(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.and(Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE));
    }

    @Test
    void testAndObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.and((Boolean[]) null)); // Null array
        assertThrows(NullPointerException.class, () -> BooleanUtils.and(Boolean.TRUE, null, Boolean.TRUE)); // Null element
    }

    // --- booleanValues() ---
    @Test
    void testBooleanValues() {
        Boolean[] expected = {Boolean.TRUE, Boolean.FALSE};
        assertArrayEquals(expected, BooleanUtils.booleanValues());
    }

    // --- compare(final boolean x, final boolean y) ---
    @ParameterizedTest
    @MethodSource("compareBooleanProvider")
    void testCompare(boolean x, boolean y, int expected) {
        assertEquals(expected, BooleanUtils.compare(x, y));
    }

    private static Stream<Arguments> compareBooleanProvider() {
        return Stream.of(
                Arguments.of(true, true, 0),
                Arguments.of(true, false, 1),
                Arguments.of(false, true, -1),
                Arguments.of(false, false, 0)
        );
    }

    // --- forEach(final Consumer<Boolean> action) ---
    @Test
    void testForEach_NormalCase() {
        List<Boolean> collected = new ArrayList<>();
        Consumer<Boolean> consumer = collected::add;
        BooleanUtils.forEach(consumer);
        assertEquals(Arrays.asList(Boolean.TRUE, Boolean.FALSE), collected);
    }

    @Test
    void testForEach_NullConsumer() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.forEach(null));
    }

    // --- isFalse(final Boolean bool) ---
    @Test
    void testIsFalse_NormalCases() {
        assertTrue(BooleanUtils.isFalse(Boolean.FALSE));
        assertFalse(BooleanUtils.isFalse(Boolean.TRUE));
    }

    @Test
    void testIsFalse_NullInput() {
        assertFalse(BooleanUtils.isFalse(null));
    }

    // --- isNotFalse(final Boolean bool) ---
    @Test
    void testIsNotFalse_NormalCases() {
        assertFalse(BooleanUtils.isNotFalse(Boolean.FALSE));
        assertTrue(BooleanUtils.isNotFalse(Boolean.TRUE));
    }

    @Test
    void testIsNotFalse_NullInput() {
        assertTrue(BooleanUtils.isNotFalse(null));
    }

    // --- isNotTrue(final Boolean bool) ---
    @Test
    void testIsNotTrue_NormalCases() {
        assertTrue(BooleanUtils.isNotTrue(Boolean.FALSE));
        assertFalse(BooleanUtils.isNotTrue(Boolean.TRUE));
    }

    @Test
    void testIsNotTrue_NullInput() {
        assertTrue(BooleanUtils.isNotTrue(null));
    }

    // --- isTrue(final Boolean bool) ---
    @Test
    void testIsTrue_NormalCases() {
        assertFalse(BooleanUtils.isTrue(Boolean.FALSE));
        assertTrue(BooleanUtils.isTrue(Boolean.TRUE));
    }

    @Test
    void testIsTrue_NullInput() {
        assertFalse(BooleanUtils.isTrue(null));
    }

    // --- negate(final Boolean bool) ---
    @Test
    void testNegate_NormalCases() {
        assertEquals(Boolean.FALSE, BooleanUtils.negate(Boolean.TRUE));
        assertEquals(Boolean.TRUE, BooleanUtils.negate(Boolean.FALSE));
    }

    @Test
    void testNegate_NullInput() {
        assertNull(BooleanUtils.negate(null));
    }

    // --- oneHot(final boolean... array) ---
    @Test
    void testOneHotPrimitive_NormalCases() {
        assertTrue(BooleanUtils.oneHot(true, false, false));
        assertTrue(BooleanUtils.oneHot(false, true, false));
        assertTrue(BooleanUtils.oneHot(false, false, true));
        assertFalse(BooleanUtils.oneHot(true, true, false));
        assertFalse(BooleanUtils.oneHot(false, false, false));
        assertFalse(BooleanUtils.oneHot(true, true, true));
        assertTrue(BooleanUtils.oneHot(true));
        assertFalse(BooleanUtils.oneHot(false));
    }

    @Test
    void testOneHotPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.oneHot((boolean[]) null)); // Null array
    }

    // --- oneHot(final Boolean... array) ---
    @Test
    void testOneHotObject_NormalCases() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.oneHot(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE));
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE));
    }

    @Test
    void testOneHotObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.oneHot((Boolean[]) null)); // Null array
        assertThrows(NullPointerException.class, () -> BooleanUtils.oneHot(Boolean.TRUE, null, Boolean.FALSE)); // Null element
    }

    // --- or(final boolean... array) ---
    @Test
    void testOrPrimitive_NormalCases() {
        assertTrue(BooleanUtils.or(true, true, true));
        assertTrue(BooleanUtils.or(true, false, true));
        assertFalse(BooleanUtils.or(false, false, false));
        assertTrue(BooleanUtils.or(true));
        assertFalse(BooleanUtils.or(false));
    }

    @Test
    void testOrPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.or((boolean[]) null)); // Null array
    }

    // --- or(final Boolean... array) ---
    @Test
    void testOrObject_NormalCases() {
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.or(Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE));
    }

    @Test
    void testOrObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.or((Boolean[]) null)); // Null array
        assertThrows(NullPointerException.class, () -> BooleanUtils.or(Boolean.FALSE, null, Boolean.FALSE)); // Null element
    }

    // --- primitiveValues() ---
    @Test
    void testPrimitiveValues() {
        boolean[] expected = {true, false};
        assertArrayEquals(expected, BooleanUtils.primitiveValues());
    }

    // --- toBoolean(final Boolean bool) ---
    @Test
    void testToBooleanFromBoolean_NormalCases() {
        assertTrue(BooleanUtils.toBoolean(Boolean.TRUE));
        assertFalse(BooleanUtils.toBoolean(Boolean.FALSE));
    }

    @Test
    void testToBooleanFromBoolean_NullInput() {
        assertFalse(BooleanUtils.toBoolean(null));
    }

    // --- toBoolean(final int value) ---
    @Test
    void testToBooleanFromInt_NormalCases() {
        assertTrue(BooleanUtils.toBoolean(1));
        assertFalse(BooleanUtils.toBoolean(0));
    }

    @Test
    void testToBooleanFromInt_OtherValues() {
        assertTrue(BooleanUtils.toBoolean(Integer.MAX_VALUE));
        assertFalse(BooleanUtils.toBoolean(Integer.MIN_VALUE));
        assertTrue(BooleanUtils.toBoolean(-1)); // Any non-zero is true
    }

    // --- toBoolean(final int value, final int trueValue, final int falseValue) ---
    @Test
    void testToBooleanFromIntWithValues_NormalCases() {
        assertTrue(BooleanUtils.toBoolean(5, 5, 10));
        assertFalse(BooleanUtils.toBoolean(10, 5, 10));
    }

    @Test
    void testToBooleanFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(0, 1, 1)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(0, 0, 0)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 2, 3)); // value not trueValue or falseValue
    }

    // --- toBoolean(final Integer value, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToBooleanFromIntegerWithValues_NormalCases() {
        assertTrue(BooleanUtils.toBoolean(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(10)));
        assertFalse(BooleanUtils.toBoolean(Integer.valueOf(10), Integer.valueOf(5), Integer.valueOf(10)));
    }

    @Test
    void testToBooleanFromIntegerWithValues_NullInputs() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, Integer.valueOf(5), Integer.valueOf(10)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(5), null, Integer.valueOf(10)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(5), Integer.valueOf(5), null));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, null, null));
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(1)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(1), Integer.valueOf(2), Integer.valueOf(3)));
    }

    // --- toBoolean(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "TRUE", "True", "on", "ON", "On", "yes", "YES", "Yes", "t", "T", "y", "Y", "1"})
    void testToBooleanFromString_TrueCases(String str) {
        assertTrue(BooleanUtils.toBoolean(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "FALSE", "False", "off", "OFF", "Off", "no", "NO", "No", "f", "F", "n", "N", "0", "", " ", "abc"})
    @NullSource
    void testToBooleanFromString_FalseCases(String str) {
        assertFalse(BooleanUtils.toBoolean(str));
    }

    // --- toBoolean(final String str, final String trueString, final String falseString) ---
    @Test
    void testToBooleanFromStringWithStrings_NormalCases() {
        assertTrue(BooleanUtils.toBoolean("ok", "ok", "notok"));
        assertFalse(BooleanUtils.toBoolean("notok", "ok", "notok"));
        assertTrue(BooleanUtils.toBoolean("OK", "ok", "notok")); // Case-insensitive trueString
        assertFalse(BooleanUtils.toBoolean("NOTOK", "ok", "notok")); // Case-insensitive falseString
    }

    @Test
    void testToBooleanFromStringWithStrings_NullInputs() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, "ok", "notok"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", null, "notok"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("notok", "ok", null));
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("test", "true", "true")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("test", "true", "false")); // value not trueString or falseString
    }

    // --- toBooleanDefaultIfNull(final Boolean bool, final boolean valueIfNull) ---
    @Test
    void testToBooleanDefaultIfNull_NormalCases() {
        assertTrue(BooleanUtils.toBooleanDefaultIfNull(Boolean.TRUE, false));
        assertFalse(BooleanUtils.toBooleanDefaultIfNull(Boolean.FALSE, true));
    }

    @Test
    void testToBooleanDefaultIfNull_NullInput() {
        assertTrue(BooleanUtils.toBooleanDefaultIfNull(null, true));
        assertFalse(BooleanUtils.toBooleanDefaultIfNull(null, false));
    }

    // --- toBooleanObject(final int value) ---
    @Test
    void testToBooleanObjectFromInt_NormalCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(1));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(0));
    }

    @Test
    void testToBooleanObjectFromInt_OtherValues() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.MAX_VALUE));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.MIN_VALUE));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(-1));
    }

    // --- toBooleanObject(final int value, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToBooleanObjectFromIntWithValues_NormalCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(5, 5, 10, 0));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(10, 5, 10, 0));
        assertNull(BooleanUtils.toBooleanObject(0, 5, 10, 0));
    }

    @Test
    void testToBooleanObjectFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(0, 1, 1, 2)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(0, 1, 2, 1)); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(0, 1, 2, 2)); // falseValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(15, 5, 10, 0)); // value not true, false, or null
    }

    // --- toBooleanObject(final Integer value) ---
    @Test
    void testToBooleanObjectFromInteger_NormalCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(1)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(0)));
    }

    @Test
    void testToBooleanObjectFromInteger_NullInput() {
        assertNull(BooleanUtils.toBooleanObject(null));
    }

    @Test
    void testToBooleanObjectFromInteger_OtherValues() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(Integer.MAX_VALUE)));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(Integer.MIN_VALUE)));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(-1)));
    }

    // --- toBooleanObject(final Integer value, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToBooleanObjectFromIntegerWithValues_NormalCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(10), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertNull(BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_NullInputs() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(null, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), null, Integer.valueOf(10), Integer.valueOf(0)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), null, Integer.valueOf(0)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(10), null));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(2)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(2), Integer.valueOf(1)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(2), Integer.valueOf(2)));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(15), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
    }

    // --- toBooleanObject(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "TRUE", "True", "on", "ON", "On", "yes", "YES", "Yes", "t", "T", "y", "Y", "1"})
    void testToBooleanObjectFromString_TrueCases(String str) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "FALSE", "False", "off", "OFF", "Off", "no", "NO", "No", "f", "F", "n", "N", "0"})
    void testToBooleanObjectFromString_FalseCases(String str) {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"", " ", "abc", "null"}) // "null" is not special here
    @NullSource
    void testToBooleanObjectFromString_NullCases(String str) {
        assertNull(BooleanUtils.toBooleanObject(str));
    }

    // --- toBooleanObject(final String str, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToBooleanObjectFromStringWithStrings_NormalCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("ok", "ok", "notok", "maybe"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("notok", "ok", "notok", "maybe"));
        assertNull(BooleanUtils.toBooleanObject("maybe", "ok", "notok", "maybe"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("OK", "ok", "notok", "maybe")); // Case-insensitive
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_NullInputs() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(null, "ok", "notok", "maybe"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", null, "notok", "maybe"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("notok", "ok", null, "maybe"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("maybe", "ok", "notok", null));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("test", "true", "true", "null"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("test", "true", "false", "true"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("test", "true", "false", "false"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("unknown", "true", "false", "null"));
    }

    // --- toInteger(final boolean bool) ---
    @Test
    void testToIntegerFromBoolean_NormalCases() {
        assertEquals(1, BooleanUtils.toInteger(true));
        assertEquals(0, BooleanUtils.toInteger(false));
    }

    // --- toInteger(final boolean bool, final int trueValue, final int falseValue) ---
    @Test
    void testToIntegerFromBooleanWithValues_NormalCases() {
        assertEquals(5, BooleanUtils.toInteger(true, 5, 10));
        assertEquals(10, BooleanUtils.toInteger(false, 5, 10));
    }

    // --- toInteger(final Boolean bool, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToIntegerFromBooleanObjectWithValues_NormalCases() {
        assertEquals(5, BooleanUtils.toInteger(Boolean.TRUE, 5, 10, 0));
        assertEquals(10, BooleanUtils.toInteger(Boolean.FALSE, 5, 10, 0));
        assertEquals(0, BooleanUtils.toInteger(null, 5, 10, 0));
    }

    // --- toIntegerObject(final boolean bool) ---
    @Test
    void testToIntegerObjectFromBoolean_NormalCases() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(true));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(false));
    }

    // --- toIntegerObject(final boolean bool, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToIntegerObjectFromBooleanWithValues_NormalCases() {
        assertEquals(Integer.valueOf(5), BooleanUtils.toIntegerObject(true, Integer.valueOf(5), Integer.valueOf(10)));
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(false, Integer.valueOf(5), Integer.valueOf(10)));
    }

    @Test
    void testToIntegerObjectFromBooleanWithValues_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(true, null, Integer.valueOf(10)));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(false, Integer.valueOf(5), null));
    }

    // --- toIntegerObject(final Boolean bool) ---
    @Test
    void testToIntegerObjectFromBooleanObject_NormalCases() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(Boolean.TRUE));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(Boolean.FALSE));
    }

    @Test
    void testToIntegerObjectFromBooleanObject_NullInput() {
        assertNull(BooleanUtils.toIntegerObject(null));
    }

    // --- toIntegerObject(final Boolean bool, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_NormalCases() {
        assertEquals(Integer.valueOf(5), BooleanUtils.toIntegerObject(Boolean.TRUE, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(null, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
    }

    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(Boolean.TRUE, null, Integer.valueOf(10), Integer.valueOf(0)));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(5), null, Integer.valueOf(0)));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(null, Integer.valueOf(5), Integer.valueOf(10), null));
    }

    // --- toString(final boolean bool, final String trueString, final String falseString) ---
    @Test
    void testToStringFromBooleanWithStrings_NormalCases() {
        assertEquals("yes", BooleanUtils.toString(true, "yes", "no"));
        assertEquals("no", BooleanUtils.toString(false, "yes", "no"));
    }

    @Test
    void testToStringFromBooleanWithStrings_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(true, null, "no"));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(false, "yes", null));
    }

    // --- toString(final Boolean bool, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToStringFromBooleanObjectWithStrings_NormalCases() {
        assertEquals("yes", BooleanUtils.toString(Boolean.TRUE, "yes", "no", "maybe"));
        assertEquals("no", BooleanUtils.toString(Boolean.FALSE, "yes", "no", "maybe"));
        assertEquals("maybe", BooleanUtils.toString(null, "yes", "no", "maybe"));
    }

    @Test
    void testToStringFromBooleanObjectWithStrings_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(Boolean.TRUE, null, "no", "maybe"));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(Boolean.FALSE, "yes", null, "maybe"));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(null, "yes", "no", null));
    }

    // --- toStringOnOff(final boolean bool) ---
    @Test
    void testToStringOnOffFromBoolean_NormalCases() {
        assertEquals("on", BooleanUtils.toStringOnOff(true));
        assertEquals("off", BooleanUtils.toStringOnOff(false));
    }

    // --- toStringOnOff(final Boolean bool) ---
    @Test
    void testToStringOnOffFromBooleanObject_NormalCases() {
        assertEquals("on", BooleanUtils.toStringOnOff(Boolean.TRUE));
        assertEquals("off", BooleanUtils.toStringOnOff(Boolean.FALSE));
    }

    @Test
    void testToStringOnOffFromBooleanObject_NullInput() {
        assertNull(BooleanUtils.toStringOnOff(null));
    }

    // --- toStringTrueFalse(final boolean bool) ---
    @Test
    void testToStringTrueFalseFromBoolean_NormalCases() {
        assertEquals("true", BooleanUtils.toStringTrueFalse(true));
        assertEquals("false", BooleanUtils.toStringTrueFalse(false));
    }

    // --- toStringTrueFalse(final Boolean bool) ---
    @Test
    void testToStringTrueFalseFromBooleanObject_NormalCases() {
        assertEquals("true", BooleanUtils.toStringTrueFalse(Boolean.TRUE));
        assertEquals("false", BooleanUtils.toStringTrueFalse(Boolean.FALSE));
    }

    @Test
    void testToStringTrueFalseFromBooleanObject_NullInput() {
        assertNull(BooleanUtils.toStringTrueFalse(null));
    }

    // --- toStringYesNo(final boolean bool) ---
    @Test
    void testToStringYesNoFromBoolean_NormalCases() {
        assertEquals("yes", BooleanUtils.toStringYesNo(true));
        assertEquals("no", BooleanUtils.toStringYesNo(false));
    }

    // --- toStringYesNo(final Boolean bool) ---
    @Test
    void testToStringYesNoFromBooleanObject_NormalCases() {
        assertEquals("yes", BooleanUtils.toStringYesNo(Boolean.TRUE));
        assertEquals("no", BooleanUtils.toStringYesNo(Boolean.FALSE));
    }

    @Test
    void testToStringYesNoFromBooleanObject_NullInput() {
        assertNull(BooleanUtils.toStringYesNo(null));
    }

    // --- values() ---
    @Test
    void testValues() {
        List<Boolean> expected = Arrays.asList(Boolean.TRUE, Boolean.FALSE);
        assertEquals(expected, BooleanUtils.values());
    }

    // --- xor(final boolean... array) ---
    @Test
    void testXorPrimitive_NormalCases() {
        assertFalse(BooleanUtils.xor(true, true));
        assertTrue(BooleanUtils.xor(true, false));
        assertTrue(BooleanUtils.xor(false, true));
        assertFalse(BooleanUtils.xor(false, false));

        assertTrue(BooleanUtils.xor(true, false, false));
        assertFalse(BooleanUtils.xor(true, true, false));
        assertFalse(BooleanUtils.xor(true, true, true));
        assertTrue(BooleanUtils.xor(true));
        assertFalse(BooleanUtils.xor(false));
    }

    @Test
    void testXorPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.xor((boolean[]) null)); // Null array
    }

    // --- xor(final Boolean... array) ---
    @Test
    void testXorObject_NormalCases() {
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE));
        assertTrue(BooleanUtils.xor(Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.xor(Boolean.FALSE, Boolean.FALSE));

        assertTrue(BooleanUtils.xor(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.TRUE));
        assertFalse(BooleanUtils.xor(Boolean.FALSE));
    }

    @Test
    void testXorObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.xor((Boolean[]) null)); // Null array
        assertThrows(NullPointerException.class, () -> BooleanUtils.xor(Boolean.TRUE, null, Boolean.FALSE)); // Null element
    }
}