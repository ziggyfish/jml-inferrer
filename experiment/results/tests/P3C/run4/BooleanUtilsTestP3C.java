package org.apache.commons.lang3.p3c;

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

class BooleanUtilsTestP3CP3C {

    // --- and(final boolean... array) ---
    @Test
    void testAndPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.and(true, true, true));
        assertFalse(BooleanUtils.and(true, false, true));
        assertFalse(BooleanUtils.and(false, false, false));
    }

    @Test
    void testAndPrimitive_EdgeCases() {
        assertTrue(BooleanUtils.and(true)); // Single true
        assertFalse(BooleanUtils.and(false)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and()); // Empty array
    }

    // --- and(final Boolean... array) ---
    @Test
    void testAndObject_NormalBehavior() {
        assertTrue(BooleanUtils.and(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testAndObject_EdgeCases() {
        assertTrue(BooleanUtils.and(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.and(Boolean.FALSE)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and((Boolean[]) null)); // Null array
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and()); // Empty array
    }

    @Test
    void testAndObject_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and(Boolean.TRUE, null, Boolean.TRUE)); // Null element
    }

    // --- booleanValues() ---
    @Test
    void testBooleanValues() {
        Boolean[] expected = {Boolean.FALSE, Boolean.TRUE};
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
                Arguments.of(false, false, 0),
                Arguments.of(true, false, 1),
                Arguments.of(false, true, -1)
        );
    }

    // --- forEach(final Consumer<Boolean> action) ---
    @Test
    void testForEach_NormalBehavior() {
        List<Boolean> consumed = new ArrayList<>();
        Consumer<Boolean> consumer = consumed::add;
        BooleanUtils.forEach(consumer);
        assertEquals(Arrays.asList(Boolean.FALSE, Boolean.TRUE), consumed);
    }

    @Test
    void testForEach_FailureScenarios() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.forEach(null)); // Null consumer
    }

    // --- isFalse(final Boolean bool) ---
    @Test
    void testIsFalse_NormalBehavior() {
        assertTrue(BooleanUtils.isFalse(Boolean.FALSE));
        assertFalse(BooleanUtils.isFalse(Boolean.TRUE));
    }

    @Test
    void testIsFalse_EdgeCases() {
        assertFalse(BooleanUtils.isFalse(null));
    }

    // --- isNotFalse(final Boolean bool) ---
    @Test
    void testIsNotFalse_NormalBehavior() {
        assertFalse(BooleanUtils.isNotFalse(Boolean.FALSE));
        assertTrue(BooleanUtils.isNotFalse(Boolean.TRUE));
    }

    @Test
    void testIsNotFalse_EdgeCases() {
        assertTrue(BooleanUtils.isNotFalse(null));
    }

    // --- isNotTrue(final Boolean bool) ---
    @Test
    void testIsNotTrue_NormalBehavior() {
        assertTrue(BooleanUtils.isNotTrue(Boolean.FALSE));
        assertFalse(BooleanUtils.isNotTrue(Boolean.TRUE));
    }

    @Test
    void testIsNotTrue_EdgeCases() {
        assertTrue(BooleanUtils.isNotTrue(null));
    }

    // --- isTrue(final Boolean bool) ---
    @Test
    void testIsTrue_NormalBehavior() {
        assertFalse(BooleanUtils.isTrue(Boolean.FALSE));
        assertTrue(BooleanUtils.isTrue(Boolean.TRUE));
    }

    @Test
    void testIsTrue_EdgeCases() {
        assertFalse(BooleanUtils.isTrue(null));
    }

    // --- negate(final Boolean bool) ---
    @Test
    void testNegate_NormalBehavior() {
        assertEquals(Boolean.FALSE, BooleanUtils.negate(Boolean.TRUE));
        assertEquals(Boolean.TRUE, BooleanUtils.negate(Boolean.FALSE));
    }

    @Test
    void testNegate_EdgeCases() {
        assertNull(BooleanUtils.negate(null));
    }

    // --- oneHot(final boolean... array) ---
    @Test
    void testOneHotPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.oneHot(true, false, false));
        assertTrue(BooleanUtils.oneHot(false, true, false));
        assertTrue(BooleanUtils.oneHot(false, false, true));
    }

    @Test
    void testOneHotPrimitive_FailureScenarios() {
        assertFalse(BooleanUtils.oneHot(true, true, false)); // More than one true
        assertFalse(BooleanUtils.oneHot(false, false, false)); // No true
    }

    @Test
    void testOneHotPrimitive_EdgeCases() {
        assertTrue(BooleanUtils.oneHot(true)); // Single true
        assertFalse(BooleanUtils.oneHot(false)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot()); // Empty array
    }

    // --- oneHot(final Boolean... array) ---
    @Test
    void testOneHotObject_NormalBehavior() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.TRUE));
    }

    @Test
    void testOneHotObject_FailureScenarios() {
        assertFalse(BooleanUtils.oneHot(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE)); // More than one true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE)); // No true
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot(Boolean.TRUE, null, Boolean.FALSE)); // Null element
    }

    @Test
    void testOneHotObject_EdgeCases() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot((Boolean[]) null)); // Null array
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot()); // Empty array
    }

    // --- or(final boolean... array) ---
    @Test
    void testOrPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.or(true, true, true));
        assertTrue(BooleanUtils.or(true, false, true));
        assertFalse(BooleanUtils.or(false, false, false));
    }

    @Test
    void testOrPrimitive_EdgeCases() {
        assertTrue(BooleanUtils.or(true)); // Single true
        assertFalse(BooleanUtils.or(false)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or()); // Empty array
    }

    // --- or(final Boolean... array) ---
    @Test
    void testOrObject_NormalBehavior() {
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testOrObject_EdgeCases() {
        assertTrue(BooleanUtils.or(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.or(Boolean.FALSE)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or((Boolean[]) null)); // Null array
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or()); // Empty array
    }

    @Test
    void testOrObject_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or(Boolean.FALSE, null, Boolean.FALSE)); // Null element
    }

    // --- primitiveValues() ---
    @Test
    void testPrimitiveValues() {
        boolean[] expected = {false, true};
        assertArrayEquals(expected, BooleanUtils.primitiveValues());
    }

    // --- toBoolean(final Boolean bool) ---
    @Test
    void testToBooleanFromBoolean_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean(Boolean.TRUE));
        assertFalse(BooleanUtils.toBoolean(Boolean.FALSE));
    }

    @Test
    void testToBooleanFromBoolean_EdgeCases() {
        assertFalse(BooleanUtils.toBoolean(null));
    }

    // --- toBoolean(final int value) ---
    @ParameterizedTest
    @ValueSource(ints = {1, 5, -10})
    void testToBooleanFromInt_True(int value) {
        assertTrue(BooleanUtils.toBoolean(value));
    }

    @ParameterizedTest
    @ValueSource(ints = {0})
    void testToBooleanFromInt_False(int value) {
        assertFalse(BooleanUtils.toBoolean(value));
    }

    // --- toBoolean(final int value, final int trueValue, final int falseValue) ---
    @Test
    void testToBooleanFromIntWithValues_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean(1, 1, 0));
        assertFalse(BooleanUtils.toBoolean(0, 1, 0));
    }

    @Test
    void testToBooleanFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(2, 1, 0)); // Value not trueValue or falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 1, 1)); // trueValue == falseValue
    }

    // --- toBoolean(final Integer value, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToBooleanFromIntegerWithValues_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean(Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(0)));
        assertFalse(BooleanUtils.toBoolean(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(0)));
    }

    @Test
    void testToBooleanFromIntegerWithValues_EdgeCases() {
        assertFalse(BooleanUtils.toBoolean(null, Integer.valueOf(1), Integer.valueOf(0))); // Null value
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(2), Integer.valueOf(1), Integer.valueOf(0))); // Value not trueValue or falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(1))); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(1), null, Integer.valueOf(0))); // Null trueValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(1), Integer.valueOf(1), null)); // Null falseValue
    }

    // --- toBoolean(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "TRUE", "on", "ON", "yes", "YES", "y", "Y", "t", "T"})
    void testToBooleanFromString_True(String str) {
        assertTrue(BooleanUtils.toBoolean(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "FALSE", "off", "OFF", "no", "NO", "n", "N", "f", "F", "someOtherString", ""})
    @NullSource
    void testToBooleanFromString_False(String str) {
        assertFalse(BooleanUtils.toBoolean(str));
    }

    // --- toBoolean(final String str, final String trueString, final String falseString) ---
    @Test
    void testToBooleanFromStringWithStrings_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean("ok", "ok", "not_ok"));
        assertFalse(BooleanUtils.toBoolean("not_ok", "ok", "not_ok"));
    }

    @Test
    void testToBooleanFromStringWithStrings_EdgeCases() {
        assertFalse(BooleanUtils.toBoolean(null, "ok", "not_ok")); // Null str
        assertFalse(BooleanUtils.toBoolean("some_other", "ok", "not_ok")); // str not matching
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", "ok", "ok")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", null, "not_ok")); // Null trueString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", "ok", null)); // Null falseString
    }

    // --- toBooleanDefaultIfNull(final Boolean bool, final boolean valueIfNull) ---
    @Test
    void testToBooleanDefaultIfNull_NormalBehavior() {
        assertTrue(BooleanUtils.toBooleanDefaultIfNull(Boolean.TRUE, false));
        assertFalse(BooleanUtils.toBooleanDefaultIfNull(Boolean.FALSE, true));
    }

    @Test
    void testToBooleanDefaultIfNull_EdgeCases() {
        assertTrue(BooleanUtils.toBooleanDefaultIfNull(null, true));
        assertFalse(BooleanUtils.toBooleanDefaultIfNull(null, false));
    }

    // --- toBooleanObject(final int value) ---
    @ParameterizedTest
    @ValueSource(ints = {1, 5, -10})
    void testToBooleanObjectFromInt_True(int value) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(value));
    }

    @ParameterizedTest
    @ValueSource(ints = {0})
    void testToBooleanObjectFromInt_False(int value) {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(value));
    }

    // --- toBooleanObject(final int value, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToBooleanObjectFromIntWithValues_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(1, 1, 0, -1));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(0, 1, 0, -1));
        assertNull(BooleanUtils.toBooleanObject(-1, 1, 0, -1));
    }

    @Test
    void testToBooleanObjectFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(2, 1, 0, -1)); // Value not matching
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 1, -1)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 0, 1)); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(0, 1, 0, 0)); // falseValue == nullValue
    }

    // --- toBooleanObject(final Integer value) ---
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromIntegerProvider")
    void testToBooleanObjectFromInteger(Integer value, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(value));
    }

    private static Stream<Arguments> toBooleanObjectFromIntegerProvider() {
        return Stream.of(
                Arguments.of(Integer.valueOf(1), Boolean.TRUE),
                Arguments.of(Integer.valueOf(5), Boolean.TRUE),
                Arguments.of(Integer.valueOf(-10), Boolean.TRUE),
                Arguments.of(Integer.valueOf(0), Boolean.FALSE),
                Arguments.of(null, Boolean.FALSE) // JML says "if value is null, returns Boolean.FALSE"
        );
    }

    // --- toBooleanObject(final Integer value, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToBooleanObjectFromIntegerWithValues_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(0), Integer.valueOf(-1)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(0), Integer.valueOf(-1)));
        assertNull(BooleanUtils.toBooleanObject(Integer.valueOf(-1), Integer.valueOf(1), Integer.valueOf(0), Integer.valueOf(-1)));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_EdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(null, Integer.valueOf(1), Integer.valueOf(0), null)); // Value is null, nullValue is null
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(null, null, Integer.valueOf(0), null)); // Value is null, trueValue is null, nullValue is null
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(2), Integer.valueOf(1), Integer.valueOf(0), Integer.valueOf(-1))); // Value not matching
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(-1))); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(1), Integer.valueOf(1), Integer.valueOf(0), Integer.valueOf(1))); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(1), Integer.valueOf(0), Integer.valueOf(0))); // falseValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(1), null, Integer.valueOf(0), Integer.valueOf(-1))); // Null trueValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(1), Integer.valueOf(1), null, Integer.valueOf(-1))); // Null falseValue
    }

    // --- toBooleanObject(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "TRUE", "on", "ON", "yes", "YES"})
    void testToBooleanObjectFromString_True(String str) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "FALSE", "off", "OFF", "no", "NO"})
    void testToBooleanObjectFromString_False(String str) {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"someOtherString", "", "y", "Y", "t", "T", "f", "F", "n", "N"})
    @NullSource
    void testToBooleanObjectFromString_Null(String str) {
        assertNull(BooleanUtils.toBooleanObject(str));
    }

    // --- toBooleanObject(final String str, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToBooleanObjectFromStringWithStrings_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("ok", "ok", "not_ok", "maybe"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("not_ok", "ok", "not_ok", "maybe"));
        assertNull(BooleanUtils.toBooleanObject("maybe", "ok", "not_ok", "maybe"));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_EdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(null, "ok", "not_ok", null)); // str is null, nullString is null
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(null, null, "not_ok", null)); // str is null, trueString is null, nullString is null
        assertNull(BooleanUtils.toBooleanObject("some_other", "ok", "not_ok", "maybe")); // str not matching
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", "ok", "ok", "maybe")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", "ok", "not_ok", "ok")); // trueString == nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("not_ok", "ok", "not_ok", "not_ok")); // falseString == nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", null, "not_ok", "maybe")); // Null trueString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", "ok", null, "maybe")); // Null falseString
    }

    // --- toInteger(final boolean bool) ---
    @Test
    void testToIntegerFromBoolean_NormalBehavior() {
        assertEquals(1, BooleanUtils.toInteger(true));
        assertEquals(0, BooleanUtils.toInteger(false));
    }

    // --- toInteger(final boolean bool, final int trueValue, final int falseValue) ---
    @Test
    void testToIntegerFromBooleanWithValues_NormalBehavior() {
        assertEquals(10, BooleanUtils.toInteger(true, 10, 20));
        assertEquals(20, BooleanUtils.toInteger(false, 10, 20));
    }

    // --- toInteger(final Boolean bool, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToIntegerFromBooleanObjectWithValues_NormalBehavior() {
        assertEquals(10, BooleanUtils.toInteger(Boolean.TRUE, 10, 20, 30));
        assertEquals(20, BooleanUtils.toInteger(Boolean.FALSE, 10, 20, 30));
        assertEquals(30, BooleanUtils.toInteger(null, 10, 20, 30));
    }

    // --- toIntegerObject(final boolean bool) ---
    @Test
    void testToIntegerObjectFromBoolean_NormalBehavior() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(true));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(false));
    }

    // --- toIntegerObject(final boolean bool, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToIntegerObjectFromBooleanWithValues_NormalBehavior() {
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(true, Integer.valueOf(10), Integer.valueOf(20)));
        assertEquals(Integer.valueOf(20), BooleanUtils.toIntegerObject(false, Integer.valueOf(10), Integer.valueOf(20)));
    }

    @Test
    void testToIntegerObjectFromBooleanWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(true, null, Integer.valueOf(20))); // Null trueValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(false, Integer.valueOf(10), null)); // Null falseValue
    }

    // --- toIntegerObject(final Boolean bool) ---
    @Test
    void testToIntegerObjectFromBooleanObject_NormalBehavior() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(Boolean.TRUE));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(Boolean.FALSE));
    }

    @Test
    void testToIntegerObjectFromBooleanObject_EdgeCases() {
        assertNull(BooleanUtils.toIntegerObject(null));
    }

    // --- toIntegerObject(final Boolean bool, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_NormalBehavior() {
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(Boolean.TRUE, Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertEquals(Integer.valueOf(20), BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertEquals(Integer.valueOf(30), BooleanUtils.toIntegerObject(null, Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
    }

    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(Boolean.TRUE, null, Integer.valueOf(20), Integer.valueOf(30))); // Null trueValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(10), null, Integer.valueOf(30))); // Null falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(null, Integer.valueOf(10), Integer.valueOf(20), null)); // Null nullValue
    }

    // --- toString(final boolean bool, final String trueString, final String falseString) ---
    @Test
    void testToStringFromBooleanWithStrings_NormalBehavior() {
        assertEquals("yes", BooleanUtils.toString(true, "yes", "no"));
        assertEquals("no", BooleanUtils.toString(false, "yes", "no"));
    }

    @Test
    void testToStringFromBooleanWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(true, null, "no")); // Null trueString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(false, "yes", null)); // Null falseString
    }

    // --- toString(final Boolean bool, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToStringFromBooleanObjectWithStrings_NormalBehavior() {
        assertEquals("yes", BooleanUtils.toString(Boolean.TRUE, "yes", "no", "maybe"));
        assertEquals("no", BooleanUtils.toString(Boolean.FALSE, "yes", "no", "maybe"));
        assertEquals("maybe", BooleanUtils.toString(null, "yes", "no", "maybe"));
    }

    @Test
    void testToStringFromBooleanObjectWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(Boolean.TRUE, null, "no", "maybe")); // Null trueString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(Boolean.FALSE, "yes", null, "maybe")); // Null falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(null, "yes", "no", null)); // Null nullString
    }

    // --- toStringOnOff(final boolean bool) ---
    @Test
    void testToStringOnOffFromBoolean_NormalBehavior() {
        assertEquals("on", BooleanUtils.toStringOnOff(true));
        assertEquals("off", BooleanUtils.toStringOnOff(false));
    }

    // --- toStringOnOff(final Boolean bool) ---
    @Test
    void testToStringOnOffFromBooleanObject_NormalBehavior() {
        assertEquals("on", BooleanUtils.toStringOnOff(Boolean.TRUE));
        assertEquals("off", BooleanUtils.toStringOnOff(Boolean.FALSE));
    }

    @Test
    void testToStringOnOffFromBooleanObject_EdgeCases() {
        assertNull(BooleanUtils.toStringOnOff(null));
    }

    // --- toStringTrueFalse(final boolean bool) ---
    @Test
    void testToStringTrueFalseFromBoolean_NormalBehavior() {
        assertEquals("true", BooleanUtils.toStringTrueFalse(true));
        assertEquals("false", BooleanUtils.toStringTrueFalse(false));
    }

    // --- toStringTrueFalse(final Boolean bool) ---
    @Test
    void testToStringTrueFalseFromBooleanObject_NormalBehavior() {
        assertEquals("true", BooleanUtils.toStringTrueFalse(Boolean.TRUE));
        assertEquals("false", BooleanUtils.toStringTrueFalse(Boolean.FALSE));
    }

    @Test
    void testToStringTrueFalseFromBooleanObject_EdgeCases() {
        assertNull(BooleanUtils.toStringTrueFalse(null));
    }

    // --- toStringYesNo(final boolean bool) ---
    @Test
    void testToStringYesNoFromBoolean_NormalBehavior() {
        assertEquals("yes", BooleanUtils.toStringYesNo(true));
        assertEquals("no", BooleanUtils.toStringYesNo(false));
    }

    // --- toStringYesNo(final Boolean bool) ---
    @Test
    void testToStringYesNoFromBooleanObject_NormalBehavior() {
        assertEquals("yes", BooleanUtils.toStringYesNo(Boolean.TRUE));
        assertEquals("no", BooleanUtils.toStringYesNo(Boolean.FALSE));
    }

    @Test
    void testToStringYesNoFromBooleanObject_EdgeCases() {
        assertNull(BooleanUtils.toStringYesNo(null));
    }

    // --- values() ---
    @Test
    void testValues() {
        List<Boolean> expected = Arrays.asList(Boolean.FALSE, Boolean.TRUE);
        assertEquals(expected, BooleanUtils.values());
    }

    // --- xor(final boolean... array) ---
    @Test
    void testXorPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.xor(true, false, false));
        assertTrue(BooleanUtils.xor(false, true, false));
        assertFalse(BooleanUtils.xor(false, false, false));
    }

    @Test
    void testXorPrimitive_FailureScenarios() {
        assertFalse(BooleanUtils.xor(true, true, false)); // More than one true
        assertFalse(BooleanUtils.xor(true, true, true)); // Odd number of true (3)
    }

    @Test
    void testXorPrimitive_EdgeCases() {
        assertTrue(BooleanUtils.xor(true)); // Single true
        assertFalse(BooleanUtils.xor(false)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor()); // Empty array
    }

    // --- xor(final Boolean... array) ---
    @Test
    void testXorObject_NormalBehavior() {
        assertTrue(BooleanUtils.xor(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.xor(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testXorObject_FailureScenarios() {
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE)); // More than one true
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE)); // Odd number of true (3)
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor(Boolean.TRUE, null, Boolean.FALSE)); // Null element
    }

    @Test
    void testXorObject_EdgeCases() {
        assertTrue(BooleanUtils.xor(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.xor(Boolean.FALSE)); // Single false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor((Boolean[]) null)); // Null array
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor()); // Empty array
    }
}