```java
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
        assertTrue(BooleanUtils.isTrue(Boolean.TRUE));
        assertFalse(BooleanUtils.isTrue(Boolean.FALSE));
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
    }

    @Test
    void testOneHotPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.oneHot((boolean[]) null)); // Null array
        assertTrue(BooleanUtils.oneHot(true)); // Single true
        assertFalse(BooleanUtils.oneHot(false)); // Single false
    }

    // --- oneHot(final Boolean... array) ---
    @Test
    void testOneHotObject_NormalCases() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.oneHot(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testOneHotObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot()); // Empty array
        assertThrows(NullPointerException.class, () -> BooleanUtils.oneHot((Boolean[]) null)); // Null array
        assertThrows(NullPointerException.class, () -> BooleanUtils.oneHot(Boolean.TRUE, null, Boolean.FALSE)); // Null element
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE)); // Single false
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
        assertFalse(BooleanUtils.toBoolean(Integer.MIN_VALUE)); // JML implies only 0 is false
        assertTrue(BooleanUtils.toBoolean(-1));
    }

    // --- toBoolean(final int value, final int trueValue, final int falseValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromIntWithValuesProvider")
    void testToBooleanFromIntWithValues_NormalCases(int value, int trueValue, int falseValue, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(value, trueValue, falseValue));
    }

    private static Stream<Arguments> toBooleanFromIntWithValuesProvider() {
        return Stream.of(
                Arguments.of(1, 1, 0, true),
                Arguments.of(0, 1, 0, false),
                Arguments.of(5, 5, 10, true),
                Arguments.of(10, 5, 10, false),
                Arguments.of(-1, -1, -2, true),
                Arguments.of(-2, -1, -2, false)
        );
    }

    @Test
    void testToBooleanFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 2, 3)); // Value not trueValue or falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 1, 1)); // trueValue == falseValue
    }

    // --- toBoolean(final Integer value, final Integer trueValue, final Integer falseValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromIntegerWithValuesProvider")
    void testToBooleanFromIntegerWithValues_NormalCases(Integer value, Integer trueValue, Integer falseValue, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(value, trueValue, falseValue));
    }

    private static Stream<Arguments> toBooleanFromIntegerWithValuesProvider() {
        return Stream.of(
                Arguments.of(1, 1, 0, true),
                Arguments.of(0, 1, 0, false),
                Arguments.of(5, 5, 10, true),
                Arguments.of(10, 5, 10, false),
                Arguments.of(-1, -1, -2, true),
                Arguments.of(-2, -1, -2, false)
        );
    }

    @Test
    void testToBooleanFromIntegerWithValues_NullInputs() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, 1, 0)); // value is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, null, 0)); // trueValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 1, null)); // falseValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, null, null));
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 2, 3)); // Value not trueValue or falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 1, 1)); // trueValue == falseValue
    }

    // --- toBoolean(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "True", "TRUE", "on", "On", "ON", "yes", "Yes", "YES"})
    void testToBooleanFromString_TrueStrings(String str) {
        assertTrue(BooleanUtils.toBoolean(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "False", "FALSE", "off", "Off", "OFF", "no", "No", "NO", "", "abc", "1", "0"})
    @NullSource
    void testToBooleanFromString_FalseStrings(String str) {
        assertFalse(BooleanUtils.toBoolean(str));
    }

    // --- toBoolean(final String str, final String trueString, final String falseString) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromStringWithStringsProvider")
    void testToBooleanFromStringWithStrings_NormalCases(String str, String trueString, String falseString, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(str, trueString, falseString));
    }

    private static Stream<Arguments> toBooleanFromStringWithStringsProvider() {
        return Stream.of(
                Arguments.of("y", "y", "n", true),
                Arguments.of("n", "y", "n", false),
                Arguments.of("yes", "yes", "no", true),
                Arguments.of("no", "yes", "no", false),
                Arguments.of(null, "y", "n", false), // JML says if str is null, it's false
                Arguments.of("Y", "y", "n", false), // Case sensitive
                Arguments.of("y", "Y", "n", false) // Case sensitive
        );
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("x", "y", "n")); // str not trueString or falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("y", "y", "y")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("y", null, "n")); // trueString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("n", "y", null)); // falseString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("y", null, null));
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
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromIntWithValuesProvider")
    void testToBooleanObjectFromIntWithValues_NormalCases(int value, int trueValue, int falseValue, int nullValue, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(value, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toBooleanObjectFromIntWithValuesProvider() {
        return Stream.of(
                Arguments.of(1, 1, 0, 2, Boolean.TRUE),
                Arguments.of(0, 1, 0, 2, Boolean.FALSE),
                Arguments.of(2, 1, 0, 2, null),
                Arguments.of(5, 5, 10, 15, Boolean.TRUE),
                Arguments.of(10, 5, 10, 15, Boolean.FALSE),
                Arguments.of(15, 5, 10, 15, null)
        );
    }

    @Test
    void testToBooleanObjectFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 2, 3, 4)); // Value not true/false/null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 1, 2)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 2, 1)); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 2, 1, 1)); // falseValue == nullValue
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
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.MAX_VALUE));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.MIN_VALUE));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(-1));
    }

    // --- toBooleanObject(final Integer value, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromIntegerWithValuesProvider")
    void testToBooleanObjectFromIntegerWithValues_NormalCases(Integer value, Integer trueValue, Integer falseValue, Integer nullValue, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(value, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toBooleanObjectFromIntegerWithValuesProvider() {
        return Stream.of(
                Arguments.of(1, 1, 0, 2, Boolean.TRUE),
                Arguments.of(0, 1, 0, 2, Boolean.FALSE),
                Arguments.of(2, 1, 0, 2, null),
                Arguments.of(null, 1, 0, null, null), // value is null, nullValue is null
                Arguments.of(5, 5, 10, 15, Boolean.TRUE),
                Arguments.of(10, 5, 10, 15, Boolean.FALSE),
                Arguments.of(15, 5, 10, 15, null)
        );
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 2, 3, 4)); // Value not true/false/null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 1, 2)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 2, 1)); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 2, 1, 1)); // falseValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, null, 2, 3)); // trueValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 2, null, 3)); // falseValue is null
    }

    // --- toBooleanObject(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "True", "TRUE", "on", "On", "ON", "yes", "Yes", "YES"})
    void testToBooleanObjectFromString_TrueStrings(String str) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "False", "FALSE", "off", "Off", "OFF", "no", "No", "NO"})
    void testToBooleanObjectFromString_FalseStrings(String str) {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"", "abc", "1", "0", "null"}) // "null" is not a special case for this method
    @NullSource
    void testToBooleanObjectFromString_NullStrings(String str) {
        assertNull(BooleanUtils.toBooleanObject(str));
    }

    // --- toBooleanObject(final String str, final String trueString, final String falseString, final String nullString) ---
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromStringWithStringsProvider")
    void testToBooleanObjectFromStringWithStrings_NormalCases(String str, String trueString, String falseString, String nullString, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(str, trueString, falseString, nullString));
    }

    private static Stream<Arguments> toBooleanObjectFromStringWithStringsProvider() {
        return Stream.of(
                Arguments.of("y", "y", "n", "u", Boolean.TRUE),
                Arguments.of("n", "y", "n", "u", Boolean.FALSE),
                Arguments.of("u", "y", "n", "u", null),
                Arguments.of(null, "y", "n", null, null), // str is null, nullString is null
                Arguments.of("Y", "y", "n", "u", null), // Case sensitive
                Arguments.of("y", "Y", "n", "u", null) // Case sensitive
        );
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("x", "y", "n", "u")); // str not true/false/null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("y", "y", "y", "u")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("y", "y", "n", "y")); // trueString == nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("n", "y", "n", "n")); // falseString == nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("y", null, "n", "u")); // trueString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("n", "y", null, "u")); // falseString is null
    }

    // --- toInteger(final boolean bool) ---
    @Test
    void testToIntegerFromBoolean_NormalCases() {
        assertEquals(1, BooleanUtils.toInteger(true));
        assertEquals(0, BooleanUtils.toInteger(false));
    }

    // --- toInteger(final boolean bool, final int trueValue, final int falseValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerFromBooleanWithValuesProvider")
    void testToIntegerFromBooleanWithValues_NormalCases(boolean bool, int trueValue, int falseValue, int expected) {
        assertEquals(expected, BooleanUtils.toInteger(bool, trueValue, falseValue));
    }

    private static Stream<Arguments> toIntegerFromBooleanWithValuesProvider() {
        return Stream.of(
                Arguments.of(true, 1, 0, 1),
                Arguments.of(false, 1, 0, 0),
                Arguments.of(true, 10, 20, 10),
                Arguments.of(false, 10, 20, 20)
        );
    }

    // --- toInteger(final Boolean bool, final int trueValue, final int falseValue, final int nullValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerFromBooleanObjectWithValuesProvider")
    void testToIntegerFromBooleanObjectWithValues_NormalCases(Boolean bool, int trueValue, int falseValue, int nullValue, int expected) {
        assertEquals(expected, BooleanUtils.toInteger(bool, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toIntegerFromBooleanObjectWithValuesProvider() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, 1, 0, -1, 1),
                Arguments.of(Boolean.FALSE, 1, 0, -1, 0),
                Arguments.of(null, 1, 0, -1, -1),
                Arguments.of(Boolean.TRUE, 10, 20, 30, 10),
                Arguments.of(Boolean.FALSE, 10, 20, 30, 20),
                Arguments.of(null, 10, 20, 30, 30)
        );
    }

    // --- toIntegerObject(final boolean bool) ---
    @Test
    void testToIntegerObjectFromBoolean_NormalCases() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(true));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(false));
    }

    // --- toIntegerObject(final boolean bool, final Integer trueValue, final Integer falseValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerObjectFromBooleanWithValuesProvider")
    void testToIntegerObjectFromBooleanWithValues_NormalCases(boolean bool, Integer trueValue, Integer falseValue, Integer expected) {
        assertEquals(expected, BooleanUtils.toIntegerObject(bool, trueValue, falseValue));
    }

    private static Stream<Arguments> toIntegerObjectFromBooleanWithValuesProvider() {
        return Stream.of(
                Arguments.of(true, 1, 0, 1),
                Arguments.of(false, 1, 0, 0),
                Arguments.of(true, 10, 20, 10),
                Arguments.of(false, 10, 20, 20)
        );
    }

    @Test
    void testToIntegerObjectFromBooleanWithValues_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(true, null, 0));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(false, 1, null));
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
    @ParameterizedTest
    @MethodSource("toIntegerObjectFromBooleanObjectWithValuesProvider")
    void testToIntegerObjectFromBooleanObjectWithValues_NormalCases(Boolean bool, Integer trueValue, Integer falseValue, Integer nullValue, Integer expected) {
        assertEquals(expected, BooleanUtils.toIntegerObject(bool, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toIntegerObjectFromBooleanObjectWithValuesProvider() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, 1, 0, -1, 1),
                Arguments.of(Boolean.FALSE, 1, 0, -1, 0),
                Arguments.of(null, 1, 0, -1, -1),
                Arguments.of(Boolean.TRUE, 10, 20, 30, 10),
                Arguments.of(Boolean.FALSE, 10, 20, 30, 20),
                Arguments.of(null, 10, 20, 30, 30)
        );
    }

    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(Boolean.TRUE, null, 0, -1));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(Boolean.FALSE, 1, null, -1));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toIntegerObject(null, 1, 0, null)); // nullValue cannot be null if bool is null
    }

    // --- toString(final boolean bool, final String trueString, final String falseString) ---
    @ParameterizedTest
    @MethodSource("toStringFromBooleanWithStringsProvider")
    void testToStringFromBooleanWithStrings_NormalCases(boolean bool, String trueString, String falseString, String expected) {
        assertEquals(expected, BooleanUtils.toString(bool, trueString, falseString));
    }

    private static Stream<Arguments> toStringFromBooleanWithStringsProvider() {
        return Stream.of(
                Arguments.of(true, "Y", "N", "Y"),
                Arguments.of(false, "Y", "N", "N"),
                Arguments.of(true, "True", "False", "True"),
                Arguments.of(false, "True", "False", "False")
        );
    }

    @Test
    void testToStringFromBooleanWithStrings_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(true, null, "N"));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(false, "Y", null));
    }

    // --- toString(final Boolean bool, final String trueString, final String falseString, final String nullString) ---
    @ParameterizedTest
    @MethodSource("toStringFromBooleanObjectWithStringsProvider")
    void testToStringFromBooleanObjectWithStrings_NormalCases(Boolean bool, String trueString, String falseString, String nullString, String expected) {
        assertEquals(expected, BooleanUtils.toString(bool, trueString, falseString, nullString));
    }

    private static Stream<Arguments> toStringFromBooleanObjectWithStringsProvider() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, "Y", "N", "U", "Y"),
                Arguments.of(Boolean.FALSE, "Y", "N", "U", "N"),
                Arguments.of(null, "Y", "N", "U", "U"),
                Arguments.of(Boolean.TRUE, "True", "False", "Unknown", "True"),
                Arguments.of(Boolean.FALSE, "True", "False", "Unknown", "False"),
                Arguments.of(null, "True", "False", "Unknown", "Unknown")
        );
    }

    @Test
    void testToStringFromBooleanObjectWithStrings_NullInputs() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(Boolean.TRUE, null, "N", "U"));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(Boolean.FALSE, "Y", null, "U"));
        assertThrows(NullPointerException.class, () -> BooleanUtils.toString(null, "Y", "N", null)); // nullString cannot be null if bool is null
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
    void test