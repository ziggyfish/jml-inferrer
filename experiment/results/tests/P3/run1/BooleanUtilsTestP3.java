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
    void testAndPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.and(true, true, true));
        assertFalse(BooleanUtils.and(true, false, true));
        assertFalse(BooleanUtils.and(false, false, false));
    }

    @Test
    void testAndPrimitive_EdgeCase_SingleElement() {
        assertTrue(BooleanUtils.and(true));
        assertFalse(BooleanUtils.and(false));
    }

    @Test
    void testAndPrimitive_EdgeCase_EmptyArray() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and());
    }

    @Test
    void testAndPrimitive_EdgeCase_LargeArray() {
        boolean[] largeTrueArray = new boolean[1000];
        Arrays.fill(largeTrueArray, true);
        assertTrue(BooleanUtils.and(largeTrueArray));

        boolean[] largeMixedArray = new boolean[1000];
        Arrays.fill(largeMixedArray, true);
        largeMixedArray[500] = false;
        assertFalse(BooleanUtils.and(largeMixedArray));
    }

    // --- and(final Boolean... array) ---
    @Test
    void testAndObject_NormalBehavior() {
        assertTrue(BooleanUtils.and(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testAndObject_EdgeCase_SingleElement() {
        assertTrue(BooleanUtils.and(Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE));
    }

    @Test
    void testAndObject_EdgeCase_EmptyArray() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and((Boolean[]) null));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and(new Boolean[0]));
    }

    @Test
    void testAndObject_FailureScenario_NullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and(Boolean.TRUE, null, Boolean.TRUE));
    }

    // --- booleanValues() ---
    @Test
    void testBooleanValues() {
        Boolean[] expected = {Boolean.TRUE, Boolean.FALSE};
        assertArrayEquals(expected, BooleanUtils.booleanValues());
    }

    // --- compare(final boolean x, final boolean y) ---
    @ParameterizedTest
    @MethodSource("comparePrimitiveArgs")
    void testComparePrimitive(boolean x, boolean y, int expected) {
        assertEquals(expected, BooleanUtils.compare(x, y));
    }

    private static Stream<Arguments> comparePrimitiveArgs() {
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
        List<Boolean> consumedBooleans = new ArrayList<>();
        Consumer<Boolean> consumer = consumedBooleans::add;
        BooleanUtils.forEach(consumer);

        assertEquals(2, consumedBooleans.size());
        assertTrue(consumedBooleans.contains(Boolean.TRUE));
        assertTrue(consumedBooleans.contains(Boolean.FALSE));
    }

    @Test
    void testForEach_FailureScenario_NullConsumer() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.forEach(null));
    }

    @Test
    void testForEach_ConsumerThrowsException() {
        Consumer<Boolean> consumer = b -> {
            throw new RuntimeException("Test exception");
        };
        assertThrows(RuntimeException.class, () -> BooleanUtils.forEach(consumer));
    }

    // --- isFalse(final Boolean bool) ---
    @ParameterizedTest
    @MethodSource("isFalseArgs")
    void testIsFalse(Boolean bool, boolean expected) {
        assertEquals(expected, BooleanUtils.isFalse(bool));
    }

    private static Stream<Arguments> isFalseArgs() {
        return Stream.of(
                Arguments.of(Boolean.FALSE, true),
                Arguments.of(Boolean.TRUE, false),
                Arguments.of(null, false)
        );
    }

    // --- isNotFalse(final Boolean bool) ---
    @ParameterizedTest
    @MethodSource("isNotFalseArgs")
    void testIsNotFalse(Boolean bool, boolean expected) {
        assertEquals(expected, BooleanUtils.isNotFalse(bool));
    }

    private static Stream<Arguments> isNotFalseArgs() {
        return Stream.of(
                Arguments.of(Boolean.FALSE, false),
                Arguments.of(Boolean.TRUE, true),
                Arguments.of(null, true)
        );
    }

    // --- isNotTrue(final Boolean bool) ---
    @ParameterizedTest
    @MethodSource("isNotTrueArgs")
    void testIsNotTrue(Boolean bool, boolean expected) {
        assertEquals(expected, BooleanUtils.isNotTrue(bool));
    }

    private static Stream<Arguments> isNotTrueArgs() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, false),
                Arguments.of(Boolean.FALSE, true),
                Arguments.of(null, true)
        );
    }

    // --- isTrue(final Boolean bool) ---
    @ParameterizedTest
    @MethodSource("isTrueArgs")
    void testIsTrue(Boolean bool, boolean expected) {
        assertEquals(expected, BooleanUtils.isTrue(bool));
    }

    private static Stream<Arguments> isTrueArgs() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, true),
                Arguments.of(Boolean.FALSE, false),
                Arguments.of(null, false)
        );
    }

    // --- negate(final Boolean bool) ---
    @ParameterizedTest
    @MethodSource("negateArgs")
    void testNegate(Boolean input, Boolean expected) {
        assertEquals(expected, BooleanUtils.negate(input));
    }

    private static Stream<Arguments> negateArgs() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, Boolean.FALSE),
                Arguments.of(Boolean.FALSE, Boolean.TRUE),
                Arguments.of(null, null)
        );
    }

    // --- oneHot(final boolean... array) ---
    @Test
    void testOneHotPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.oneHot(true, false, false));
        assertTrue(BooleanUtils.oneHot(false, true, false));
        assertTrue(BooleanUtils.oneHot(false, false, true));
    }

    @Test
    void testOneHotPrimitive_FailureScenario_MultipleTrue() {
        assertFalse(BooleanUtils.oneHot(true, true, false));
        assertFalse(BooleanUtils.oneHot(true, true, true));
    }

    @Test
    void testOneHotPrimitive_FailureScenario_NoTrue() {
        assertFalse(BooleanUtils.oneHot(false, false, false));
    }

    @Test
    void testOneHotPrimitive_EdgeCase_SingleElement() {
        assertTrue(BooleanUtils.oneHot(true));
        assertFalse(BooleanUtils.oneHot(false));
    }

    @Test
    void testOneHotPrimitive_EdgeCase_EmptyArray() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot());
    }

    // --- oneHot(final Boolean... array) ---
    @Test
    void testOneHotObject_NormalBehavior() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
    }

    @Test
    void testOneHotObject_FailureScenario_MultipleTrue() {
        assertFalse(BooleanUtils.oneHot(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE));
    }

    @Test
    void testOneHotObject_FailureScenario_NoTrue() {
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testOneHotObject_EdgeCase_SingleElement() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE));
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE));
    }

    @Test
    void testOneHotObject_EdgeCase_EmptyArray() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot((Boolean[]) null));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot(new Boolean[0]));
    }

    @Test
    void testOneHotObject_FailureScenario_NullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot(Boolean.TRUE, null, Boolean.FALSE));
    }

    // --- or(final boolean... array) ---
    @Test
    void testOrPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.or(true, false, false));
        assertTrue(BooleanUtils.or(true, true, true));
        assertFalse(BooleanUtils.or(false, false, false));
    }

    @Test
    void testOrPrimitive_EdgeCase_SingleElement() {
        assertTrue(BooleanUtils.or(true));
        assertFalse(BooleanUtils.or(false));
    }

    @Test
    void testOrPrimitive_EdgeCase_EmptyArray() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or());
    }

    // --- or(final Boolean... array) ---
    @Test
    void testOrObject_NormalBehavior() {
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testOrObject_EdgeCase_SingleElement() {
        assertTrue(BooleanUtils.or(Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE));
    }

    @Test
    void testOrObject_EdgeCase_EmptyArray() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or((Boolean[]) null));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or(new Boolean[0]));
    }

    @Test
    void testOrObject_FailureScenario_NullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or(Boolean.FALSE, null, Boolean.FALSE));
    }

    // --- primitiveValues() ---
    @Test
    void testPrimitiveValues() {
        boolean[] expected = {true, false};
        assertArrayEquals(expected, BooleanUtils.primitiveValues());
    }

    // --- toBoolean(final Boolean bool) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromBooleanArgs")
    void testToBooleanFromBoolean(Boolean bool, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(bool));
    }

    private static Stream<Arguments> toBooleanFromBooleanArgs() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, true),
                Arguments.of(Boolean.FALSE, false),
                Arguments.of(null, false)
        );
    }

    // --- toBoolean(final int value) ---
    @ParameterizedTest
    @ValueSource(ints = {1, 5, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
    void testToBooleanFromInt_True(int value) {
        assertTrue(BooleanUtils.toBoolean(value));
    }

    @Test
    void testToBooleanFromInt_False() {
        assertFalse(BooleanUtils.toBoolean(0));
    }

    // --- toBoolean(final int value, final int trueValue, final int falseValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromIntWithValuesArgs")
    void testToBooleanFromIntWithValues(int value, int trueValue, int falseValue, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(value, trueValue, falseValue));
    }

    private static Stream<Arguments> toBooleanFromIntWithValuesArgs() {
        return Stream.of(
                Arguments.of(1, 1, 0, true),
                Arguments.of(0, 1, 0, false),
                Arguments.of(5, 5, 10, true),
                Arguments.of(10, 5, 10, false),
                Arguments.of(-1, -1, 0, true),
                Arguments.of(0, -1, 0, false)
        );
    }

    @Test
    void testToBooleanFromIntWithValues_FailureScenario_NeitherTrueNorFalse() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(2, 1, 0));
    }

    @Test
    void testToBooleanFromIntWithValues_FailureScenario_TrueAndFalseAreSame() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 1, 1));
    }

    // --- toBoolean(final Integer value, final Integer trueValue, final Integer falseValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromIntegerWithValuesArgs")
    void testToBooleanFromIntegerWithValues(Integer value, Integer trueValue, Integer falseValue, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(value, trueValue, falseValue));
    }

    private static Stream<Arguments> toBooleanFromIntegerWithValuesArgs() {
        return Stream.of(
                Arguments.of(1, 1, 0, true),
                Arguments.of(0, 1, 0, false),
                Arguments.of(5, 5, 10, true),
                Arguments.of(10, 5, 10, false),
                Arguments.of(-1, -1, 0, true),
                Arguments.of(0, -1, 0, false)
        );
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenario_NeitherTrueNorFalse() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(2, 1, 0));
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenario_TrueAndFalseAreSame() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, 1, 1));
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenario_NullValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, 1, 0));
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenario_NullTrueValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(1, null, 0));
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenario_NullFalseValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(0, 1, null));
    }

    // --- toBoolean(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "TRUE", "TrUe", "on", "ON", "yes", "YES", "y", "Y", "t", "T"})
    void testToBooleanFromString_True(String str) {
        assertTrue(BooleanUtils.toBoolean(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "FALSE", "f", "F", "no", "NO", "off", "OFF", "n", "N", "", "  ", "abc", "123"})
    @NullSource
    void testToBooleanFromString_False(String str) {
        assertFalse(BooleanUtils.toBoolean(str));
    }

    // --- toBoolean(final String str, final String trueString, final String falseString) ---
    @ParameterizedTest
    @MethodSource("toBooleanFromStringWithStringsArgs")
    void testToBooleanFromStringWithStrings(String str, String trueString, String falseString, boolean expected) {
        assertEquals(expected, BooleanUtils.toBoolean(str, trueString, falseString));
    }

    private static Stream<Arguments> toBooleanFromStringWithStringsArgs() {
        return Stream.of(
                Arguments.of("yes", "yes", "no", true),
                Arguments.of("no", "yes", "no", false),
                Arguments.of("Y", "Y", "N", true),
                Arguments.of("N", "Y", "N", false),
                Arguments.of("TRUE", "TRUE", "FALSE", true),
                Arguments.of("FALSE", "TRUE", "FALSE", false),
                Arguments.of(null, "yes", "no", false) // null str defaults to false
        );
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenario_NeitherTrueNorFalse() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("maybe", "yes", "no"));
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenario_TrueAndFalseAreSame() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("yes", "yes", "yes"));
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenario_NullTrueString() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("yes", null, "no"));
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenario_NullFalseString() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("no", "yes", null));
    }

    // --- toBooleanDefaultIfNull(final Boolean bool, final boolean valueIfNull) ---
    @ParameterizedTest
    @MethodSource("toBooleanDefaultIfNullArgs")
    void testToBooleanDefaultIfNull(Boolean bool, boolean valueIfNull, boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanDefaultIfNull(bool, valueIfNull));
    }

    private static Stream<Arguments> toBooleanDefaultIfNullArgs() {
        return Stream.of(
                Arguments.of(Boolean.TRUE, true, true),
                Arguments.of(Boolean.TRUE, false, true),
                Arguments.of(Boolean.FALSE, true, false),
                Arguments.of(Boolean.FALSE, false, false),
                Arguments.of(null, true, true),
                Arguments.of(null, false, false)
        );
    }

    // --- toBooleanObject(final int value) ---
    @ParameterizedTest
    @ValueSource(ints = {1, 5, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
    void testToBooleanObjectFromInt_True(int value) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(value));
    }

    @Test
    void testToBooleanObjectFromInt_False() {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(0));
    }

    // --- toBooleanObject(final int value, final int trueValue, final int falseValue, final int nullValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromIntWithValuesArgs")
    void testToBooleanObjectFromIntWithValues(int value, int trueValue, int falseValue, int nullValue, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(value, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toBooleanObjectFromIntWithValuesArgs() {
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
    void testToBooleanObjectFromIntWithValues_FailureScenario_NeitherTrueFalseNorNull() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(3, 1, 0, 2));
    }

    @Test
    void testToBooleanObjectFromIntWithValues_FailureScenario_DuplicateValues() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 1, 2));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 0, 0));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 2, 1));
    }

    // --- toBooleanObject(final Integer value) ---
    @ParameterizedTest
    @ValueSource(ints = {1, 5, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
    void testToBooleanObjectFromInteger_True(int value) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(value)));
    }

    @Test
    void testToBooleanObjectFromInteger_False() {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(0)));
    }

    @Test
    void testToBooleanObjectFromInteger_Null() {
        assertNull(BooleanUtils.toBooleanObject(null));
    }

    // --- toBooleanObject(final Integer value, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromIntegerWithValuesArgs")
    void testToBooleanObjectFromIntegerWithValues(Integer value, Integer trueValue, Integer falseValue, Integer nullValue, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(value, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toBooleanObjectFromIntegerWithValuesArgs() {
        return Stream.of(
                Arguments.of(1, 1, 0, 2, Boolean.TRUE),
                Arguments.of(0, 1, 0, 2, Boolean.FALSE),
                Arguments.of(2, 1, 0, 2, null),
                Arguments.of(null, 1, 0, null, null),
                Arguments.of(5, 5, 10, 15, Boolean.TRUE),
                Arguments.of(10, 5, 10, 15, Boolean.FALSE),
                Arguments.of(15, 5, 10, 15, null)
        );
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenario_NeitherTrueFalseNorNull() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(3, 1, 0, 2));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenario_DuplicateValues() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 1, 2));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 0, 0));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, 1, 2, 1));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenario_NullTrueValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(1, null, 0, 2));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenario_NullFalseValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(0, 1, null, 2));
    }

    // --- toBooleanObject(final String str) ---
    @ParameterizedTest
    @ValueSource(strings = {"true", "TRUE", "TrUe", "on", "ON", "yes", "YES", "y", "Y", "t", "T"})
    void testToBooleanObjectFromString_True(String str) {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"false", "FALSE", "f", "F", "no", "NO", "off", "OFF", "n", "N"})
    void testToBooleanObjectFromString_False(String str) {
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(str));
    }

    @ParameterizedTest
    @ValueSource(strings = {"", "  ", "abc", "123"})
    @NullSource
    void testToBooleanObjectFromString_Null(String str) {
        assertNull(BooleanUtils.toBooleanObject(str));
    }

    // --- toBooleanObject(final String str, final String trueString, final String falseString, final String nullString) ---
    @ParameterizedTest
    @MethodSource("toBooleanObjectFromStringWithStringsArgs")
    void testToBooleanObjectFromStringWithStrings(String str, String trueString, String falseString, String nullString, Boolean expected) {
        assertEquals(expected, BooleanUtils.toBooleanObject(str, trueString, falseString, nullString));
    }

    private static Stream<Arguments> toBooleanObjectFromStringWithStringsArgs() {
        return Stream.of(
                Arguments.of("yes", "yes", "no", "maybe", Boolean.TRUE),
                Arguments.of("no", "yes", "no", "maybe", Boolean.FALSE),
                Arguments.of("maybe", "yes", "no", "maybe", null),
                Arguments.of(null, "yes", "no", null, null),
                Arguments.of("Y", "Y", "N", "U", Boolean.TRUE),
                Arguments.of("N", "Y", "N", "U", Boolean.FALSE),
                Arguments.of("U", "Y", "N", "U", null)
        );
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenario_NeitherTrueFalseNorNull() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("unknown", "yes", "no", "maybe"));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenario_DuplicateStrings() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("yes", "yes", "yes", "no"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("yes", "yes", "no", "yes"));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("yes", "no", "yes", "yes"));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenario_NullTrueString() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("yes", null, "no", "maybe"));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenario_NullFalseString() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("no", "yes", null, "maybe"));
    }

    // --- toInteger(final boolean bool) ---
    @Test
    void testToIntegerFromBoolean() {
        assertEquals(1, BooleanUtils.toInteger(true));
        assertEquals(0, BooleanUtils.toInteger(false));
    }

    // --- toInteger(final boolean bool, final int trueValue, final int falseValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerFromBooleanWithValuesArgs")
    void testToIntegerFromBooleanWithValues(boolean bool, int trueValue, int falseValue, int expected) {
        assertEquals(expected, BooleanUtils.toInteger(bool, trueValue, falseValue));
    }

    private static Stream<Arguments> toIntegerFromBooleanWithValuesArgs() {
        return Stream.of(
                Arguments.of(true, 1, 0, 1),
                Arguments.of(false, 1, 0, 0),
                Arguments.of(true, 10, 20, 10),
                Arguments.of(false, 10, 20, 20)
        );
    }

    // --- toInteger(final Boolean bool, final int trueValue, final int falseValue, final int nullValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerFromBooleanObjectWithValuesArgs")
    void testToIntegerFromBooleanObjectWithValues(Boolean bool, int trueValue, int falseValue, int nullValue, int expected) {
        assertEquals(expected, BooleanUtils.toInteger(bool, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toIntegerFromBooleanObjectWithValuesArgs() {
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
    void testToIntegerObjectFromBoolean() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(true));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(false));
    }

    // --- toIntegerObject(final boolean bool, final Integer trueValue, final Integer falseValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerObjectFromBooleanWithValuesArgs")
    void testToIntegerObjectFromBooleanWithValues(boolean bool, Integer trueValue, Integer falseValue, Integer expected) {
        assertEquals(expected, BooleanUtils.toIntegerObject(bool, trueValue, falseValue));
    }

    private static Stream<Arguments> toIntegerObjectFromBooleanWithValuesArgs() {
        return Stream.of(
                Arguments.of(true, 1, 0, 1),
                Arguments.of(false, 1, 0, 0),
                Arguments.of(true, 10, 20, 10),
                Arguments.of(false, 10, 20, 20)
        );
    }

    @Test
    void testToIntegerObjectFromBooleanWithValues_FailureScenario_NullTrueValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(true, null, 0));
    }

    @Test
    void testToIntegerObjectFromBooleanWithValues_FailureScenario_NullFalseValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(false, 1, null));
    }

    // --- toIntegerObject(final Boolean bool) ---
    @Test
    void testToIntegerObjectFromBooleanObject() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(Boolean.TRUE));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(Boolean.FALSE));
        assertNull(BooleanUtils.toIntegerObject(null));
    }

    // --- toIntegerObject(final Boolean bool, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @ParameterizedTest
    @MethodSource("toIntegerObjectFromBooleanObjectWithValuesArgs")
    void testToIntegerObjectFromBooleanObjectWithValues(Boolean bool, Integer trueValue, Integer falseValue, Integer nullValue, Integer expected) {
        assertEquals(expected, BooleanUtils.toIntegerObject(bool, trueValue, falseValue, nullValue));
    }

    private static Stream<Arguments> toIntegerObjectFromBooleanObjectWithValuesArgs() {
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
    void testToIntegerObjectFromBooleanObjectWithValues_FailureScenario_NullTrueValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(Boolean.TRUE, null, 0, -1));
    }

    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_FailureScenario_NullFalseValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(Boolean.FALSE, 1, null, -1));
    }

    @Test
    void testToIntegerObjectFromBooleanObjectWithValues_FailureScenario_NullNullValue() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(null, 1, 0, null));
    }

    // --- toString(final boolean bool, final String trueString, final String falseString) ---
    @ParameterizedTest