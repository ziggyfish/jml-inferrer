package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.BooleanUtils;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.*;

class BooleanUtilsTestP3CP3C {

    // --- and(final boolean... array) ---
    @Test
    void testAndPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.and(true, true, true));
        assertFalse(BooleanUtils.and(true, false, true));
        assertFalse(BooleanUtils.and(false, false, false));
        assertTrue(BooleanUtils.and(true));
        assertFalse(BooleanUtils.and(false));
    }

    @Test
    void testAndPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and()); // Empty array
        assertTrue(BooleanUtils.and(true)); // Single true
        assertFalse(BooleanUtils.and(false)); // Single false
    }

    // --- and(final Boolean... array) ---
    @Test
    void testAndObject_NormalBehavior() {
        assertTrue(BooleanUtils.and(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.and(Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE));
    }

    @Test
    void testAndObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and()); // Empty array
        assertTrue(BooleanUtils.and(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.and(Boolean.FALSE)); // Single false
    }

    @Test
    void testAndObject_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and(Boolean.TRUE, null, Boolean.TRUE)); // Null element
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and((Boolean[]) null)); // Null array
    }

    // --- booleanValues() ---
    @Test
    void testBooleanValues_NormalBehavior() {
        Boolean[] expected = {Boolean.FALSE, Boolean.TRUE};
        assertArrayEquals(expected, BooleanUtils.booleanValues());
    }

    @Test
    void testBooleanValues_Immutable() {
        Boolean[] values = BooleanUtils.booleanValues();
        assertNotNull(values);
        assertEquals(2, values.length);
        // Ensure it's not the same instance that can be modified
        values[0] = Boolean.TRUE; // Try to modify
        Boolean[] original = BooleanUtils.booleanValues();
        assertFalse(original[0]); // Should still be FALSE
    }

    // --- compare(final boolean x, final boolean y) ---
    @Test
    void testCompare_NormalBehavior() {
        assertEquals(0, BooleanUtils.compare(true, true));
        assertEquals(0, BooleanUtils.compare(false, false));
        assertEquals(1, BooleanUtils.compare(true, false));
        assertEquals(-1, BooleanUtils.compare(false, true));
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
    void testForEach_FailureScenarios() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.forEach(null));
    }

    @Test
    void testForEach_Order() {
        List<Boolean> consumedBooleans = new ArrayList<>();
        BooleanUtils.forEach(consumedBooleans::add);
        // The order is not explicitly guaranteed by the JML, but typically it's FALSE then TRUE.
        // We'll test for the common implementation behavior.
        assertEquals(Boolean.FALSE, consumedBooleans.get(0));
        assertEquals(Boolean.TRUE, consumedBooleans.get(1));
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
        assertTrue(BooleanUtils.isNotFalse(Boolean.TRUE));
        assertTrue(BooleanUtils.isNotFalse(null));
        assertFalse(BooleanUtils.isNotFalse(Boolean.FALSE));
    }

    // --- isNotTrue(final Boolean bool) ---
    @Test
    void testIsNotTrue_NormalBehavior() {
        assertTrue(BooleanUtils.isNotTrue(Boolean.FALSE));
        assertTrue(BooleanUtils.isNotTrue(null));
        assertFalse(BooleanUtils.isNotTrue(Boolean.TRUE));
    }

    // --- isTrue(final Boolean bool) ---
    @Test
    void testIsTrue_NormalBehavior() {
        assertTrue(BooleanUtils.isTrue(Boolean.TRUE));
        assertFalse(BooleanUtils.isTrue(Boolean.FALSE));
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
    void testOneHotPrimitive_EdgeCases() {
        assertFalse(BooleanUtils.oneHot(true, true, false)); // More than one true
        assertFalse(BooleanUtils.oneHot(false, false, false)); // No true
        assertFalse(BooleanUtils.oneHot()); // Empty array
        assertTrue(BooleanUtils.oneHot(true)); // Single true
        assertFalse(BooleanUtils.oneHot(false)); // Single false
    }

    // --- oneHot(final Boolean... array) ---
    @Test
    void testOneHotObject_NormalBehavior() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.TRUE));
    }

    @Test
    void testOneHotObject_EdgeCases() {
        assertFalse(BooleanUtils.oneHot(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE)); // More than one true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE)); // No true
        assertFalse(BooleanUtils.oneHot()); // Empty array
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE)); // Single false
    }

    @Test
    void testOneHotObject_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot(Boolean.TRUE, null, Boolean.FALSE)); // Null element
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot((Boolean[]) null)); // Null array
    }

    // --- or(final boolean... array) ---
    @Test
    void testOrPrimitive_NormalBehavior() {
        assertTrue(BooleanUtils.or(true, true, true));
        assertTrue(BooleanUtils.or(true, false, true));
        assertFalse(BooleanUtils.or(false, false, false));
        assertTrue(BooleanUtils.or(true));
        assertFalse(BooleanUtils.or(false));
    }

    @Test
    void testOrPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or()); // Empty array
        assertTrue(BooleanUtils.or(true)); // Single true
        assertFalse(BooleanUtils.or(false)); // Single false
    }

    // --- or(final Boolean... array) ---
    @Test
    void testOrObject_NormalBehavior() {
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.or(Boolean.TRUE));
        assertFalse(BooleanUtils.or(Boolean.FALSE));
    }

    @Test
    void testOrObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or()); // Empty array
        assertTrue(BooleanUtils.or(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.or(Boolean.FALSE)); // Single false
    }

    @Test
    void testOrObject_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or(Boolean.FALSE, null, Boolean.FALSE)); // Null element
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or((Boolean[]) null)); // Null array
    }

    // --- primitiveValues() ---
    @Test
    void testPrimitiveValues_NormalBehavior() {
        boolean[] expected = {false, true};
        assertArrayEquals(expected, BooleanUtils.primitiveValues());
    }

    @Test
    void testPrimitiveValues_Immutable() {
        boolean[] values = BooleanUtils.primitiveValues();
        assertNotNull(values);
        assertEquals(2, values.length);
        // Ensure it's not the same instance that can be modified
        values[0] = true; // Try to modify
        boolean[] original = BooleanUtils.primitiveValues();
        assertFalse(original[0]); // Should still be FALSE
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
    @Test
    void testToBooleanFromInt_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean(1));
        assertFalse(BooleanUtils.toBoolean(0));
    }

    @Test
    void testToBooleanFromInt_EdgeCases() {
        assertTrue(BooleanUtils.toBoolean(Integer.MAX_VALUE));
        assertTrue(BooleanUtils.toBoolean(Integer.MIN_VALUE));
        assertTrue(BooleanUtils.toBoolean(-1));
    }

    // --- toBoolean(final int value, final int trueValue, final int falseValue) ---
    @Test
    void testToBooleanFromIntWithValues_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean(5, 5, 10));
        assertFalse(BooleanUtils.toBoolean(10, 5, 10));
    }

    @Test
    void testToBooleanFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(5, 5, 5)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(15, 5, 10)); // value not trueValue or falseValue
    }

    // --- toBoolean(final Integer value, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToBooleanFromIntegerWithValues_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(10)));
        assertFalse(BooleanUtils.toBoolean(Integer.valueOf(10), Integer.valueOf(5), Integer.valueOf(10)));
    }

    @Test
    void testToBooleanFromIntegerWithValues_EdgeCases() {
        assertFalse(BooleanUtils.toBoolean(null, Integer.valueOf(5), Integer.valueOf(10))); // value is null, not trueValue/falseValue
        assertTrue(BooleanUtils.toBoolean(null, null, Integer.valueOf(10))); // value is null, trueValue is null
        assertFalse(BooleanUtils.toBoolean(null, Integer.valueOf(5), null)); // value is null, falseValue is null
    }

    @Test
    void testToBooleanFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(5))); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(15), Integer.valueOf(5), Integer.valueOf(10))); // value not trueValue or falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(5), null, null)); // trueValue and falseValue are null
    }

    // --- toBoolean(final String str) ---
    @Test
    void testToBooleanFromString_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean("true"));
        assertTrue(BooleanUtils.toBoolean("TRUE"));
        assertTrue(BooleanUtils.toBoolean("on"));
        assertTrue(BooleanUtils.toBoolean("yes"));
        assertTrue(BooleanUtils.toBoolean("y"));
        assertTrue(BooleanUtils.toBoolean("t"));

        assertFalse(BooleanUtils.toBoolean("false"));
        assertFalse(BooleanUtils.toBoolean("FALSE"));
        assertFalse(BooleanUtils.toBoolean("off"));
        assertFalse(BooleanUtils.toBoolean("no"));
        assertFalse(BooleanUtils.toBoolean("n"));
        assertFalse(BooleanUtils.toBoolean("f"));
        assertFalse(BooleanUtils.toBoolean("abc"));
        assertFalse(BooleanUtils.toBoolean(""));
    }

    @Test
    void testToBooleanFromString_EdgeCases() {
        assertFalse(BooleanUtils.toBoolean(null));
    }

    // --- toBoolean(final String str, final String trueString, final String falseString) ---
    @Test
    void testToBooleanFromStringWithStrings_NormalBehavior() {
        assertTrue(BooleanUtils.toBoolean("Y", "Y", "N"));
        assertFalse(BooleanUtils.toBoolean("N", "Y", "N"));
        assertTrue(BooleanUtils.toBoolean("active", "active", "inactive"));
    }

    @Test
    void testToBooleanFromStringWithStrings_EdgeCases() {
        assertTrue(BooleanUtils.toBoolean(null, null, "N"));
        assertFalse(BooleanUtils.toBoolean(null, "Y", null));
        assertTrue(BooleanUtils.toBoolean("", "", "N"));
        assertFalse(BooleanUtils.toBoolean("N", "", "N"));
    }

    @Test
    void testToBooleanFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("Y", "Y", "Y")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("X", "Y", "N")); // str not trueString or falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("Y", null, null)); // trueString and falseString are null
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
    @Test
    void testToBooleanObjectFromInt_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(1));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(0));
    }

    @Test
    void testToBooleanObjectFromInt_EdgeCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.MAX_VALUE));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.MIN_VALUE));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(-1));
    }

    // --- toBooleanObject(final int value, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToBooleanObjectFromIntWithValues_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(5, 5, 10, 0));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(10, 5, 10, 0));
        assertNull(BooleanUtils.toBooleanObject(0, 5, 10, 0));
    }

    @Test
    void testToBooleanObjectFromIntWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(5, 5, 5, 0)); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(5, 5, 10, 5)); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(5, 10, 5, 5)); // falseValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(15, 5, 10, 0)); // value not trueValue, falseValue, or nullValue
    }

    // --- toBooleanObject(final Integer value) ---
    @Test
    void testToBooleanObjectFromInteger_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(1)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(0)));
    }

    @Test
    void testToBooleanObjectFromInteger_EdgeCases() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(Integer.MAX_VALUE)));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(Integer.MIN_VALUE)));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(-1)));
        assertNull(BooleanUtils.toBooleanObject(null));
    }

    // --- toBooleanObject(final Integer value, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToBooleanObjectFromIntegerWithValues_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(10), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertNull(BooleanUtils.toBooleanObject(Integer.valueOf(0), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_EdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(null, Integer.valueOf(5), Integer.valueOf(10), null)); // value is null, nullValue is null
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(null, null, Integer.valueOf(10), Integer.valueOf(0))); // value is null, trueValue is null
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(null, Integer.valueOf(5), null, Integer.valueOf(0))); // value is null, falseValue is null
    }

    @Test
    void testToBooleanObjectFromIntegerWithValues_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(0))); // trueValue == falseValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(5))); // trueValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(5), Integer.valueOf(5))); // falseValue == nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(15), Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0))); // value not trueValue, falseValue, or nullValue
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), null, null, Integer.valueOf(0))); // trueValue and falseValue are null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(5), null, null)); // falseValue and nullValue are null
    }

    // --- toBooleanObject(final String str) ---
    @Test
    void testToBooleanObjectFromString_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("true"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("TRUE"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("on"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("yes"));

        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("false"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("FALSE"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("off"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("no"));

        assertNull(BooleanUtils.toBooleanObject("abc"));
        assertNull(BooleanUtils.toBooleanObject(""));
    }

    @Test
    void testToBooleanObjectFromString_EdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(null));
    }

    // --- toBooleanObject(final String str, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToBooleanObjectFromStringWithStrings_NormalBehavior() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("Y", "Y", "N", "U"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("N", "Y", "N", "U"));
        assertNull(BooleanUtils.toBooleanObject("U", "Y", "N", "U"));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_EdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(null, "Y", "N", null)); // str is null, nullString is null
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(null, null, "N", "U")); // str is null, trueString is null
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(null, "Y", null, "U")); // str is null, falseString is null
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("", "", "N", "U"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("N", "Y", "", "U"));
    }

    @Test
    void testToBooleanObjectFromStringWithStrings_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("Y", "Y", "Y", "U")); // trueString == falseString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("Y", "Y", "N", "Y")); // trueString == nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("Y", "N", "Y", "Y")); // falseString == nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("X", "Y", "N", "U")); // str not trueString, falseString, or nullString
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("Y", null, null, "U")); // trueString and falseString are null
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
        assertEquals(5, BooleanUtils.toInteger(true, 5, 10));
        assertEquals(10, BooleanUtils.toInteger(false, 5, 10));
    }

    // --- toInteger(final Boolean bool, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToIntegerFromBooleanObjectWithValues_NormalBehavior() {
        assertEquals(5, BooleanUtils.toInteger(Boolean.TRUE, 5, 10, 0));
        assertEquals(10, BooleanUtils.toInteger(Boolean.FALSE, 5, 10, 0));
        assertEquals(0, BooleanUtils.toInteger(null, 5, 10, 0));
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
        assertEquals(Integer.valueOf(5), BooleanUtils.toIntegerObject(true, Integer.valueOf(5), Integer.valueOf(10)));
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(false, Integer.valueOf(5), Integer.valueOf(10)));
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
        assertEquals(Integer.valueOf(5), BooleanUtils.toIntegerObject(Boolean.TRUE, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(null, Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(0)));
    }

    // --- toString(final boolean bool, final String trueString, final String falseString) ---
    @Test
    void testToStringFromBooleanWithStrings_NormalBehavior() {
        assertEquals("Y", BooleanUtils.toString(true, "Y", "N"));
        assertEquals("N", BooleanUtils.toString(false, "Y", "N"));
    }

    // --- toString(final Boolean bool, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToStringFromBooleanObjectWithStrings_NormalBehavior() {
        assertEquals("Y", BooleanUtils.toString(Boolean.TRUE, "Y", "N", "U"));
        assertEquals("N", BooleanUtils.toString(Boolean.FALSE, "Y", "N", "U"));
        assertEquals("U", BooleanUtils.toString(null, "Y", "N", "U"));
    }

    @Test
    void testToStringFromBooleanObjectWithStrings_EdgeCases() {
        assertEquals(null, BooleanUtils.toString(null, "Y", "N", null));
        assertEquals("", BooleanUtils.toString(Boolean.TRUE, "", "N", "U"));
        assertEquals("", BooleanUtils.toString(Boolean.FALSE, "Y", "", "U"));
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
        assertEquals(null, BooleanUtils.toStringOnOff(null));
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
        assertEquals(null, BooleanUtils.toStringTrueFalse(null));
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
        assertEquals(null, BooleanUtils.toStringYesNo(null));
    }

    // --- values() ---
    @Test
    void testValues_NormalBehavior() {
        List<Boolean> expected = Arrays.asList(Boolean.FALSE, Boolean.TRUE);
        assertEquals(expected, BooleanUtils.values());
    }

    @Test
    void testValues_Immutable() {
        List<Boolean> values = BooleanUtils.values();
        assertNotNull(values);
        assertEquals(2, values.size());
        // Ensure the returned list is immutable
        assertThrows(UnsupportedOperationException.class, () -> values.add(Boolean.TRUE));
    }

    // --- xor(final boolean... array) ---
    @Test
    void testXorPrimitive_NormalBehavior() {
        assertFalse(BooleanUtils.xor(false, false, false));
        assertTrue(BooleanUtils.xor(true, false, false));
        assertTrue(BooleanUtils.xor(false, true, false));
        assertTrue(BooleanUtils.xor(false, false, true));
        assertFalse(BooleanUtils.xor(true, true, false));
        assertFalse(BooleanUtils.xor(true, true, true));
    }

    @Test
    void testXorPrimitive_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor()); // Empty array
        assertTrue(BooleanUtils.xor(true)); // Single true
        assertFalse(BooleanUtils.xor(false)); // Single false
    }

    // --- xor(final Boolean... array) ---
    @Test
    void testXorObject_NormalBehavior() {
        assertFalse(BooleanUtils.xor(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.FALSE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
    }

    @Test
    void testXorObject_EdgeCases() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor()); // Empty array
        assertTrue(BooleanUtils.xor(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.xor(Boolean.FALSE)); // Single false
    }

    @Test
    void testXorObject_FailureScenarios() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor(Boolean.TRUE, null, Boolean.FALSE)); // Null element
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor((Boolean[]) null)); // Null array
    }
}