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
    void testAndPrimitiveNormal() {
        assertTrue(BooleanUtils.and(true, true, true));
        assertFalse(BooleanUtils.and(true, false, true));
        assertFalse(BooleanUtils.and(false, false, false));
    }

    @Test
    void testAndPrimitiveEdgeCases() {
        assertTrue(BooleanUtils.and(true)); // Single true
        assertFalse(BooleanUtils.and(false)); // Single false
        assertTrue(BooleanUtils.and()); // Empty array, should be true (identity for AND)
    }

    // --- and(final Boolean... array) ---
    @Test
    void testAndObjectNormal() {
        assertTrue(BooleanUtils.and(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.TRUE, Boolean.FALSE, Boolean.TRUE));
        assertFalse(BooleanUtils.and(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testAndObjectEdgeCases() {
        assertTrue(BooleanUtils.and(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.and(Boolean.FALSE)); // Single false
        assertTrue(BooleanUtils.and()); // Empty array, should be true (identity for AND)
    }

    @Test
    void testAndObjectFailureNullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.and(Boolean.TRUE, null, Boolean.FALSE));
    }

    // --- booleanValues() ---
    @Test
    void testBooleanValues() {
        Boolean[] expected = {Boolean.FALSE, Boolean.TRUE};
        assertArrayEquals(expected, BooleanUtils.booleanValues());
    }

    // --- compare(final boolean x, final boolean y) ---
    @Test
    void testCompareNormal() {
        assertEquals(0, BooleanUtils.compare(true, true));
        assertEquals(0, BooleanUtils.compare(false, false));
        assertEquals(1, BooleanUtils.compare(true, false));
        assertEquals(-1, BooleanUtils.compare(false, true));
    }

    // --- forEach(final Consumer<Boolean> action) ---
    @Test
    void testForEachNormal() {
        List<Boolean> consumed = new ArrayList<>();
        Consumer<Boolean> consumer = consumed::add;
        BooleanUtils.forEach(consumer);
        assertEquals(Arrays.asList(Boolean.FALSE, Boolean.TRUE), consumed);
    }

    @Test
    void testForEachFailureNullConsumer() {
        assertThrows(NullPointerException.class, () -> BooleanUtils.forEach(null));
    }

    // --- isFalse(final Boolean bool) ---
    @Test
    void testIsFalseNormal() {
        assertTrue(BooleanUtils.isFalse(Boolean.FALSE));
        assertFalse(BooleanUtils.isFalse(Boolean.TRUE));
    }

    @Test
    void testIsFalseEdgeCases() {
        assertFalse(BooleanUtils.isFalse(null));
    }

    // --- isNotFalse(final Boolean bool) ---
    @Test
    void testIsNotFalseNormal() {
        assertFalse(BooleanUtils.isNotFalse(Boolean.FALSE));
        assertTrue(BooleanUtils.isNotFalse(Boolean.TRUE));
    }

    @Test
    void testIsNotFalseEdgeCases() {
        assertTrue(BooleanUtils.isNotFalse(null));
    }

    // --- isNotTrue(final Boolean bool) ---
    @Test
    void testIsNotTrueNormal() {
        assertTrue(BooleanUtils.isNotTrue(Boolean.FALSE));
        assertFalse(BooleanUtils.isNotTrue(Boolean.TRUE));
    }

    @Test
    void testIsNotTrueEdgeCases() {
        assertTrue(BooleanUtils.isNotTrue(null));
    }

    // --- isTrue(final Boolean bool) ---
    @Test
    void testIsTrueNormal() {
        assertFalse(BooleanUtils.isTrue(Boolean.FALSE));
        assertTrue(BooleanUtils.isTrue(Boolean.TRUE));
    }

    @Test
    void testIsTrueEdgeCases() {
        assertFalse(BooleanUtils.isTrue(null));
    }

    // --- negate(final Boolean bool) ---
    @Test
    void testNegateNormal() {
        assertEquals(Boolean.FALSE, BooleanUtils.negate(Boolean.TRUE));
        assertEquals(Boolean.TRUE, BooleanUtils.negate(Boolean.FALSE));
    }

    @Test
    void testNegateEdgeCases() {
        assertNull(BooleanUtils.negate(null));
    }

    // --- oneHot(final boolean... array) ---
    @Test
    void testOneHotPrimitiveNormal() {
        assertTrue(BooleanUtils.oneHot(true, false, false));
        assertTrue(BooleanUtils.oneHot(false, true, false));
        assertTrue(BooleanUtils.oneHot(false, false, true));
    }

    @Test
    void testOneHotPrimitiveFailure() {
        assertFalse(BooleanUtils.oneHot(true, true, false)); // More than one true
        assertFalse(BooleanUtils.oneHot(false, false, false)); // No true
    }

    @Test
    void testOneHotPrimitiveEdgeCases() {
        assertTrue(BooleanUtils.oneHot(true)); // Single true
        assertFalse(BooleanUtils.oneHot(false)); // Single false
        assertFalse(BooleanUtils.oneHot()); // Empty array
    }

    // --- oneHot(final Boolean... array) ---
    @Test
    void testOneHotObjectNormal() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertTrue(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.TRUE));
    }

    @Test
    void testOneHotObjectFailure() {
        assertFalse(BooleanUtils.oneHot(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE)); // More than one true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE)); // No true
    }

    @Test
    void testOneHotObjectEdgeCases() {
        assertTrue(BooleanUtils.oneHot(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.oneHot(Boolean.FALSE)); // Single false
        assertFalse(BooleanUtils.oneHot()); // Empty array
    }

    @Test
    void testOneHotObjectFailureNullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.oneHot(Boolean.TRUE, null, Boolean.FALSE));
    }

    // --- or(final boolean... array) ---
    @Test
    void testOrPrimitiveNormal() {
        assertTrue(BooleanUtils.or(true, false, false));
        assertTrue(BooleanUtils.or(false, true, false));
        assertFalse(BooleanUtils.or(false, false, false));
    }

    @Test
    void testOrPrimitiveEdgeCases() {
        assertTrue(BooleanUtils.or(true)); // Single true
        assertFalse(BooleanUtils.or(false)); // Single false
        assertFalse(BooleanUtils.or()); // Empty array, should be false (identity for OR)
    }

    // --- or(final Boolean... array) ---
    @Test
    void testOrObjectNormal() {
        assertTrue(BooleanUtils.or(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.or(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.or(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
    }

    @Test
    void testOrObjectEdgeCases() {
        assertTrue(BooleanUtils.or(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.or(Boolean.FALSE)); // Single false
        assertFalse(BooleanUtils.or()); // Empty array, should be false (identity for OR)
    }

    @Test
    void testOrObjectFailureNullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.or(Boolean.TRUE, null, Boolean.FALSE));
    }

    // --- primitiveValues() ---
    @Test
    void testPrimitiveValues() {
        boolean[] expected = {false, true};
        assertArrayEquals(expected, BooleanUtils.primitiveValues());
    }

    // --- toBoolean(final Boolean bool) ---
    @Test
    void testToBooleanObjectNormal() {
        assertTrue(BooleanUtils.toBoolean(Boolean.TRUE));
        assertFalse(BooleanUtils.toBoolean(Boolean.FALSE));
    }

    @Test
    void testToBooleanObjectFailureNull() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null));
    }

    // --- toBoolean(final int value) ---
    @Test
    void testToBooleanIntNormal() {
        assertTrue(BooleanUtils.toBoolean(1));
        assertFalse(BooleanUtils.toBoolean(0));
    }

    @Test
    void testToBooleanIntFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(5));
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(-1));
    }

    // --- toBoolean(final int value, final int trueValue, final int falseValue) ---
    @Test
    void testToBooleanIntCustomValuesNormal() {
        assertTrue(BooleanUtils.toBoolean(10, 10, 20));
        assertFalse(BooleanUtils.toBoolean(20, 10, 20));
    }

    @Test
    void testToBooleanIntCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(5, 10, 20)); // Value not true/false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(10, 10, 10)); // True and false values are same
    }

    // --- toBoolean(final Integer value, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToBooleanIntegerCustomValuesNormal() {
        assertTrue(BooleanUtils.toBoolean(Integer.valueOf(10), Integer.valueOf(10), Integer.valueOf(20)));
        assertFalse(BooleanUtils.toBoolean(Integer.valueOf(20), Integer.valueOf(10), Integer.valueOf(20)));
    }

    @Test
    void testToBooleanIntegerCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(20))); // Value not true/false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(10), Integer.valueOf(10), Integer.valueOf(10))); // True and false values are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, Integer.valueOf(10), Integer.valueOf(20))); // Value is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(10), null, Integer.valueOf(20))); // trueValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(Integer.valueOf(10), Integer.valueOf(10), null)); // falseValue is null
    }

    // --- toBoolean(final String str) ---
    @Test
    void testToBooleanStringNormal() {
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
    }

    @Test
    void testToBooleanStringEdgeCases() {
        assertFalse(BooleanUtils.toBoolean(null));
        assertFalse(BooleanUtils.toBoolean(""));
        assertFalse(BooleanUtils.toBoolean("  "));
        assertFalse(BooleanUtils.toBoolean("abc"));
    }

    // --- toBoolean(final String str, final String trueString, final String falseString) ---
    @Test
    void testToBooleanStringCustomValuesNormal() {
        assertTrue(BooleanUtils.toBoolean("ok", "ok", "notok"));
        assertFalse(BooleanUtils.toBoolean("notok", "ok", "notok"));
    }

    @Test
    void testToBooleanStringCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("maybe", "ok", "notok")); // Value not true/false
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", "ok", "ok")); // True and false strings are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean(null, "ok", "notok")); // str is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", null, "notok")); // trueString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBoolean("ok", "ok", null)); // falseString is null
    }

    // --- toBooleanDefaultIfNull(final Boolean bool, final boolean valueIfNull) ---
    @Test
    void testToBooleanDefaultIfNullNormal() {
        assertTrue(BooleanUtils.toBooleanDefaultIfNull(Boolean.TRUE, false));
        assertFalse(BooleanUtils.toBooleanDefaultIfNull(Boolean.FALSE, true));
    }

    @Test
    void testToBooleanDefaultIfNullEdgeCases() {
        assertTrue(BooleanUtils.toBooleanDefaultIfNull(null, true));
        assertFalse(BooleanUtils.toBooleanDefaultIfNull(null, false));
    }

    // --- toBooleanObject(final int value) ---
    @Test
    void testToBooleanObjectIntNormal() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(1));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(0));
    }

    @Test
    void testToBooleanObjectIntEdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(5));
        assertNull(BooleanUtils.toBooleanObject(-1));
    }

    // --- toBooleanObject(final int value, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToBooleanObjectIntCustomValuesNormal() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(10, 10, 20, 30));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(20, 10, 20, 30));
        assertNull(BooleanUtils.toBooleanObject(30, 10, 20, 30));
    }

    @Test
    void testToBooleanObjectIntCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(5, 10, 20, 30)); // Value not true/false/null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(10, 10, 10, 30)); // True and false values are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(10, 10, 20, 10)); // True and null values are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(20, 10, 20, 20)); // False and null values are same
    }

    // --- toBooleanObject(final Integer value) ---
    @Test
    void testToBooleanObjectIntegerNormal() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(1)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(0)));
    }

    @Test
    void testToBooleanObjectIntegerEdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(Integer.valueOf(5)));
        assertNull(BooleanUtils.toBooleanObject(Integer.valueOf(-1)));
        assertNull(BooleanUtils.toBooleanObject(null));
    }

    // --- toBooleanObject(final Integer value, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToBooleanObjectIntegerCustomValuesNormal() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject(Integer.valueOf(10), Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject(Integer.valueOf(20), Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertNull(BooleanUtils.toBooleanObject(Integer.valueOf(30), Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertNull(BooleanUtils.toBooleanObject(null, Integer.valueOf(10), Integer.valueOf(20), null));
    }

    @Test
    void testToBooleanObjectIntegerCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(5), Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30))); // Value not true/false/null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(10), Integer.valueOf(10), Integer.valueOf(10), Integer.valueOf(30))); // True and false values are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(10), Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(10))); // True and null values are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(20), Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(20))); // False and null values are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(10), null, Integer.valueOf(20), Integer.valueOf(30))); // trueValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject(Integer.valueOf(10), Integer.valueOf(10), null, Integer.valueOf(30))); // falseValue is null
    }

    // --- toBooleanObject(final String str) ---
    @Test
    void testToBooleanObjectStringNormal() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("true"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("TRUE"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("on"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("yes"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("y"));
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("t"));

        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("false"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("FALSE"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("off"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("no"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("n"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("f"));
    }

    @Test
    void testToBooleanObjectStringEdgeCases() {
        assertNull(BooleanUtils.toBooleanObject(null));
        assertNull(BooleanUtils.toBooleanObject(""));
        assertNull(BooleanUtils.toBooleanObject("  "));
        assertNull(BooleanUtils.toBooleanObject("abc"));
    }

    // --- toBooleanObject(final String str, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToBooleanObjectStringCustomValuesNormal() {
        assertEquals(Boolean.TRUE, BooleanUtils.toBooleanObject("ok", "ok", "notok", "maybe"));
        assertEquals(Boolean.FALSE, BooleanUtils.toBooleanObject("notok", "ok", "notok", "maybe"));
        assertNull(BooleanUtils.toBooleanObject("maybe", "ok", "notok", "maybe"));
        assertNull(BooleanUtils.toBooleanObject(null, "ok", "notok", null));
    }

    @Test
    void testToBooleanObjectStringCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("unknown", "ok", "notok", "maybe")); // Value not true/false/null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", "ok", "ok", "maybe")); // True and false strings are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", "ok", "notok", "ok")); // True and null strings are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("notok", "ok", "notok", "notok")); // False and null strings are same
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", null, "notok", "maybe")); // trueString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toBooleanObject("ok", "ok", null, "maybe")); // falseString is null
    }

    // --- toInteger(final boolean bool) ---
    @Test
    void testToIntegerPrimitiveNormal() {
        assertEquals(1, BooleanUtils.toInteger(true));
        assertEquals(0, BooleanUtils.toInteger(false));
    }

    // --- toInteger(final boolean bool, final int trueValue, final int falseValue) ---
    @Test
    void testToIntegerPrimitiveCustomValuesNormal() {
        assertEquals(10, BooleanUtils.toInteger(true, 10, 20));
        assertEquals(20, BooleanUtils.toInteger(false, 10, 20));
    }

    // --- toInteger(final Boolean bool, final int trueValue, final int falseValue, final int nullValue) ---
    @Test
    void testToIntegerObjectCustomValuesNormal() {
        assertEquals(10, BooleanUtils.toInteger(Boolean.TRUE, 10, 20, 30));
        assertEquals(20, BooleanUtils.toInteger(Boolean.FALSE, 10, 20, 30));
        assertEquals(30, BooleanUtils.toInteger(null, 10, 20, 30));
    }

    // --- toIntegerObject(final boolean bool) ---
    @Test
    void testToIntegerObjectPrimitiveNormal() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(true));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(false));
    }

    // --- toIntegerObject(final boolean bool, final Integer trueValue, final Integer falseValue) ---
    @Test
    void testToIntegerObjectPrimitiveCustomValuesNormal() {
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(true, Integer.valueOf(10), Integer.valueOf(20)));
        assertEquals(Integer.valueOf(20), BooleanUtils.toIntegerObject(false, Integer.valueOf(10), Integer.valueOf(20)));
    }

    @Test
    void testToIntegerObjectPrimitiveCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(true, null, Integer.valueOf(20))); // trueValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(false, Integer.valueOf(10), null)); // falseValue is null
    }

    // --- toIntegerObject(final Boolean bool) ---
    @Test
    void testToIntegerObjectObjectNormal() {
        assertEquals(Integer.valueOf(1), BooleanUtils.toIntegerObject(Boolean.TRUE));
        assertEquals(Integer.valueOf(0), BooleanUtils.toIntegerObject(Boolean.FALSE));
    }

    @Test
    void testToIntegerObjectObjectEdgeCases() {
        assertNull(BooleanUtils.toIntegerObject(null));
    }

    // --- toIntegerObject(final Boolean bool, final Integer trueValue, final Integer falseValue, final Integer nullValue) ---
    @Test
    void testToIntegerObjectObjectCustomValuesNormal() {
        assertEquals(Integer.valueOf(10), BooleanUtils.toIntegerObject(Boolean.TRUE, Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertEquals(Integer.valueOf(20), BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
        assertEquals(Integer.valueOf(30), BooleanUtils.toIntegerObject(null, Integer.valueOf(10), Integer.valueOf(20), Integer.valueOf(30)));
    }

    @Test
    void testToIntegerObjectObjectCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(Boolean.TRUE, null, Integer.valueOf(20), Integer.valueOf(30))); // trueValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(Boolean.FALSE, Integer.valueOf(10), null, Integer.valueOf(30))); // falseValue is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toIntegerObject(null, Integer.valueOf(10), Integer.valueOf(20), null)); // nullValue is null
    }

    // --- toString(final boolean bool, final String trueString, final String falseString) ---
    @Test
    void testToStringPrimitiveCustomValuesNormal() {
        assertEquals("yes", BooleanUtils.toString(true, "yes", "no"));
        assertEquals("no", BooleanUtils.toString(false, "yes", "no"));
    }

    @Test
    void testToStringPrimitiveCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(true, null, "no")); // trueString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(false, "yes", null)); // falseString is null
    }

    // --- toString(final Boolean bool, final String trueString, final String falseString, final String nullString) ---
    @Test
    void testToStringObjectCustomValuesNormal() {
        assertEquals("yes", BooleanUtils.toString(Boolean.TRUE, "yes", "no", "maybe"));
        assertEquals("no", BooleanUtils.toString(Boolean.FALSE, "yes", "no", "maybe"));
        assertEquals("maybe", BooleanUtils.toString(null, "yes", "no", "maybe"));
    }

    @Test
    void testToStringObjectCustomValuesFailure() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(Boolean.TRUE, null, "no", "maybe")); // trueString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(Boolean.FALSE, "yes", null, "maybe")); // falseString is null
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.toString(null, "yes", "no", null)); // nullString is null
    }

    // --- toStringOnOff(final boolean bool) ---
    @Test
    void testToStringOnOffPrimitiveNormal() {
        assertEquals("on", BooleanUtils.toStringOnOff(true));
        assertEquals("off", BooleanUtils.toStringOnOff(false));
    }

    // --- toStringOnOff(final Boolean bool) ---
    @Test
    void testToStringOnOffObjectNormal() {
        assertEquals("on", BooleanUtils.toStringOnOff(Boolean.TRUE));
        assertEquals("off", BooleanUtils.toStringOnOff(Boolean.FALSE));
    }

    @Test
    void testToStringOnOffObjectEdgeCases() {
        assertNull(BooleanUtils.toStringOnOff(null));
    }

    // --- toStringTrueFalse(final boolean bool) ---
    @Test
    void testToStringTrueFalsePrimitiveNormal() {
        assertEquals("true", BooleanUtils.toStringTrueFalse(true));
        assertEquals("false", BooleanUtils.toStringTrueFalse(false));
    }

    // --- toStringTrueFalse(final Boolean bool) ---
    @Test
    void testToStringTrueFalseObjectNormal() {
        assertEquals("true", BooleanUtils.toStringTrueFalse(Boolean.TRUE));
        assertEquals("false", BooleanUtils.toStringTrueFalse(Boolean.FALSE));
    }

    @Test
    void testToStringTrueFalseObjectEdgeCases() {
        assertNull(BooleanUtils.toStringTrueFalse(null));
    }

    // --- toStringYesNo(final boolean bool) ---
    @Test
    void testToStringYesNoPrimitiveNormal() {
        assertEquals("yes", BooleanUtils.toStringYesNo(true));
        assertEquals("no", BooleanUtils.toStringYesNo(false));
    }

    // --- toStringYesNo(final Boolean bool) ---
    @Test
    void testToStringYesNoObjectNormal() {
        assertEquals("yes", BooleanUtils.toStringYesNo(Boolean.TRUE));
        assertEquals("no", BooleanUtils.toStringYesNo(Boolean.FALSE));
    }

    @Test
    void testToStringYesNoObjectEdgeCases() {
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
    void testXorPrimitiveNormal() {
        assertTrue(BooleanUtils.xor(true, false, false));
        assertTrue(BooleanUtils.xor(false, true, false));
        assertFalse(BooleanUtils.xor(false, false, false));
        assertFalse(BooleanUtils.xor(true, true, false));
        assertFalse(BooleanUtils.xor(true, true, true));
    }

    @Test
    void testXorPrimitiveEdgeCases() {
        assertTrue(BooleanUtils.xor(true)); // Single true
        assertFalse(BooleanUtils.xor(false)); // Single false
        assertFalse(BooleanUtils.xor()); // Empty array, should be false (identity for XOR)
    }

    // --- xor(final Boolean... array) ---
    @Test
    void testXorObjectNormal() {
        assertTrue(BooleanUtils.xor(Boolean.TRUE, Boolean.FALSE, Boolean.FALSE));
        assertTrue(BooleanUtils.xor(Boolean.FALSE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.xor(Boolean.FALSE, Boolean.FALSE, Boolean.FALSE));
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.FALSE));
        assertFalse(BooleanUtils.xor(Boolean.TRUE, Boolean.TRUE, Boolean.TRUE));
    }

    @Test
    void testXorObjectEdgeCases() {
        assertTrue(BooleanUtils.xor(Boolean.TRUE)); // Single true
        assertFalse(BooleanUtils.xor(Boolean.FALSE)); // Single false
        assertFalse(BooleanUtils.xor()); // Empty array, should be false (identity for XOR)
    }

    @Test
    void testXorObjectFailureNullElement() {
        assertThrows(IllegalArgumentException.class, () -> BooleanUtils.xor(Boolean.TRUE, null, Boolean.FALSE));
    }
}