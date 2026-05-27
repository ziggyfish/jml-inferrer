package org.apache.commons.lang3.tuple.p3;

import org.apache.commons.lang3.function.FailableBiConsumer;
import org.apache.commons.lang3.function.FailableBiFunction;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

class PairTestP3P3 {

    // --- emptyArray() tests ---

    /**
     * Tests that emptyArray() returns a non-null, empty array.
     */
    @Test
    void testEmptyArray_basic() {
        Pair<String, Integer>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray);
        assertEquals(0, emptyArray.length);
    }

    /**
     * Tests that emptyArray() returns the same instance each time (singleton pattern).
     */
    @Test
    void testEmptyArray_singleton() {
        Pair<String, Integer>[] array1 = Pair.emptyArray();
        Pair<Double, Boolean>[] array2 = Pair.emptyArray();
        assertSame(array1, array2);
    }

    // --- of(L left, R right) tests ---

    /**
     * Tests of() with non-null values.
     */
    @Test
    void testOf_nonNullValues() {
        Pair<String, Integer> pair = Pair.of("hello", 123);
        assertNotNull(pair);
        assertEquals("hello", pair.getLeft());
        assertEquals(123, pair.getRight());
        assertEquals("hello", pair.getKey());
        assertEquals(123, pair.getValue());
    }

    /**
     * Tests of() with null left value.
     */
    @Test
    void testOf_nullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    /**
     * Tests of() with null right value.
     */
    @Test
    void testOf_nullRight() {
        Pair<String, Integer> pair = Pair.of("hello", null);
        assertNotNull(pair);
        assertEquals("hello", pair.getLeft());
        assertNull(pair.getRight());
    }

    /**
     * Tests of() with both null values.
     */
    @Test
    void testOf_bothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    /**
     * Tests of() with different types.
     */
    @Test
    void testOf_differentTypes() {
        Pair<Double, Boolean> pair = Pair.of(3.14, true);
        assertNotNull(pair);
        assertEquals(3.14, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---

    /**
     * Tests of(Map.Entry) with a non-null entry.
     */
    @Test
    void testOfEntry_nonNullEntry() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("key", pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    /**
     * Tests of(Map.Entry) with a null entry.
     */
    @Test
    void testOfEntry_nullEntry() {
        assertThrows(IllegalArgumentException.class, () -> Pair.of((Map.Entry<String, Integer>) null));
    }

    /**
     * Tests of(Map.Entry) with an entry containing null key.
     */
    @Test
    void testOfEntry_nullKeyInEntry() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    /**
     * Tests of(Map.Entry) with an entry containing null value.
     */
    @Test
    void testOfEntry_nullValueInEntry() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("key", pair.getLeft());
        assertNull(pair.getRight());
    }

    /**
     * Tests of(Map.Entry) with an entry containing both null key and value.
     */
    @Test
    void testOfEntry_bothNullInEntry() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    // --- ofNonNull(L left, R right) tests ---

    /**
     * Tests ofNonNull() with non-null values.
     */
    @Test
    void testOfNonNull_nonNullValues() {
        Pair<String, Integer> pair = Pair.ofNonNull("hello", 123);
        assertNotNull(pair);
        assertEquals("hello", pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    /**
     * Tests ofNonNull() with null left value, expecting NullPointerException.
     */
    @Test
    void testOfNonNull_nullLeft() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 123));
    }

    /**
     * Tests ofNonNull() with null right value, expecting NullPointerException.
     */
    @Test
    void testOfNonNull_nullRight() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("hello", null));
    }

    /**
     * Tests ofNonNull() with both null values, expecting NullPointerException.
     */
    @Test
    void testOfNonNull_bothNull() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null));
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---

    /**
     * Tests accept() with a successful consumer.
     */
    @Test
    void testAccept_success() throws IOException {
        Pair<String, Integer> pair = Pair.of("test", 10);
        AtomicReference<String> leftRef = new AtomicReference<>();
        AtomicReference<Integer> rightRef = new AtomicReference<>();

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            leftRef.set(l);
            rightRef.set(r);
        };

        pair.accept(consumer);

        assertEquals("test", leftRef.get());
        assertEquals(10, rightRef.get());
    }

    /**
     * Tests accept() with a consumer that throws an exception.
     */
    @Test
    void testAccept_throwsException() {
        Pair<String, Integer> pair = Pair.of("test", 10);

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Consumer failed");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.accept(consumer));
        assertEquals("Consumer failed", thrown.getMessage());
    }

    /**
     * Tests accept() with a null consumer, expecting NullPointerException.
     */
    @Test
    void testAccept_nullConsumer() {
        Pair<String, Integer> pair = Pair.of("test", 10);
        assertThrows(NullPointerException.class, () -> pair.accept(null));
    }

    /**
     * Tests accept() with null values in the pair.
     */
    @Test
    void testAccept_nullPairValues() throws IOException {
        Pair<String, Integer> pair = Pair.of(null, null);
        AtomicReference<String> leftRef = new AtomicReference<>();
        AtomicReference<Integer> rightRef = new AtomicReference<>();

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            leftRef.set(l);
            rightRef.set(r);
        };

        pair.accept(consumer);

        assertNull(leftRef.get());
        assertNull(rightRef.get());
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---

    /**
     * Tests apply() with a successful function.
     */
    @Test
    void testApply_success() throws IOException {
        Pair<String, Integer> pair = Pair.of("value", 5);

        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> l + "_" + r;

        String result = pair.apply(function);
        assertEquals("value_5", result);
    }

    /**
     * Tests apply() with a function that throws an exception.
     */
    @Test
    void testApply_throwsException() {
        Pair<String, Integer> pair = Pair.of("value", 5);

        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Function failed");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.apply(function));
        assertEquals("Function failed", thrown.getMessage());
    }

    /**
     * Tests apply() with a null function, expecting NullPointerException.
     */
    @Test
    void testApply_nullFunction() {
        Pair<String, Integer> pair = Pair.of("value", 5);
        assertThrows(NullPointerException.class, () -> pair.apply(null));
    }

    /**
     * Tests apply() with null values in the pair.
     */
    @Test
    void testApply_nullPairValues() throws IOException {
        Pair<String, Integer> pair = Pair.of(null, null);

        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            if (l == null && r == null) {
                return "both_null";
            }
            return "not_both_null";
        };

        String result = pair.apply(function);
        assertEquals("both_null", result);
    }

    /**
     * Tests apply() with a function returning null.
     */
    @Test
    void testApply_functionReturnsNull() throws IOException {
        Pair<String, Integer> pair = Pair.of("value", 5);

        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> null;

        String result = pair.apply(function);
        assertNull(result);
    }

    // --- compareTo(Pair<L, R> other) tests ---

    /**
     * Tests compareTo() with equal pairs.
     */
    @Test
    void testCompareTo_equalPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(0, pair1.compareTo(pair2));
    }

    /**
     * Tests compareTo() where left values are different (pair1 < pair2).
     */
    @Test
    void testCompareTo_leftLess() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertTrue(pair1.compareTo(pair2) < 0);
    }

    /**
     * Tests compareTo() where left values are different (pair1 > pair2).
     */
    @Test
    void testCompareTo_leftGreater() {
        Pair<String, Integer> pair1 = Pair.of("B", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.compareTo(pair2) > 0);
    }

    /**
     * Tests compareTo() where left values are equal and right values are different (pair1 < pair2).
     */
    @Test
    void testCompareTo_rightLess() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 2);
        assertTrue(pair1.compareTo(pair2) < 0);
    }

    /**
     * Tests compareTo() where left values are equal and right values are different (pair1 > pair2).
     */
    @Test
    void testCompareTo_rightGreater() {
        Pair<String, Integer> pair1 = Pair.of("A", 2);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.compareTo(pair2) > 0);
    }

    /**
     * Tests compareTo() with null left values.
     */
    @Test
    void testCompareTo_nullLeftValues() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 1);
        assertEquals(0, pair1.compareTo(pair2));

        Pair<String, Integer> pair3 = Pair.of(null, 1);
        Pair<String, Integer> pair4 = Pair.of("A", 1);
        assertTrue(pair3.compareTo(pair4) < 0); // null is considered less than non-null

        Pair<String, Integer> pair5 = Pair.of("A", 1);
        Pair<String, Integer> pair6 = Pair.of(null, 1);
        assertTrue(pair5.compareTo(pair6) > 0); // non-null is considered greater than null
    }

    /**
     * Tests compareTo() with null right values.
     */
    @Test
    void testCompareTo_nullRightValues() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        assertEquals(0, pair1.compareTo(pair2));

        Pair<String, Integer> pair3 = Pair.of("A", null);
        Pair<String, Integer> pair4 = Pair.of("A", 1);
        assertTrue(pair3.compareTo(pair4) < 0); // null is considered less than non-null

        Pair<String, Integer> pair5 = Pair.of("A", 1);
        Pair<String, Integer> pair6 = Pair.of("A", null);
        assertTrue(pair5.compareTo(pair6) > 0); // non-null is considered greater than null
    }

    /**
     * Tests compareTo() with both null values.
     */
    @Test
    void testCompareTo_bothNullValues() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertEquals(0, pair1.compareTo(pair2));
    }

    /**
     * Tests compareTo() with a null 'other' pair, expecting NullPointerException.
     */
    @Test
    void testCompareTo_nullOther() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> pair.compareTo(null));
    }

    /**
     * Tests compareTo() with non-comparable types (should compile but might throw ClassCastException at runtime if not handled by Pair's internal comparator).
     * Pair's default implementation uses Comparable. If types are not Comparable, it will throw.
     */
    @Test
    void testCompareTo_nonComparableTypes() {
        // This test relies on the internal implementation of Pair's compareTo,
        // which uses ComparableComparator.nullLow().
        // If the types are not Comparable, a ClassCastException will be thrown.
        // We simulate this by using a custom non-comparable class.
        class NonComparable {
            int value;
            NonComparable(int value) { this.value = value; }
            @Override public String toString() { return String.valueOf(value); }
        }

        Pair<NonComparable, Integer> pair1 = Pair.of(new NonComparable(1), 1);
        Pair<NonComparable, Integer> pair2 = Pair.of(new NonComparable(2), 1);

        // The default implementation of Pair.compareTo expects L and R to be Comparable.
        // If they are not, it will throw a ClassCastException.
        assertThrows(ClassCastException.class, () -> pair1.compareTo(pair2));

        // However, if the types are comparable, it works as expected.
        Pair<Integer, Integer> intPair1 = Pair.of(1, 1);
        Pair<Integer, Integer> intPair2 = Pair.of(2, 1);
        assertTrue(intPair1.compareTo(intPair2) < 0);
    }


    // --- equals(Object obj) tests ---

    /**
     * Tests equals() with identical pairs.
     */
    @Test
    void testEquals_identical() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertTrue(pair.equals(pair));
    }

    /**
     * Tests equals() with equal pairs.
     */
    @Test
    void testEquals_equal() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
    }

    /**
     * Tests equals() with different left values.
     */
    @Test
    void testEquals_differentLeft() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertFalse(pair1.equals(pair2));
    }

    /**
     * Tests equals() with different right values.
     */
    @Test
    void testEquals_differentRight() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 2);
        assertFalse(pair1.equals(pair2));
    }

    /**
     * Tests equals() with different both values.
     */
    @Test
    void testEquals_differentBoth() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 2);
        assertFalse(pair1.equals(pair2));
    }

    /**
     * Tests equals() with null left values.
     */
    @Test
    void testEquals_nullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 1);
        assertTrue(pair1.equals(pair2));

        Pair<String, Integer> pair3 = Pair.of(null, 1);
        Pair<String, Integer> pair4 = Pair.of("A", 1);
        assertFalse(pair3.equals(pair4));
    }

    /**
     * Tests equals() with null right values.
     */
    @Test
    void testEquals_nullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        assertTrue(pair1.equals(pair2));

        Pair<String, Integer> pair3 = Pair.of("A", null);
        Pair<String, Integer> pair4 = Pair.of("A", 1);
        assertFalse(pair3.equals(pair4));
    }

    /**
     * Tests equals() with both null values.
     */
    @Test
    void testEquals_bothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertTrue(pair1.equals(pair2));
    }

    /**
     * Tests equals() with a null object.
     */
    @Test
    void testEquals_nullObject() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertFalse(pair.equals(null));
    }

    /**
     * Tests equals() with an object of a different class.
     */
    @Test
    void testEquals_differentClass() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        String notAPair = "Not a pair";
        assertFalse(pair.equals(notAPair));
    }

    /**
     * Tests equals() with a Map.Entry that has the same values.
     * Note: Pair does not implement Map.Entry, so they should not be equal.
     */
    @Test
    void testEquals_mapEntry() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("A", 1);
        assertFalse(pair.equals(entry));
    }

    // --- getKey(), getLeft(), getRight(), getValue() tests ---

    /**
     * Tests getKey() and getLeft() with non-null values.
     */
    @Test
    void testGetLeftAndKey_nonNull() {
        Pair<String, Integer> pair = Pair.of("key", 10);
        assertEquals("key", pair.getLeft());
        assertEquals("key", pair.getKey());
    }

    /**
     * Tests getKey() and getLeft() with null left value.
     */
    @Test
    void testGetLeftAndKey_null() {
        Pair<String, Integer> pair = Pair.of(null, 10);
        assertNull(pair.getLeft());
        assertNull(pair.getKey());
    }

    /**
     * Tests getRight() and getValue() with non-null values.
     */
    @Test
    void testGetRightAndValue_nonNull() {
        Pair<String, Integer> pair = Pair.of("key", 10);
        assertEquals(10, pair.getRight());
        assertEquals(10, pair.getValue());
    }

    /**
     * Tests getRight() and getValue() with null right value.
     */
    @Test
    void testGetRightAndValue_null() {
        Pair<String, Integer> pair = Pair.of("key", null);
        assertNull(pair.getRight());
        assertNull(pair.getValue());
    }

    // --- hashCode() tests ---

    /**
     * Tests hashCode() for equal pairs.
     */
    @Test
    void testHashCode_equalPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(pair1.hashCode(), pair2.hashCode());
    }

    /**
     * Tests hashCode() for different pairs.
     */
    @Test
    void testHashCode_differentPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 2);
        assertNotEquals(pair1.hashCode(), pair2.hashCode());
    }

    /**
     * Tests hashCode() with null left value.
     */
    @Test
    void testHashCode_nullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 1);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        Pair<String, Integer> pair3 = Pair.of(null, 1);
        Pair<String, Integer> pair4 = Pair.of("A", 1);
        assertNotEquals(pair3.hashCode(), pair4.hashCode());
    }

    /**
     * Tests hashCode() with null right value.
     */
    @Test
    void testHashCode_nullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        Pair<String, Integer> pair3 = Pair.of("A", null);
        Pair<String, Integer> pair4 = Pair.of("A", 1);
        assertNotEquals(pair3.hashCode(), pair4.hashCode());
    }

    /**
     * Tests hashCode() with both null values.
     */
    @Test
    void testHashCode_bothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertEquals(pair1.hashCode(), pair2.hashCode());
    }

    // --- toString() tests ---

    /**
     * Tests toString() with non-null values.
     */
    @Test
    void testToString_nonNull() {
        Pair<String, Integer> pair = Pair.of("hello", 123);
        assertEquals("(hello,123)", pair.toString());
    }

    /**
     * Tests toString() with null left value.
     */
    @Test
    void testToString_nullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertEquals("(null,123)", pair.toString());
    }

    /**
     * Tests toString() with null right value.
     */
    @Test
    void testToString_nullRight() {
        Pair<String, Integer> pair = Pair.of("hello", null);
        assertEquals("(hello,null)", pair.toString());
    }

    /**
     * Tests toString() with both null values.
     */
    @Test
    void testToString_bothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("(null,null)", pair.toString());
    }

    /**
     * Tests toString() with empty strings.
     */
    @Test
    void testToString_emptyStrings() {
        Pair<String, String> pair = Pair.of("", "");
        assertEquals("(,)", pair.toString());
    }

    // --- toString(String format) tests ---

    /**
     * Tests toString(format) with a valid format string and non-null values.
     */
    @Test
    void testToStringFormat_validFormatNonNull() {
        Pair<String, Integer> pair = Pair.of("left", 42);
        assertEquals("Left: left, Right: 42", pair.toString("Left: %L, Right: %R"));
        assertEquals("Key: left, Value: 42", pair.toString("Key: %K, Value: %V"));
    }

    /**
     * Tests toString(format) with a valid format string and null values.
     */
    @Test
    void testToStringFormat_validFormatNullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("Left: null, Right: null", pair.toString("Left: %L, Right: %R"));
        assertEquals("Key: null, Value: null", pair.toString("Key: %K, Value: %V"));
    }

    /**
     * Tests toString(format) with an empty format string.
     */
    @Test
    void testToStringFormat_emptyFormat() {
        Pair<String, Integer> pair = Pair.of("left", 42);
        assertEquals("", pair.toString(""));
    }

    /**
     * Tests toString(format) with a format string containing only literal text.
     */
    @Test
    void testToStringFormat_literalText() {
        Pair<String, Integer> pair = Pair.of("left", 42);
        assertEquals("This is a pair", pair.toString("This is a pair"));
    }

    /**
     * Tests toString(format) with a format string containing unknown format specifiers.
     * The specification implies that only %L, %R, %K, %V are handled. Others should be ignored or passed through.
     * Commons Lang's String.replace() behavior is to leave unknown specifiers as is.
     */
    @Test
    void testToStringFormat_unknownSpecifiers() {
        Pair<String, Integer> pair = Pair.of("left", 42);
        assertEquals("Left: left, Right: 42, Unknown: %X", pair.toString("Left: %L, Right: %R, Unknown: %X"));
    }

    /**
     * Tests toString(format) with a null format string, expecting NullPointerException.
     */
    @Test
    void testToStringFormat_nullFormat() {
        Pair<String, Integer> pair = Pair.of("left", 42);
        assertThrows(NullPointerException.class, () -> pair.toString(null));
    }

    /**
     * Tests toString(format) with a format string that uses the same specifier multiple times.
     */
    @Test
    void testToStringFormat_repeatedSpecifiers() {
        Pair<String, Integer> pair = Pair.of("left", 42);
        assertEquals("left and left, 42 and 42", pair.toString("%L and %L, %R and %R"));
    }
}