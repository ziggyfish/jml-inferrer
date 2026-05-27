package org.apache.commons.lang3.tuple.p3;

import org.apache.commons.lang3.tuple.MutablePair;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class MutablePairTestP3P3 {

    // --- emptyArray() tests ---

    @Test
    void testEmptyArray() {
        MutablePair<String, Integer>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsImmutable() {
        MutablePair<String, Integer>[] array1 = MutablePair.emptyArray();
        MutablePair<String, Integer>[] array2 = MutablePair.emptyArray();
        assertNotSame(array1, array2, "emptyArray() should return a new array instance each time");
    }

    // --- of(L left, R right) tests ---

    @Test
    void testOfWithNonNullValues() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", 123);
        assertNotNull(pair, "of() should return a non-null pair");
        assertEquals("Hello", pair.getLeft(), "Left value should match constructor input");
        assertEquals(123, pair.getRight(), "Right value should match constructor input");
    }

    @Test
    void testOfWithNullLeft() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair, "of() should return a non-null pair even with null left");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(123, pair.getRight(), "Right value should match constructor input");
    }

    @Test
    void testOfWithNullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should return a non-null pair even with null right");
        assertEquals("Hello", pair.getLeft(), "Left value should match constructor input");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithBothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "of() should return a non-null pair even with both null");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithDifferentTypes() {
        MutablePair<Integer, Boolean> pair = MutablePair.of(42, true);
        assertEquals(42, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfWithMapEntryNonNullValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should return a non-null pair");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertEquals(456, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfWithMapEntryNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should return a non-null pair even with null key");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(456, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfWithMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should return a non-null pair even with null value");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should return a non-null pair even with both null");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithMapEntryNullEntry() {
        // JML specification for of(Map.Entry) does not explicitly forbid null entry.
        // It's common for such methods to throw NPE if the input object itself is null.
        // However, if it's allowed, it should create a pair of nulls.
        MutablePair<String, Integer> pair = MutablePair.of((Map.Entry<String, Integer>) null);
        assertNotNull(pair, "of(null Map.Entry) should return a non-null pair");
        assertNull(pair.getLeft(), "Left value should be null when entry is null");
        assertNull(pair.getRight(), "Right value should be null when entry is null");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullWithNonNullValues() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Alpha", 789);
        assertNotNull(pair, "ofNonNull() should return a non-null pair");
        assertEquals("Alpha", pair.getLeft(), "Left value should match constructor input");
        assertEquals(789, pair.getRight(), "Right value should match constructor input");
    }

    @Test
    void testOfNonNullWithNullLeftThrowsNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NPE for null left value");
    }

    @Test
    void testOfNonNullWithNullRightThrowsNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Alpha", null),
                "ofNonNull() should throw NPE for null right value");
    }

    @Test
    void testOfNonNullWithBothNullThrowsNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NPE for both null values");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullWithMapEntryNonNullValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Gamma", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "ofNonNull(Map.Entry) should return a non-null pair");
        assertEquals("Gamma", pair.getLeft(), "Left value should match entry's key");
        assertEquals(101, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfNonNullWithMapEntryNullKeyThrowsNPE() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NPE for null key");
    }

    @Test
    void testOfNonNullWithMapEntryNullValueThrowsNPE() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Gamma", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NPE for null value");
    }

    @Test
    void testOfNonNullWithMapEntryBothNullThrowsNPE() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NPE for both null key and value");
    }

    @Test
    void testOfNonNullWithMapEntryNullEntryThrowsNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull((Map.Entry<String, Integer>) null),
                "ofNonNull(null Map.Entry) should throw NPE");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeftNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals("LeftValue", pair.getLeft(), "getLeft() should return the correct non-null value");
    }

    @Test
    void testGetLeftNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        assertNull(pair.getLeft(), "getLeft() should return null if left value is null");
    }

    // --- getRight() tests ---

    @Test
    void testGetRightNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals(1, pair.getRight(), "getRight() should return the correct non-null value");
    }

    @Test
    void testGetRightNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight(), "getRight() should return null if right value is null");
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should allow setting left value to null");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("SameLeft", 1);
        pair.setLeft("SameLeft");
        assertEquals("SameLeft", pair.getLeft(), "setLeft() should work even if value is the same");
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(20);
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
        assertEquals(20, pair.getRight(), "setRight() should update the right value");
    }

    @Test
    void testSetRightToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(null);
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
        assertNull(pair.getRight(), "setRight() should allow setting right value to null");
    }

    @Test
    void testSetRightToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(10);
        assertEquals(10, pair.getRight(), "setRight() should work even if value is the same");
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 100);
        Integer oldValue = pair.setValue(200);
        assertEquals(100, oldValue, "setValue() should return the old right value");
        assertEquals("Left", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(200, pair.getRight(), "setValue() should update the right value");
    }

    @Test
    void testSetValueToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 100);
        Integer oldValue = pair.setValue(null);
        assertEquals(100, oldValue, "setValue() should return the old right value even when setting to null");
        assertEquals("Left", pair.getLeft(), "setValue() should not affect the left value");
        assertNull(pair.getRight(), "setValue() should allow setting right value to null");
    }

    @Test
    void testSetValueWhenRightWasNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        Integer oldValue = pair.setValue(300);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals("Left", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(300, pair.getRight(), "setValue() should update the right value");
    }

    @Test
    void testSetValueToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 100);
        Integer oldValue = pair.setValue(100);
        assertEquals(100, oldValue, "setValue() should return the old right value even if it's the same");
        assertEquals(100, pair.getRight(), "setValue() should work even if value is the same");
    }

    // --- toString() and equals()/hashCode() (good practice, though not explicitly in JML) ---

    @Test
    void testToString() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        assertEquals("(A,1)", pair.toString());

        MutablePair<String, Integer> nullPair = MutablePair.of(null, null);
        assertEquals("(null,null)", nullPair.toString());

        MutablePair<String, Integer> mixedPair = MutablePair.of("B", null);
        assertEquals("(B,null)", mixedPair.toString());
    }

    @Test
    void testEqualsAndHashCode() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair3 = MutablePair.of("B", 1);
        MutablePair<String, Integer> pair4 = MutablePair.of("A", 2);
        MutablePair<String, Integer> pair5 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair6 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair7 = MutablePair.of("A", null);
        MutablePair<String, Integer> pair8 = MutablePair.of("A", null);

        // Reflexivity
        assertEquals(pair1, pair1);

        // Symmetry
        assertEquals(pair1, pair2);
        assertEquals(pair2, pair1);

        // Transitivity (not fully tested here, but implied by symmetry and consistency)
        // Consistency
        assertEquals(pair1.hashCode(), pair2.hashCode());

        // Inequality
        assertNotEquals(pair1, pair3);
        assertNotEquals(pair1, pair4);
        assertNotEquals(pair1, null);
        assertNotEquals(pair1, "NotAPair");

        // Null values
        assertEquals(pair5, pair6);
        assertEquals(pair5.hashCode(), pair6.hashCode());
        assertEquals(pair7, pair8);
        assertEquals(pair7.hashCode(), pair8.hashCode());
        assertNotEquals(pair1, pair5);
        assertNotEquals(pair1, pair7);
    }
}