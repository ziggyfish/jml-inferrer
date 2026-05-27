package org.apache.commons.lang3.tuple.p3c;

import org.apache.commons.lang3.tuple.MutablePair;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class MutablePairTestP3CP3C {

    // --- emptyArray() tests ---

    @Test
    void testEmptyArray() {
        MutablePair<?, ?>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsImmutableReference() {
        MutablePair<?, ?>[] array1 = MutablePair.emptyArray();
        MutablePair<?, ?>[] array2 = MutablePair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same array instance for performance");
    }

    // --- of(L left, R right) tests ---

    @Test
    void testOfWithNonNullValues() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", 123);
        assertNotNull(pair, "of() should not return null for non-null inputs");
        assertEquals("Hello", pair.getLeft(), "Left value should match input");
        assertEquals(123, pair.getRight(), "Right value should match input");
    }

    @Test
    void testOfWithNullLeft() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair, "of() should not return null for null left input");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(123, pair.getRight(), "Right value should match input");
    }

    @Test
    void testOfWithNullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should not return null for null right input");
        assertEquals("Hello", pair.getLeft(), "Left value should match input");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithBothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "of() should not return null for both null inputs");
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
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 100);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for non-null entry");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertEquals(100, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfWithMapEntryNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 100);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for null key in entry");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(100, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfWithMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for null value in entry");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for both null in entry");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithNullMapEntry() {
        // JML spec does not explicitly forbid null Map.Entry, but it's a failure scenario
        // The current implementation throws NullPointerException.
        assertThrows(NullPointerException.class, () -> MutablePair.of(null),
                "of(null Map.Entry) should throw NullPointerException");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullWithNonNullValues() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Alpha", 1);
        assertNotNull(pair, "ofNonNull() should not return null for non-null inputs");
        assertEquals("Alpha", pair.getLeft(), "Left value should match input");
        assertEquals(1, pair.getRight(), "Right value should match input");
    }

    @Test
    void testOfNonNullWithNullLeft() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 1),
                "ofNonNull() should throw NullPointerException for null left value");
    }

    @Test
    void testOfNonNullWithNullRight() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Beta", null),
                "ofNonNull() should throw NullPointerException for null right value");
    }

    @Test
    void testOfNonNullWithBothNull() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null values");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullWithMapEntryNonNullValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Gamma", 2);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "ofNonNull(Map.Entry) should not return null for non-null entry with non-null key/value");
        assertEquals("Gamma", pair.getLeft(), "Left value should match entry's key");
        assertEquals(2, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfNonNullWithMapEntryNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 2);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null key in entry");
    }

    @Test
    void testOfNonNullWithMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Delta", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null value in entry");
    }

    @Test
    void testOfNonNullWithMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for both null in entry");
    }

    @Test
    void testOfNonNullWithNullMapEntry() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null),
                "ofNonNull(null Map.Entry) should throw NullPointerException");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeftNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 10);
        assertEquals("LeftValue", pair.getLeft(), "getLeft() should return the correct non-null value");
    }

    @Test
    void testGetLeftNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 10);
        assertNull(pair.getLeft(), "getLeft() should return null if left value is null");
    }

    // --- getRight() tests ---

    @Test
    void testGetRightNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 20);
        assertEquals(20, pair.getRight(), "getRight() should return the correct non-null value");
    }

    @Test
    void testGetRightNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight(), "getRight() should return null if right value is null");
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftFromNonNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 10);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
        assertEquals(10, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 10);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update null left to non-null");
    }

    @Test
    void testSetLeftFromNonNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 10);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should update non-null left to null");
    }

    @Test
    void testSetLeftFromNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 10);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should keep left as null");
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightFromNonNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(20);
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
        assertEquals(20, pair.getRight(), "setRight() should update the right value");
    }

    @Test
    void testSetRightFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        pair.setRight(20);
        assertEquals(20, pair.getRight(), "setRight() should update null right to non-null");
    }

    @Test
    void testSetRightFromNonNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(null);
        assertNull(pair.getRight(), "setRight() should update non-null right to null");
    }

    @Test
    void testSetRightFromNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        pair.setRight(null);
        assertNull(pair.getRight(), "setRight() should keep right as null");
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueFromNonNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(200);
        assertEquals(100, oldValue, "setValue() should return the old right value");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(200, pair.getRight(), "setValue() should update the right value");
    }

    @Test
    void testSetValueFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(200);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(200, pair.getRight(), "setValue() should update null right to non-null");
    }

    @Test
    void testSetValueFromNonNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(null);
        assertEquals(100, oldValue, "setValue() should return the old right value");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertNull(pair.getRight(), "setValue() should update non-null right to null");
    }

    @Test
    void testSetValueFromNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(null);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertNull(pair.getRight(), "setValue() should keep right as null");
    }

    // --- toString() and equals()/hashCode() for completeness and general behavior ---

    @Test
    void testToString() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        assertEquals("(A,1)", pair.toString());

        MutablePair<String, Integer> nullPair = MutablePair.of(null, null);
        assertEquals("(null,null)", nullPair.toString());

        MutablePair<String, Integer> leftNull = MutablePair.of(null, 1);
        assertEquals("(null,1)", leftNull.toString());

        MutablePair<String, Integer> rightNull = MutablePair.of("A", null);
        assertEquals("(A,null)", rightNull.toString());
    }

    @Test
    void testEqualsAndHashCode() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair3 = MutablePair.of("B", 1);
        MutablePair<String, Integer> pair4 = MutablePair.of("A", 2);
        MutablePair<String, Integer> pair5 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair6 = MutablePair.of(null, 1);

        assertEquals(pair1, pair2);
        assertEquals(pair1.hashCode(), pair2.hashCode());
        assertNotEquals(pair1, pair3);
        assertNotEquals(pair1, pair4);
        assertNotEquals(pair1, null);
        assertNotEquals(pair1, "not a pair");
        assertEquals(pair5, pair6);
        assertEquals(pair5.hashCode(), pair6.hashCode());

        // Test mutability affects equality
        MutablePair<String, Integer> mutablePair = MutablePair.of("X", 10);
        MutablePair<String, Integer> initialCopy = MutablePair.of("X", 10);
        assertEquals(mutablePair, initialCopy);
        mutablePair.setLeft("Y");
        assertNotEquals(mutablePair, initialCopy);
    }
}