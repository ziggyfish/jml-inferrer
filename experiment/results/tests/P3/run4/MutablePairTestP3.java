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
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    void testOfWithMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfWithMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfWithMapEntryNullEntry() {
        // JML specification does not explicitly forbid null entry, but it's a common edge case
        // The current implementation of MutablePair.of(Map.Entry) handles null entry by throwing NPE
        assertThrows(NullPointerException.class, () -> MutablePair.of(null),
                "of(null Map.Entry) should throw NullPointerException");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullWithNonNullValues() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Alpha", 789);
        assertNotNull(pair);
        assertEquals("Alpha", pair.getLeft());
        assertEquals(789, pair.getRight());
    }

    @Test
    void testOfNonNullWithNullLeft() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNullWithNullRight() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Alpha", null),
                "ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNullWithBothNull() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullWithMapEntryNonNullValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Beta", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair);
        assertEquals("Beta", pair.getLeft());
        assertEquals(101, pair.getRight());
    }

    @Test
    void testOfNonNullWithMapEntryNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null key");
    }

    @Test
    void testOfNonNullWithMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Beta", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null value");
    }

    @Test
    void testOfNonNullWithMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for both null");
    }

    @Test
    void testOfNonNullWithMapEntryNullEntry() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null),
                "ofNonNull(null Map.Entry) should throw NullPointerException");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeftNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals("LeftValue", pair.getLeft());
    }

    @Test
    void testGetLeftNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        assertNull(pair.getLeft());
    }

    @Test
    void testGetLeftAfterSetLeft() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft());
    }

    // --- getRight() tests ---

    @Test
    void testGetRightNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals(1, pair.getRight());
    }

    @Test
    void testGetRightNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight());
    }

    @Test
    void testGetRightAfterSetRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setRight(2);
        assertEquals(2, pair.getRight());
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 10);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft should update the left value");
        assertEquals(10, pair.getRight(), "setLeft should not affect the right value");
    }

    @Test
    void testSetLeftNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 10);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft should allow setting null for left value");
        assertEquals(10, pair.getRight(), "setLeft should not affect the right value");
    }

    @Test
    void testSetLeftToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("SameLeft", 10);
        pair.setLeft("SameLeft");
        assertEquals("SameLeft", pair.getLeft());
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(30);
        assertEquals("Left", pair.getLeft(), "setRight should not affect the left value");
        assertEquals(30, pair.getRight(), "setRight should update the right value");
    }

    @Test
    void testSetRightNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(null);
        assertEquals("Left", pair.getLeft(), "setRight should not affect the left value");
        assertNull(pair.getRight(), "setRight should allow setting null for right value");
    }

    @Test
    void testSetRightToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(20);
        assertEquals(20, pair.getRight());
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(200);
        assertEquals(100, oldValue, "setValue should return the old right value");
        assertEquals("Key", pair.getLeft(), "setValue should not affect the left value");
        assertEquals(200, pair.getRight(), "setValue should update the right value");
    }

    @Test
    void testSetValueNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(null);
        assertEquals(100, oldValue, "setValue should return the old right value even when setting null");
        assertEquals("Key", pair.getLeft(), "setValue should not affect the left value");
        assertNull(pair.getRight(), "setValue should allow setting null for right value");
    }

    @Test
    void testSetValueFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(500);
        assertNull(oldValue, "setValue should return null if old right value was null");
        assertEquals("Key", pair.getLeft());
        assertEquals(500, pair.getRight());
    }

    @Test
    void testSetValueFromNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(null);
        assertNull(oldValue, "setValue should return null if old right value was null");
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    // --- General behavior and toString/equals/hashCode (not in spec, but good practice) ---

    @Test
    void testToString() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        assertEquals("(A,1)", pair.toString());

        MutablePair<String, Integer> nullPair = MutablePair.of(null, null);
        assertEquals("(null,null)", nullPair.toString());

        MutablePair<String, Integer> leftNullPair = MutablePair.of(null, 1);
        assertEquals("(null,1)", leftNullPair.toString());

        MutablePair<String, Integer> rightNullPair = MutablePair.of("A", null);
        assertEquals("(A,null)", rightNullPair.toString());
    }

    @Test
    void testEqualsAndHashCode() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair3 = MutablePair.of("B", 1);
        MutablePair<String, Integer> pair4 = MutablePair.of("A", 2);
        MutablePair<String, Integer> pair5 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair6 = MutablePair.of(null, 1);

        // Equals
        assertEquals(pair1, pair2, "Equal pairs should be equal");
        assertNotEquals(pair1, pair3, "Different left values should make pairs unequal");
        assertNotEquals(pair1, pair4, "Different right values should make pairs unequal");
        assertNotEquals(pair1, null, "Pair should not be equal to null");
        assertNotEquals(pair1, "A string", "Pair should not be equal to different type");
        assertEquals(pair5, pair6, "Pairs with null left should be equal if right is equal");

        // HashCode
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Equal pairs should have equal hash codes");
        assertNotEquals(pair1.hashCode(), pair3.hashCode(), "Different left values should result in different hash codes");
        assertNotEquals(pair1.hashCode(), pair4.hashCode(), "Different right values should result in different hash codes");
        assertEquals(pair5.hashCode(), pair6.hashCode(), "Pairs with null left should have equal hash codes if right is equal");
    }

    @Test
    void testEqualsAndHashCodeWithNulls() {
        MutablePair<String, Integer> pair1 = MutablePair.of(null, null);
        MutablePair<String, Integer> pair2 = MutablePair.of(null, null);
        MutablePair<String, Integer> pair3 = MutablePair.of("A", null);
        MutablePair<String, Integer> pair4 = MutablePair.of(null, 1);

        assertEquals(pair1, pair2);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        assertNotEquals(pair1, pair3);
        assertNotEquals(pair1, pair4);
    }
}