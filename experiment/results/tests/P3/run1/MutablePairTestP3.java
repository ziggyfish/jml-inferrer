package org.apache.commons.lang3.tuple.p3;

import org.apache.commons.lang3.tuple.MutablePair;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

public class MutablePairTestP3P3 {

    // --- emptyArray() tests ---

    @Test
    void testEmptyArray() {
        MutablePair<String, Integer>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsImmutable() {
        MutablePair<String, Integer>[] emptyArray1 = MutablePair.emptyArray();
        MutablePair<String, Integer>[] emptyArray2 = MutablePair.emptyArray();
        assertSame(emptyArray1, emptyArray2, "emptyArray() should return the same instance for performance");
    }

    // --- of(L left, R right) tests ---

    @Test
    void testOfNormalValues() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", 123);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    @Test
    void testOfNullLeft() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    @Test
    void testOfNullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfBothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfDifferentTypes() {
        MutablePair<Integer, Boolean> pair = MutablePair.of(42, true);
        assertNotNull(pair);
        assertEquals(42, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfMapEntryNormalValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    void testOfMapEntryNullLeft() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    void testOfMapEntryNullRight() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryNullEntry() {
        // JML specification does not explicitly forbid null entry, but it's a common failure scenario.
        // The current implementation of MutablePair.of(Map.Entry) handles it by creating a pair of nulls.
        MutablePair<String, Integer> pair = MutablePair.of((Map.Entry<String, Integer>) null);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullNormalValues() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Non-null", 789);
        assertNotNull(pair);
        assertEquals("Non-null", pair.getLeft());
        assertEquals(789, pair.getRight());
    }

    @Test
    void testOfNonNullNullLeft() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNullNullRight() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Non-null", null),
                "ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNullBothNull() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullMapEntryNormalValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("EntryKey", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair);
        assertEquals("EntryKey", pair.getLeft());
        assertEquals(101, pair.getRight());
    }

    @Test
    void testOfNonNullMapEntryNullLeft() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException if entry's left is null");
    }

    @Test
    void testOfNonNullMapEntryNullRight() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("EntryKey", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException if entry's right is null");
    }

    @Test
    void testOfNonNullMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException if entry's left and right are null");
    }

    @Test
    void testOfNonNullMapEntryNullEntry() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull((Map.Entry<String, Integer>) null),
                "ofNonNull(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeftNormal() {
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
    void testGetRightNormal() {
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
    void testSetLeftNormal() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft());
        assertEquals(1, pair.getRight(), "setLeft should not change right value");
    }

    @Test
    void testSetLeftToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft(null);
        assertNull(pair.getLeft());
        assertEquals(1, pair.getRight(), "setLeft should not change right value");
    }

    @Test
    void testSetLeftFromNullToValue() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft());
        assertEquals(1, pair.getRight(), "setLeft should not change right value");
    }

    @Test
    void testSetLeftToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Same", 1);
        pair.setLeft("Same");
        assertEquals("Same", pair.getLeft());
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightNormal() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        pair.setRight(2);
        assertEquals(2, pair.getRight());
        assertEquals("Left", pair.getLeft(), "setRight should not change left value");
    }

    @Test
    void testSetRightToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        pair.setRight(null);
        assertNull(pair.getRight());
        assertEquals("Left", pair.getLeft(), "setRight should not change left value");
    }

    @Test
    void testSetRightFromNullToValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        pair.setRight(2);
        assertEquals(2, pair.getRight());
        assertEquals("Left", pair.getLeft(), "setRight should not change left value");
    }

    @Test
    void testSetRightToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        pair.setRight(1);
        assertEquals(1, pair.getRight());
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueNormal() {
        MutablePair<String, Integer> pair = Mutableof("Left", 1);
        Integer oldValue = pair.setValue(2);
        assertEquals(1, oldValue, "setValue should return the old right value");
        assertEquals(2, pair.getRight(), "setValue should update the right value");
        assertEquals("Left", pair.getLeft(), "setValue should not change left value");
    }

    @Test
    void testSetValueToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        Integer oldValue = pair.setValue(null);
        assertEquals(1, oldValue, "setValue should return the old right value");
        assertNull(pair.getRight(), "setValue should update the right value to null");
        assertEquals("Left", pair.getLeft(), "setValue should not change left value");
    }

    @Test
    void testSetValueFromNullToValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        Integer oldValue = pair.setValue(2);
        assertNull(oldValue, "setValue should return the old right value (null)");
        assertEquals(2, pair.getRight(), "setValue should update the right value");
        assertEquals("Left", pair.getLeft(), "setValue should not change left value");
    }

    @Test
    void testSetValueToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        Integer oldValue = pair.setValue(1);
        assertEquals(1, oldValue, "setValue should return the old right value even if it's the same");
        assertEquals(1, pair.getRight(), "setValue should still have the same right value");
    }

    // --- General behavior and interaction tests ---

    @Test
    void testMutability() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        pair.setLeft("B");
        pair.setRight(2);
        assertEquals("B", pair.getLeft());
        assertEquals(2, pair.getRight());
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
        assertNotEquals(pair1, pair3);
        assertNotEquals(pair1, pair4);
        assertNotEquals(pair1, null);
        assertNotEquals(pair1, "NotAPair");
        assertEquals(pair5, pair6);

        assertEquals(pair1.hashCode(), pair2.hashCode());
        assertEquals(pair5.hashCode(), pair6.hashCode());
    }

    @Test
    void testToString() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 123);
        assertEquals("(Key,123)", pair.toString());

        MutablePair<String, Integer> nullLeft = MutablePair.of(null, 123);
        assertEquals("(null,123)", nullLeft.toString());

        MutablePair<String, Integer> nullRight = MutablePair.of("Key", null);
        assertEquals("(Key,null)", nullRight.toString());

        MutablePair<String, Integer> bothNull = MutablePair.of(null, null);
        assertEquals("(null,null)", bothNull.toString());
    }

    // Helper method to avoid casting in some tests
    private <L, R> MutablePair<L, R> Mutableof(L left, R right) {
        return MutablePair.of(left, right);
    }
}