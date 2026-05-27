package org.apache.commons.lang3.tuple.p3c;

import org.apache.commons.lang3.tuple.MutablePair;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Map;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.*;

class MutablePairTestP3CP3C {

    // --- emptyArray() tests ---

    @Test
    void testEmptyArray() {
        MutablePair<String, Integer>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsImmutableReference() {
        MutablePair<String, Integer>[] array1 = MutablePair.emptyArray();
        MutablePair<String, Integer>[] array2 = MutablePair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same array instance for efficiency");
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
    void testOfWithNullLeftValue() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair, "of() should not return null for null left input");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(123, pair.getRight(), "Right value should match input");
    }

    @Test
    void testOfWithNullRightValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should not return null for null right input");
        assertEquals("Hello", pair.getLeft(), "Left value should match input");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithBothNullValues() {
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
    void testOfWithNonNullMapEntry() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for non-null entry");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertEquals(456, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfWithMapEntryHavingNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for entry with null key");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(456, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfWithMapEntryHavingNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for entry with null value");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithMapEntryHavingBothNulls() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for entry with both nulls");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    void testOfWithNullMapEntry() {
        // JML specification does not explicitly forbid null Map.Entry, but it's a common failure scenario.
        // The current implementation of MutablePair.of(Map.Entry) throws NPE if entry is null.
        assertThrows(NullPointerException.class, () -> MutablePair.of((Map.Entry<String, Integer>) null),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullWithNonNullValues() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Alpha", 789);
        assertNotNull(pair, "ofNonNull() should not return null for non-null inputs");
        assertEquals("Alpha", pair.getLeft(), "Left value should match input");
        assertEquals(789, pair.getRight(), "Right value should match input");
    }

    @Test
    void testOfNonNullWithNullLeftValue() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException for null left value");
    }

    @Test
    void testOfNonNullWithNullRightValue() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Alpha", null),
                "ofNonNull() should throw NullPointerException for null right value");
    }

    @Test
    void testOfNonNullWithBothNullValues() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null values");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullWithNonNullMapEntryAndValues() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Beta", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "ofNonNull(Map.Entry) should not return null for non-null entry with non-null values");
        assertEquals("Beta", pair.getLeft(), "Left value should match entry's key");
        assertEquals(101, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    void testOfNonNullWithMapEntryHavingNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null key");
    }

    @Test
    void testOfNonNullWithMapEntryHavingNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Beta", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null value");
    }

    @Test
    void testOfNonNullWithMapEntryHavingBothNulls() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with both nulls");
    }

    @Test
    void testOfNonNullWithNullMapEntry() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull((Map.Entry<String, Integer>) null),
                "ofNonNull(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeftWithNonNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals("LeftValue", pair.getLeft(), "getLeft() should return the correct non-null value");
    }

    @Test
    void testGetLeftWithNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        assertNull(pair.getLeft(), "getLeft() should return null if left value is null");
    }

    @Test
    void testGetLeftAfterSetLeft() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "getLeft() should return the updated left value");
    }

    // --- getRight() tests ---

    @Test
    void testGetRightWithNonNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 2);
        assertEquals(2, pair.getRight(), "getRight() should return the correct non-null value");
    }

    @Test
    void testGetRightWithNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        assertNull(pair.getRight(), "getRight() should return null if right value is null");
    }

    @Test
    void testGetRightAfterSetRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setRight(99);
        assertEquals(99, pair.getRight(), "getRight() should return the updated right value");
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftWithNonNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 10);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
    }

    @Test
    void testSetLeftWithNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 10);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should allow setting left value to null");
    }

    @Test
    void testSetLeftMultipleTimes() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        pair.setLeft("B");
        assertEquals("B", pair.getLeft());
        pair.setLeft("C");
        assertEquals("C", pair.getLeft());
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightWithNonNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(30);
        assertEquals(30, pair.getRight(), "setRight() should update the right value");
    }

    @Test
    void testSetRightWithNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(null);
        assertNull(pair.getRight(), "setRight() should allow setting right value to null");
    }

    @Test
    void testSetRightMultipleTimes() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        pair.setRight(2);
        assertEquals(2, pair.getRight());
        pair.setRight(3);
        assertEquals(3, pair.getRight());
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueWithNonNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(200);
        assertEquals(100, oldValue, "setValue() should return the old right value");
        assertEquals(200, pair.getRight(), "setValue() should update the right value");
        assertEquals("Key", pair.getLeft(), "setValue() should not change the left value");
    }

    @Test
    void testSetValueWithNullValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(null);
        assertEquals(100, oldValue, "setValue() should return the old right value even if new is null");
        assertNull(pair.getRight(), "setValue() should allow setting right value to null");
        assertEquals("Key", pair.getLeft(), "setValue() should not change the left value");
    }

    @Test
    void testSetValueWhenRightWasInitiallyNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(500);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals(500, pair.getRight(), "setValue() should update the right value from null to non-null");
    }

    @Test
    void testSetValueMultipleTimes() {
        MutablePair<String, Integer> pair = MutablePair.of("X", 10);
        assertEquals(10, pair.setValue(20));
        assertEquals(20, pair.getRight());
        assertEquals(20, pair.setValue(30));
        assertEquals(30, pair.getRight());
        assertEquals(30, pair.setValue(null));
        assertNull(pair.getRight());
        assertNull(pair.setValue(40));
        assertEquals(40, pair.getRight());
    }

    // --- General behavior and utility methods (not explicitly in spec but good to test) ---

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
        assertNotEquals(pair1, "NotAPair");

        assertEquals(pair5, pair6);
        assertEquals(pair5.hashCode(), pair6.hashCode());

        // Test mutation affecting equals/hashCode
        pair1.setLeft("B");
        assertEquals(pair1, pair3); // Now pair1 is ("B", 1)
        assertEquals(pair1.hashCode(), pair3.hashCode());

        pair1.setRight(2);
        assertNotEquals(pair1, pair3); // Now pair1 is ("B", 2)
        assertEquals(pair1, MutablePair.of("B", 2));
    }

    @Test
    void testToString() {
        MutablePair<String, Integer> pair1 = MutablePair.of("Hello", 123);
        assertEquals("(Hello,123)", pair1.toString());

        MutablePair<String, Integer> pair2 = MutablePair.of(null, 456);
        assertEquals("(null,456)", pair2.toString());

        MutablePair<String, Integer> pair3 = MutablePair.of("World", null);
        assertEquals("(World,null)", pair3.toString());

        MutablePair<String, Integer> pair4 = MutablePair.of(null, null);
        assertEquals("(null,null)", pair4.toString());
    }

    @Test
    void testImmutabilityOfEmptyArrayReference() {
        MutablePair<String, Integer>[] array = MutablePair.emptyArray();
        // Attempting to modify the array itself (not its content, which is empty)
        // This test ensures the reference returned is always the same, not that the array is modifiable.
        // The array is of length 0, so no elements can be set.
        // This is more about ensuring the same empty array instance is returned.
        assertSame(MutablePair.emptyArray(), array);
    }
}