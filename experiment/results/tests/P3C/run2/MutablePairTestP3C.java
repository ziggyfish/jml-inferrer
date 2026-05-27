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
    void testEmptyArrayIsImmutable() {
        MutablePair<?, ?>[] array1 = MutablePair.emptyArray();
        MutablePair<?, ?>[] array2 = MutablePair.emptyArray();
        // While the array itself is empty, we want to ensure it's not a new instance every time
        // or at least that modifying the returned array doesn't affect subsequent calls if it were mutable.
        // For an empty array, this test primarily confirms consistency.
        assertSame(array1, array2, "emptyArray() should return the same empty array instance");
    }

    // --- of(L left, R right) tests ---

    @Test
    void testOfNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", 123);
        assertNotNull(pair, "of() should not return null for non-null inputs");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullLeft() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair, "of() should not return null for null left input");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should not return null for null right input");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithBothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "of() should not return null for both null inputs");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithDifferentTypes() {
        MutablePair<Integer, Boolean> pair = MutablePair.of(42, true);
        assertEquals(42, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for non-null entry");
        assertEquals("Key", pair.getLeft(), "Left element should match entry's key");
        assertEquals(456, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfMapEntryWithNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for entry with null key");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(456, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfMapEntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for entry with null value");
        assertEquals("Key", pair.getLeft(), "Left element should match entry's key");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfMapEntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for entry with both nulls");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfMapEntryWithNullEntry() {
        // JML @requires pair != null;
        assertThrows(NullPointerException.class, () -> MutablePair.of(null),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("NonNullLeft", 789);
        assertNotNull(pair, "ofNonNull() should not return null");
        assertEquals("NonNullLeft", pair.getLeft(), "Left element should match input");
        assertEquals(789, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfNonNullWithNullLeft() {
        // JML @requires left != null;
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException for null left input");
    }

    @Test
    void testOfNonNullWithNullRight() {
        // JML @requires right != null;
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("NonNullLeft", null),
                "ofNonNull() should throw NullPointerException for null right input");
    }

    @Test
    void testOfNonNullWithBothNull() {
        // JML @requires left != null && right != null;
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null inputs");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("NonNullKey", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "ofNonNull(Map.Entry) should not return null");
        assertEquals("NonNullKey", pair.getLeft(), "Left element should match entry's key");
        assertEquals(101, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfNonNullMapEntryWithNullKey() {
        // JML @requires pair.getKey() != null;
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null key");
    }

    @Test
    void testOfNonNullMapEntryWithNullValue() {
        // JML @requires pair.getValue() != null;
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("NonNullKey", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null value");
    }

    @Test
    void testOfNonNullMapEntryWithBothNull() {
        // JML @requires pair.getKey() != null && pair.getValue() != null;
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with both nulls");
    }

    @Test
    void testOfNonNullMapEntryWithNullEntry() {
        // JML @requires pair != null;
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null),
                "ofNonNull(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeftNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals("LeftValue", pair.getLeft(), "getLeft() should return the correct left value");
    }

    @Test
    void testGetLeftWhenNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        assertNull(pair.getLeft(), "getLeft() should return null if left value is null");
    }

    // --- getRight() tests ---

    @Test
    void testGetRightNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals(1, pair.getRight(), "getRight() should return the correct right value");
    }

    @Test
    void testGetRightWhenNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight(), "getRight() should return null if right value is null");
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", 1);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should allow setting left value to null");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update null left value to non-null");
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", 1);
        pair.setRight(2);
        assertEquals(2, pair.getRight(), "setRight() should update the right value");
        assertEquals("InitialLeft", pair.getLeft(), "setRight() should not affect the left value");
    }

    @Test
    void testSetRightToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", 1);
        pair.setRight(null);
        assertNull(pair.getRight(), "setRight() should allow setting right value to null");
        assertEquals("InitialLeft", pair.getLeft(), "setRight() should not affect the left value");
    }

    @Test
    void testSetRightFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", null);
        pair.setRight(2);
        assertEquals(2, pair.getRight(), "setRight() should update null right value to non-null");
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 10);
        Integer oldValue = pair.setValue(20);
        assertEquals(10, oldValue, "setValue() should return the old right value");
        assertEquals(20, pair.getRight(), "setValue() should update the right value");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
    }

    @Test
    void testSetValueToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 10);
        Integer oldValue = pair.setValue(null);
        assertEquals(10, oldValue, "setValue() should return the old right value when setting to null");
        assertNull(pair.getRight(), "setValue() should allow setting right value to null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
    }

    @Test
    void testSetValueFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(30);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals(30, pair.getRight(), "setValue() should update null right value to non-null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
    }

    @Test
    void testSetValueFromNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(null);
        assertNull(oldValue, "setValue() should return null if old right value was null and new is null");
        assertNull(pair.getRight(), "setValue() should keep right value as null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
    }

    // --- Additional tests for immutability/mutability aspects ---

    @Test
    void testMutability() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        pair.setLeft("B");
        pair.setRight(2);
        assertEquals("B", pair.getLeft());
        assertEquals(2, pair.getRight());

        Integer oldValue = pair.setValue(3);
        assertEquals(2, oldValue);
        assertEquals(3, pair.getRight());
    }

    @Test
    void testToString() {
        MutablePair<String, Integer> pair = MutablePair.of("Test", 123);
        assertEquals("(Test,123)", pair.toString());

        MutablePair<String, Integer> nullPair = MutablePair.of(null, null);
        assertEquals("(null,null)", nullPair.toString());

        MutablePair<String, Integer> leftNullPair = MutablePair.of(null, 123);
        assertEquals("(null,123)", leftNullPair.toString());

        MutablePair<String, Integer> rightNullPair = MutablePair.of("Test", null);
        assertEquals("(Test,null)", rightNullPair.toString());
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

        // Equals
        assertEquals(pair1, pair2);
        assertNotEquals(pair1, pair3);
        assertNotEquals(pair1, pair4);
        assertNotEquals(pair1, null);
        assertNotEquals(pair1, "A"); // Different type
        assertEquals(pair5, pair6);
        assertEquals(pair7, pair8);
        assertNotEquals(pair1, pair5);
        assertNotEquals(pair1, pair7);

        // HashCode
        assertEquals(pair1.hashCode(), pair2.hashCode());
        assertNotEquals(pair1.hashCode(), pair3.hashCode()); // Not guaranteed, but highly probable
        assertNotEquals(pair1.hashCode(), pair4.hashCode()); // Not guaranteed, but highly probable
        assertEquals(pair5.hashCode(), pair6.hashCode());
        assertEquals(pair7.hashCode(), pair8.hashCode());
    }
}