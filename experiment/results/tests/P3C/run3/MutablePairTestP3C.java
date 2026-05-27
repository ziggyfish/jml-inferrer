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
        MutablePair<String, Integer>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsImmutable() {
        MutablePair<String, Integer>[] emptyArray1 = MutablePair.emptyArray();
        MutablePair<String, Integer>[] emptyArray2 = MutablePair.emptyArray();
        assertSame(emptyArray1, emptyArray2, "emptyArray() should return the same instance for efficiency");
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
        assertNotNull(pair, "of() should not return null even if left is null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should not return null even if right is null");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithBothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "of() should not return null even if both are null");
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
        assertNotNull(pair, "of(Map.Entry) should not return null even if entry's key is null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(456, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfMapEntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null even if entry's value is null");
        assertEquals("Key", pair.getLeft(), "Left element should match entry's key");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfMapEntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null even if entry's key and value are null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfMapEntryWithNullEntry() {
        // JML specification for of(Map.Entry) does not explicitly forbid null entry,
        // but the implementation typically handles it by throwing NPE or returning null.
        // Commons Lang's implementation of MutablePair.of(Map.Entry) throws NPE.
        assertThrows(NullPointerException.class, () -> MutablePair.of((Map.Entry<String, Integer>) null),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Non-null", 789);
        assertNotNull(pair, "ofNonNull() should not return null for non-null inputs");
        assertEquals("Non-null", pair.getLeft(), "Left element should match input");
        assertEquals(789, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfNonNullWithNullLeft() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException if left is null");
    }

    @Test
    void testOfNonNullWithNullRight() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Non-null", null),
                "ofNonNull() should throw NullPointerException if right is null");
    }

    @Test
    void testOfNonNullWithBothNull() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException if both are null");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("NonNullKey", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "ofNonNull(Map.Entry) should not return null for non-null entry with non-null key/value");
        assertEquals("NonNullKey", pair.getLeft(), "Left element should match entry's key");
        assertEquals(101, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfNonNullMapEntryWithNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException if entry's key is null");
    }

    @Test
    void testOfNonNullMapEntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("NonNullKey", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException if entry's value is null");
    }

    @Test
    void testOfNonNullMapEntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException if entry's key and value are null");
    }

    @Test
    void testOfNonNullMapEntryWithNullEntry() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull((Map.Entry<String, Integer>) null),
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
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 2);
        assertEquals(2, pair.getRight(), "getRight() should return the correct right value");
    }

    @Test
    void testGetRightWhenNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight(), "getRight() should return null if right value is null");
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", 10);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
        assertEquals(10, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("InitialLeft", 10);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should allow setting left to null");
        assertEquals(10, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("SameValue", 10);
        pair.setLeft("SameValue");
        assertEquals("SameValue", pair.getLeft(), "setLeft() should work even if value is the same");
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(30);
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
        assertEquals(30, pair.getRight(), "setRight() should update the right value");
    }

    @Test
    void testSetRightToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(null);
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
        assertNull(pair.getRight(), "setRight() should allow setting right to null");
    }

    @Test
    void testSetRightToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 20);
        pair.setRight(20);
        assertEquals(20, pair.getRight(), "setRight() should work even if value is the same");
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(200);
        assertEquals(100, oldValue, "setValue() should return the old right value");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(200, pair.getRight(), "setValue() should update the right value");
    }

    @Test
    void testSetValueToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(null);
        assertEquals(100, oldValue, "setValue() should return the old right value even when setting to null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertNull(pair.getRight(), "setValue() should allow setting right to null");
    }

    @Test
    void testSetValueFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(300);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(300, pair.getRight(), "setValue() should update the right value");
    }

    @Test
    void testSetValueToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 100);
        Integer oldValue = pair.setValue(100);
        assertEquals(100, oldValue, "setValue() should return the old right value even if it's the same");
        assertEquals(100, pair.getRight(), "setValue() should still hold the same right value");
    }

    // --- Constructor (implicit in of methods) and toString/equals/hashCode (not specified but good to check) ---

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

        // Equals
        assertEquals(pair1, pair2);
        assertNotEquals(pair1, pair3);
        assertNotEquals(pair1, pair4);
        assertNotEquals(pair1, null);
        assertNotEquals(pair1, "NotAPair");
        assertEquals(pair5, pair6);
        assertEquals(pair7, pair8);
        assertNotEquals(pair1, pair5);
        assertNotEquals(pair1, pair7);

        // HashCode
        assertEquals(pair1.hashCode(), pair2.hashCode());
        // Hash codes for unequal objects are not guaranteed to be different, but for good distribution, they usually are.
        // We can at least check consistency.
        assertEquals(pair5.hashCode(), pair6.hashCode());
        assertEquals(pair7.hashCode(), pair8.hashCode());
    }
}