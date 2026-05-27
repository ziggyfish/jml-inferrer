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
    void testEmptyArrayReturnsSameInstance() {
        MutablePair<String, Integer>[] array1 = MutablePair.emptyArray();
        MutablePair<String, Integer>[] array2 = MutablePair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same instance for efficiency");
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
        assertNotNull(pair, "of() should not return null even with null left");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should not return null even with null right");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithBothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "of() should not return null even with both null");
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
        assertNotNull(pair, "of(Map.Entry) should not return null even with null key");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(456, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfMapEntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null even with null value");
        assertEquals("Key", pair.getLeft(), "Left element should match entry's key");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfMapEntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null even with both null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfMapEntryWithNullEntry() {
        // JML specification does not explicitly forbid null entry for of(Map.Entry)
        // but it's good practice to test it. It typically throws NPE.
        assertThrows(NullPointerException.class, () -> MutablePair.of((Map.Entry<String, Integer>) null),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNullNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Non-null", 789);
        assertNotNull(pair, "ofNonNull() should not return null");
        assertEquals("Non-null", pair.getLeft());
        assertEquals(789, pair.getRight());
    }

    @Test
    void testOfNonNullWithNullLeft() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNullWithNullRight() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Non-null", null),
                "ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNullWithBothNull() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("NonNullKey", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "ofNonNull(Map.Entry) should not return null");
        assertEquals("NonNullKey", pair.getLeft());
        assertEquals(101, pair.getRight());
    }

    @Test
    void testOfNonNullMapEntryWithNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null key in entry");
    }

    @Test
    void testOfNonNullMapEntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("NonNullKey", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null value in entry");
    }

    @Test
    void testOfNonNullMapEntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for both null in entry");
    }

    @Test
    void testOfNonNullMapEntryWithNullEntry() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull((Map.Entry<String, Integer>) null),
                "ofNonNull(Map.Entry) should throw NullPointerException for null entry itself");
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

    @Test
    void testGetLeftAfterSetLeft() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "getLeft() should reflect the updated left value");
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

    @Test
    void testGetRightAfterSetRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setRight(2);
        assertEquals(2, pair.getRight(), "getRight() should reflect the updated right value");
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeftNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should allow setting left to null");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeftFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        pair.setLeft("NonNullLeft");
        assertEquals("NonNullLeft", pair.getLeft(), "setLeft() should update from null to non-null");
    }

    @Test
    void testSetLeftToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Same", 1);
        pair.setLeft("Same");
        assertEquals("Same", pair.getLeft(), "setLeft() should work even if value is the same");
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRightNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        pair.setRight(2);
        assertEquals(2, pair.getRight(), "setRight() should update the right value");
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
    }

    @Test
    void testSetRightToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        pair.setRight(null);
        assertNull(pair.getRight(), "setRight() should allow setting right to null");
        assertEquals("Left", pair.getLeft(), "setRight() should not affect the left value");
    }

    @Test
    void testSetRightFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        pair.setRight(2);
        assertEquals(2, pair.getRight(), "setRight() should update from null to non-null");
    }

    @Test
    void testSetRightToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 2);
        pair.setRight(2);
        assertEquals(2, pair.getRight(), "setRight() should work even if value is the same");
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValueNormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        Integer oldValue = pair.setValue(2);
        assertEquals(1, oldValue, "setValue() should return the old right value");
        assertEquals(2, pair.getRight(), "setValue() should update the right value");
        assertEquals("Left", pair.getLeft(), "setValue() should not affect the left value");
    }

    @Test
    void testSetValueToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 1);
        Integer oldValue = pair.setValue(null);
        assertEquals(1, oldValue, "setValue() should return the old right value when setting to null");
        assertNull(pair.getRight(), "setValue() should allow setting right to null");
        assertEquals("Left", pair.getLeft(), "setValue() should not affect the left value");
    }

    @Test
    void testSetValueFromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        Integer oldValue = pair.setValue(2);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals(2, pair.getRight(), "setValue() should update from null to non-null");
    }

    @Test
    void testSetValueToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 2);
        Integer oldValue = pair.setValue(2);
        assertEquals(2, oldValue, "setValue() should return the old value even if it's the same");
        assertEquals(2, pair.getRight(), "setValue() should work even if value is the same");
    }

    // --- General Pair Behavior (equals, hashCode, toString) ---

    @Test
    void testEqualsAndHashCode() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair3 = MutablePair.of("B", 1);
        MutablePair<String, Integer> pair4 = MutablePair.of("A", 2);
        MutablePair<String, Integer> pair5 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair6 = MutablePair.of(null, 1);

        assertEquals(pair1, pair2, "Pairs with same content should be equal");
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Equal pairs should have same hash code");
        assertNotEquals(pair1, pair3, "Pairs with different left should not be equal");
        assertNotEquals(pair1, pair4, "Pairs with different right should not be equal");
        assertNotEquals(pair1, null, "Pair should not be equal to null");
        assertNotEquals(pair1, "NotAPair", "Pair should not be equal to different class");

        assertEquals(pair5, pair6, "Pairs with null left and same right should be equal");
        assertEquals(pair5.hashCode(), pair6.hashCode(), "Equal pairs with null should have same hash code");

        // Test after modification
        pair1.setLeft("C");
        assertNotEquals(pair1, pair2, "Pairs should not be equal after modification");
    }

    @Test
    void testToString() {
        MutablePair<String, Integer> pair1 = MutablePair.of("Hello", 123);
        assertEquals("(Hello,123)", pair1.toString(), "toString() should return expected format");

        MutablePair<String, Integer> pair2 = MutablePair.of(null, null);
        assertEquals("(null,null)", pair2.toString(), "toString() should handle nulls");

        MutablePair<String, Integer> pair3 = MutablePair.of("Long String Value", 987654321);
        assertEquals("(Long String Value,987654321)", pair3.toString(), "toString() should handle longer values");
    }
}