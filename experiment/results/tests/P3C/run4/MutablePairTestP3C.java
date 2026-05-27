package org.apache.commons.lang3.tuple.p3c;

import org.apache.commons.lang3.tuple.MutablePair;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

public class MutablePairTestP3CP3C {

    // --- emptyArray() tests ---

    @Test
    void testEmptyArray() {
        MutablePair<?, ?>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
        // Ensure it's a new array each time (or at least not the same reference)
        MutablePair<?, ?>[] anotherEmptyArray = MutablePair.emptyArray();
        assertNotSame(emptyArray, anotherEmptyArray, "emptyArray() should return a new array instance each time");
    }

    // --- of(L left, R right) tests ---

    @Test
    void testOf_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", 123);
        assertNotNull(pair, "of() should not return null for non-null inputs");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOf_NullLeft() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair, "of() should not return null for null left input");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOf_NullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "of() should not return null for null right input");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOf_BothNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "of() should not return null for both null inputs");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOf_DifferentTypes() {
        MutablePair<Integer, Boolean> pair = MutablePair.of(42, true);
        assertEquals(42, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfMapEntry_NormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 100);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "of(Map.Entry) should not return null for non-null entry");
        assertEquals("Key", pair.getLeft(), "Left element should match entry key");
        assertEquals(100, pair.getRight(), "Right element should match entry value");
    }

    @Test
    void testOfMapEntry_NullEntry() {
        // JML specification for of(Map.Entry) does not explicitly forbid null entry.
        // It's common for such methods to throw NPE or return a pair with nulls.
        // Based on other 'of' methods, returning a pair with nulls seems more consistent.
        MutablePair<String, Integer> pair = MutablePair.of((Map.Entry<String, Integer>) null);
        assertNotNull(pair, "of(Map.Entry) should not return null even for null entry");
        assertNull(pair.getLeft(), "Left element should be null for null entry");
        assertNull(pair.getRight(), "Right element should be null for null entry");
    }

    @Test
    void testOfMapEntry_EntryWithNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 100);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(100, pair.getRight());
    }

    @Test
    void testOfMapEntry_EntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntry_EntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    void testOfNonNull_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Alpha", 1);
        assertNotNull(pair);
        assertEquals("Alpha", pair.getLeft());
        assertEquals(1, pair.getRight());
    }

    @Test
    void testOfNonNull_NullLeft_ThrowsException() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 1),
                "ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNull_NullRight_ThrowsException() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Beta", null),
                "ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNull_BothNull_ThrowsException() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both nulls");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    void testOfNonNullMapEntry_NormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Gamma", 2);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair);
        assertEquals("Gamma", pair.getLeft());
        assertEquals(2, pair.getRight());
    }

    @Test
    void testOfNonNullMapEntry_NullEntry_ThrowsException() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull((Map.Entry<String, Integer>) null),
                "ofNonNull(Map.Entry) should throw NullPointerException for null entry");
    }

    @Test
    void testOfNonNullMapEntry_EntryWithNullKey_ThrowsException() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 2);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null key");
    }

    @Test
    void testOfNonNullMapEntry_EntryWithNullValue_ThrowsException() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Delta", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null value");
    }

    @Test
    void testOfNonNullMapEntry_EntryWithBothNull_ThrowsException() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with both nulls");
    }

    // --- getLeft() tests ---

    @Test
    void testGetLeft_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 10);
        assertEquals("LeftValue", pair.getLeft());
    }

    @Test
    void testGetLeft_NullLeft() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 10);
        assertNull(pair.getLeft());
    }

    // --- getRight() tests ---

    @Test
    void testGetRight_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 10);
        assertEquals(10, pair.getRight());
    }

    @Test
    void testGetRight_NullRight() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight());
    }

    // --- setLeft(L left) tests ---

    @Test
    void testSetLeft_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft(), "setLeft() should update the left value");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeft_SetToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setLeft(null);
        assertNull(pair.getLeft(), "setLeft() should allow setting left to null");
        assertEquals(1, pair.getRight(), "setLeft() should not affect the right value");
    }

    @Test
    void testSetLeft_SetToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Same", 1);
        pair.setLeft("Same");
        assertEquals("Same", pair.getLeft());
    }

    // --- setRight(R right) tests ---

    @Test
    void testSetRight_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setRight(99);
        assertEquals("Initial", pair.getLeft(), "setRight() should not affect the left value");
        assertEquals(99, pair.getRight(), "setRight() should update the right value");
    }

    @Test
    void testSetRight_SetToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setRight(null);
        assertEquals("Initial", pair.getLeft(), "setRight() should not affect the left value");
        assertNull(pair.getRight(), "setRight() should allow setting right to null");
    }

    @Test
    void testSetRight_SetToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Initial", 1);
        pair.setRight(1);
        assertEquals(1, pair.getRight());
    }

    // --- setValue(R value) tests ---

    @Test
    void testSetValue_NormalBehavior() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 10);
        Integer oldValue = pair.setValue(20);
        assertEquals(10, oldValue, "setValue() should return the old right value");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertEquals(20, pair.getRight(), "setValue() should update the right value");
    }

    @Test
    void testSetValue_SetToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 10);
        Integer oldValue = pair.setValue(null);
        assertEquals(10, oldValue, "setValue() should return the old right value even if new is null");
        assertEquals("Key", pair.getLeft(), "setValue() should not affect the left value");
        assertNull(pair.getRight(), "setValue() should allow setting right to null");
    }

    @Test
    void testSetValue_FromNullToNonNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(50);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals("Key", pair.getLeft());
        assertEquals(50, pair.getRight());
    }

    @Test
    void testSetValue_FromNullToNull() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", null);
        Integer oldValue = pair.setValue(null);
        assertNull(oldValue, "setValue() should return null if old right value was null");
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testSetValue_SetToSameValue() {
        MutablePair<String, Integer> pair = MutablePair.of("Key", 10);
        Integer oldValue = pair.setValue(10);
        assertEquals(10, oldValue);
        assertEquals(10, pair.getRight());
    }

    // --- General behavior tests (e.g., immutability of returned array) ---

    @Test
    void testEmptyArray_Immutability() {
        MutablePair<String, Integer>[] emptyArray = MutablePair.emptyArray();
        // Attempt to modify the array (should not be possible for a 0-length array)
        // This test primarily ensures that the returned array is not null and has 0 length.
        // If it were mutable and non-empty, we'd test modifying elements.
        assertNotNull(emptyArray);
        assertEquals(0, emptyArray.length);
    }

    @Test
    void testToString() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        assertEquals("(A,1)", pair.toString());

        MutablePair<String, Integer> nullLeft = MutablePair.of(null, 1);
        assertEquals("(null,1)", nullLeft.toString());

        MutablePair<String, Integer> nullRight = MutablePair.of("A", null);
        assertEquals("(A,null)", nullRight.toString());

        MutablePair<String, Integer> bothNull = MutablePair.of(null, null);
        assertEquals("(null,null)", bothNull.toString());
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
        assertNotEquals(pair1, new Object());
        assertEquals(pair5, pair6);
        assertEquals(pair7, pair8);
        assertNotEquals(pair1, pair5);
        assertNotEquals(pair1, pair7);

        // HashCode
        assertEquals(pair1.hashCode(), pair2.hashCode());
        assertEquals(pair5.hashCode(), pair6.hashCode());
        assertEquals(pair7.hashCode(), pair8.hashCode());
        // Note: Hash code collision is possible, so inequality of hash codes is not guaranteed for unequal objects.
        // However, for distinct objects, it's a good practice to check if they are different.
        assertNotEquals(pair1.hashCode(), pair3.hashCode());
        assertNotEquals(pair1.hashCode(), pair4.hashCode());
    }

    @Test
    void testEqualsAndHashCode_AfterMutation() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);

        assertEquals(pair1, pair2);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        pair1.setLeft("B");
        assertNotEquals(pair1, pair2);
        assertNotEquals(pair1.hashCode(), pair2.hashCode()); // Not strictly required, but usually true

        pair2.setLeft("B");
        assertEquals(pair1, pair2);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        pair1.setRight(2);
        assertNotEquals(pair1, pair2);
        assertNotEquals(pair1.hashCode(), pair2.hashCode());

        pair2.setRight(2);
        assertEquals(pair1, pair2);
        assertEquals(pair1.hashCode(), pair2.hashCode());
    }
}