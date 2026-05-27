package org.apache.commons.lang3.tuple.p3c;

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

class PairTestP3CP3C {

    // --- emptyArray() tests ---
    @Test
    void testEmptyArray() {
        Pair<String, Integer>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsAlwaysTheSameInstance() {
        Pair<String, Integer>[] array1 = Pair.emptyArray();
        Pair<Double, Boolean>[] array2 = Pair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same instance regardless of generic types");
    }

    // --- of(L left, R right) tests ---
    @Test
    void testOfNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertEquals(123, pair.getRight());
        assertEquals("Hello", pair.getKey());
        assertEquals(123, pair.getValue());
    }

    @Test
    void testOfNullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    @Test
    void testOfNullRight() {
        Pair<String, Integer> pair = Pair.of("Hello", null);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfBothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfDifferentTypes() {
        Pair<Integer, Boolean> pair = Pair.of(42, true);
        assertEquals(42, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---
    @Test
    void testOfMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    void testOfMapEntryNullEntry() {
        assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    @Test
    void testOfMapEntryNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    void testOfMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryFromHashMap() {
        Map<String, Integer> map = new HashMap<>();
        map.put("A", 1);
        Map.Entry<String, Integer> entry = map.entrySet().iterator().next();
        Pair<String, Integer> pair = Pair.of(entry);
        assertEquals("A", pair.getLeft());
        assertEquals(1, pair.getRight());
    }

    // --- ofNonNull(L left, R right) tests ---
    @Test
    void testOfNonNullNormalBehavior() {
        Pair<String, Integer> pair = Pair.ofNonNull("NonNullLeft", 789);
        assertNotNull(pair);
        assertEquals("NonNullLeft", pair.getLeft());
        assertEquals(789, pair.getRight());
    }

    @Test
    void testOfNonNullNullLeft() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 789),
                "ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNullNullRight() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("NonNullLeft", null),
                "ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNullBothNull() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null");
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---
    @Test
    void testAcceptNormalBehavior() throws IOException {
        Pair<String, Integer> pair = Pair.of("Test", 100);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicReference<Integer> consumedRight = new AtomicReference<>();

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            consumedLeft.set(l);
            consumedRight.set(r);
        };

        pair.accept(consumer);

        assertEquals("Test", consumedLeft.get());
        assertEquals(100, consumedRight.get());
    }

    @Test
    void testAcceptWithNullValues() throws IOException {
        Pair<String, Integer> pair = Pair.of(null, null);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicReference<Integer> consumedRight = new AtomicReference<>();

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            consumedLeft.set(l);
            consumedRight.set(r);
        };

        pair.accept(consumer);

        assertNull(consumedLeft.get());
        assertNull(consumedRight.get());
    }

    @Test
    void testAcceptThrowsException() {
        Pair<String, Integer> pair = Pair.of("Test", 100);
        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Test exception from consumer");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.accept(consumer));
        assertEquals("Test exception from consumer", thrown.getMessage());
    }

    @Test
    void testAcceptNullConsumer() {
        Pair<String, Integer> pair = Pair.of("Test", 100);
        assertThrows(NullPointerException.class, () -> pair.accept(null),
                "accept() should throw NullPointerException for null consumer");
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---
    @Test
    void testApplyNormalBehavior() throws IOException {
        Pair<String, Integer> pair = Pair.of("Value", 200);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> l + "-" + r;

        String result = pair.apply(function);
        assertEquals("Value-200", result);
    }

    @Test
    void testApplyWithNullValues() throws IOException {
        Pair<String, Integer> pair = Pair.of(null, null);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) ->
                (l == null ? "null" : l) + "-" + (r == null ? "null" : r);

        String result = pair.apply(function);
        assertEquals("null-null", result);
    }

    @Test
    void testApplyThrowsException() {
        Pair<String, Integer> pair = Pair.of("Value", 200);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Test exception from function");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.apply(function));
        assertEquals("Test exception from function", thrown.getMessage());
    }

    @Test
    void testApplyNullFunction() {
        Pair<String, Integer> pair = Pair.of("Value", 200);
        assertThrows(NullPointerException.class, () -> pair.apply(null),
                "apply() should throw NullPointerException for null function");
    }

    @Test
    void testApplyReturnsNull() throws IOException {
        Pair<String, Integer> pair = Pair.of("Value", 200);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> null;
        assertNull(pair.apply(function));
    }

    // --- compareTo(Pair<L, R> other) tests ---
    @Test
    void testCompareToEqualPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(0, pair1.compareTo(pair2));
    }

    @Test
    void testCompareToDifferentLeft() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertTrue(pair1.compareTo(pair2) < 0); // "A" < "B"
        assertTrue(pair2.compareTo(pair1) > 0); // "B" > "A"
    }

    @Test
    void testCompareToDifferentRight() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 2);
        assertTrue(pair1.compareTo(pair2) < 0); // 1 < 2
        assertTrue(pair2.compareTo(pair1) > 0); // 2 > 1
    }

    @Test
    void testCompareToDifferentBoth() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 0);
        assertTrue(pair1.compareTo(pair2) < 0); // "A" < "B", so right value doesn't matter
    }

    @Test
    void testCompareToNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.compareTo(pair2) < 0); // null < "A"
        assertTrue(pair2.compareTo(pair1) > 0); // "A" > null
    }

    @Test
    void testCompareToNullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.compareTo(pair2) < 0); // null < 1
        assertTrue(pair2.compareTo(pair1) > 0); // 1 > null
    }

    @Test
    void testCompareToBothNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 2);
        assertTrue(pair1.compareTo(pair2) < 0); // 1 < 2
        assertTrue(pair2.compareTo(pair1) > 0); // 2 > 1
    }

    @Test
    void testCompareToBothNullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("B", null);
        assertTrue(pair1.compareTo(pair2) < 0); // "A" < "B"
        assertTrue(pair2.compareTo(pair1) > 0); // "B" > "A"
    }

    @Test
    void testCompareToAllNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertEquals(0, pair1.compareTo(pair2));
    }

    @Test
    void testCompareToNullOther() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> pair.compareTo(null),
                "compareTo() should throw NullPointerException for null other pair");
    }

    @Test
    void testCompareToNonComparableTypes() {
        // This test relies on the fact that Pair uses Comparable for comparison.
        // If the types are not Comparable, it will throw a ClassCastException at runtime.
        // JML doesn't explicitly state this, but it's an implicit requirement for compareTo.
        Pair<Object, Integer> pair1 = Pair.of(new Object(), 1);
        Pair<Object, Integer> pair2 = Pair.of(new Object(), 1);

        // The default implementation of Pair uses ComparableUtils.compare which handles nulls
        // and then tries to cast to Comparable.
        assertThrows(ClassCastException.class, () -> pair1.compareTo(pair2),
                "compareTo() should throw ClassCastException if elements are not Comparable");
    }

    // --- equals(Object obj) tests ---
    @Test
    void testEqualsSameInstance() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertTrue(pair.equals(pair));
    }

    @Test
    void testEqualsEqualPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
    }

    @Test
    void testEqualsDifferentLeft() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertFalse(pair1.equals(pair2));
    }

    @Test
    void testEqualsDifferentRight() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 2);
        assertFalse(pair1.equals(pair2));
    }

    @Test
    void testEqualsDifferentBoth() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 2);
        assertFalse(pair1.equals(pair2));
    }

    @Test
    void testEqualsWithNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 1);
        Pair<String, Integer> pair3 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
        assertFalse(pair1.equals(pair3));
    }

    @Test
    void testEqualsWithNullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        Pair<String, Integer> pair3 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
        assertFalse(pair1.equals(pair3));
    }

    @Test
    void testEqualsWithBothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertTrue(pair1.equals(pair2));
    }

    @Test
    void testEqualsWithDifferentTypes() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        assertFalse(pair1.equals("A")); // Not a Pair
        assertFalse(pair1.equals(null));
    }

    @Test
    void testEqualsWithMapEntry() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("A", 1);
        assertTrue(pair.equals(entry)); // Pair should be equal to Map.Entry if contents are same
        assertTrue(entry.equals(pair)); // Map.Entry should also be equal to Pair
    }

    @Test
    void testEqualsWithMapEntryDifferent() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("B", 1);
        assertFalse(pair.equals(entry));
    }

    // --- getKey(), getLeft(), getRight(), getValue() tests ---
    @Test
    void testGettersNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Key1", 10);
        assertEquals("Key1", pair.getKey());
        assertEquals("Key1", pair.getLeft());
        assertEquals(10, pair.getRight());
        assertEquals(10, pair.getValue());
    }

    @Test
    void testGettersWithNullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNull(pair.getKey());
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
        assertNull(pair.getValue());
    }

    // --- hashCode() tests ---
    @Test
    void testHashCodeEqualPairsHaveSameHashCode() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(pair1.hashCode(), pair2.hashCode());
    }

    @Test
    void testHashCodeDifferentPairsHaveDifferentHashCode() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        Pair<String, Integer> pair3 = Pair.of("A", 2);
        assertNotEquals(pair1.hashCode(), pair2.hashCode());
        assertNotEquals(pair1.hashCode(), pair3.hashCode());
    }

    @Test
    void testHashCodeWithNullValues() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 1);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        Pair<String, Integer> pair3 = Pair.of("A", null);
        Pair<String, Integer> pair4 = Pair.of("A", null);
        assertEquals(pair3.hashCode(), pair4.hashCode());

        Pair<String, Integer> pair5 = Pair.of(null, null);
        Pair<String, Integer> pair6 = Pair.of(null, null);
        assertEquals(pair5.hashCode(), pair6.hashCode());
    }

    @Test
    void testHashCodeConsistencyWithEquals() {
        Pair<String, Integer> pair1 = Pair.of("Test", 123);
        Pair<String, Integer> pair2 = Pair.of("Test", 123);
        Pair<String, Integer> pair3 = Pair.of("Other", 456);

        assertTrue(pair1.equals(pair2));
        assertEquals(pair1.hashCode(), pair2.hashCode());

        assertFalse(pair1.equals(pair3));
        // Hash codes are not required to be different for unequal objects, but it's good practice
        // to check they are usually different for distinct content.
        assertNotEquals(pair1.hashCode(), pair3.hashCode());
    }

    // --- toString() tests ---
    @Test
    void testToStringNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertEquals("(Left,100)", pair.toString());
    }

    @Test
    void testToStringWithNullValues() {
        Pair<String, Integer> pair1 = Pair.of(null, 100);
        assertEquals("(null,100)", pair1.toString());

        Pair<String, Integer> pair2 = Pair.of("Left", null);
        assertEquals("(Left,null)", pair2.toString());

        Pair<String, Integer> pair3 = Pair.of(null, null);
        assertEquals("(null,null)", pair3.toString());
    }

    @Test
    void testToStringWithSpecialCharacters() {
        Pair<String, String> pair = Pair.of("L,eft", "R)ight");
        assertEquals("(L,eft,R)ight)", pair.toString());
    }

    // --- toString(String format) tests ---
    @Test
    void testToStringFormatNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertEquals("Left=100", pair.toString("%1$s=%2$s"));
        assertEquals("100-Left", pair.toString("%2$s-%1$s"));
    }

    @Test
    void testToStringFormatWithNullValues() {
        Pair<String, Integer> pair1 = Pair.of(null, 100);
        assertEquals("null:100", pair1.toString("%1$s:%2$s"));

        Pair<String, Integer> pair2 = Pair.of("Left", null);
        assertEquals("Left:null", pair2.toString("%1$s:%2$s"));

        Pair<String, Integer> pair3 = Pair.of(null, null);
        assertEquals("null:null", pair3.toString("%1$s:%2$s"));
    }

    @Test
    void testToStringFormatEmptyFormatString() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertEquals("", pair.toString(""));
    }

    @Test
    void testToStringFormatOnlyLeftPlaceholder() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertEquals("Left", pair.toString("%1$s"));
    }

    @Test
    void testToStringFormatOnlyRightPlaceholder() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertEquals("100", pair.toString("%2$s"));
    }

    @Test
    void testToStringFormatNoPlaceholders() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertEquals("Fixed String", pair.toString("Fixed String"));
    }

    @Test
    void testToStringFormatNullFormatString() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertThrows(NullPointerException.class, () -> pair.toString(null),
                "toString(format) should throw NullPointerException for null format string");
    }

    @Test
    void testToStringFormatInvalidFormatString() {
        Pair<String, Integer> pair = Pair.of("Left", 100);
        assertThrows(java.util.IllegalFormatException.class, () -> pair.toString("%3$s"),
                "toString(format) should throw IllegalFormatException for invalid format string");
    }
}