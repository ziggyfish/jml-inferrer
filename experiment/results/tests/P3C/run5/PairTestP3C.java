package org.apache.commons.lang3.tuple.p3c;

import org.apache.commons.lang3.function.FailableBiConsumer;
import org.apache.commons.lang3.function.FailableBiFunction;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Pair Class Unit Tests")
class PairTestP3CP3C {

    // --- emptyArray() tests ---
    @Test
    @DisplayName("emptyArray() should return a non-null, empty array")
    void testEmptyArray_basic() {
        Pair<?, ?>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray);
        assertEquals(0, emptyArray.length);
    }

    @Test
    @DisplayName("emptyArray() should return the same array instance on multiple calls")
    void testEmptyArray_singleton() {
        Pair<?, ?>[] array1 = Pair.emptyArray();
        Pair<?, ?>[] array2 = Pair.emptyArray();
        assertSame(array1, array2);
    }

    @Test
    @DisplayName("emptyArray() should return an array of Pair type")
    void testEmptyArray_type() {
        Pair<String, Integer>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray);
        assertEquals(0, emptyArray.length);
    }

    // --- of(L left, R right) tests ---
    @Test
    @DisplayName("of(L, R) should create a Pair with non-null elements")
    void testOf_nonNullElements() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with null left element")
    void testOf_nullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with null right element")
    void testOf_nullRight() {
        Pair<String, Integer> pair = Pair.of("Hello", null);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with both null elements")
    void testOf_bothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    @DisplayName("of(L, R) should handle different data types")
    void testOf_differentTypes() {
        Pair<Double, Boolean> pair = Pair.of(3.14, true);
        assertEquals(3.14, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---
    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a non-null Map.Entry")
    void testOf_mapEntry_nonNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with null left")
    void testOf_mapEntry_nullLeft() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with null right")
    void testOf_mapEntry_nullRight() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with both nulls")
    void testOf_mapEntry_bothNulls() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    @DisplayName("of(Map.Entry) should throw NullPointerException if entry is null")
    void testOf_mapEntry_nullEntry() {
        assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null));
    }

    // --- ofNonNull(L left, R right) tests ---
    @Test
    @DisplayName("ofNonNull(L, R) should create a Pair with non-null elements")
    void testOfNonNull_nonNullElements() {
        Pair<String, Integer> pair = Pair.ofNonNull("Hello", 123);
        assertNotNull(pair);
        assertEquals("Hello", pair.getLeft());
        assertEquals(123, pair.getRight());
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException if left is null")
    void testOfNonNull_nullLeft() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 123));
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException if right is null")
    void testOfNonNull_nullRight() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("Hello", null));
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException if both are null")
    void testOfNonNull_bothNull() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null));
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---
    @Test
    @DisplayName("accept() should execute consumer with pair elements")
    void testAccept_basic() throws Exception {
        Pair<String, Integer> pair = Pair.of("Test", 100);
        AtomicReference<String> leftRef = new AtomicReference<>();
        AtomicReference<Integer> rightRef = new AtomicReference<>();

        pair.accept((l, r) -> {
            leftRef.set(l);
            rightRef.set(r);
        });

        assertEquals("Test", leftRef.get());
        assertEquals(100, rightRef.get());
    }

    @Test
    @DisplayName("accept() should handle null elements gracefully")
    void testAccept_nullElements() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        AtomicReference<String> leftRef = new AtomicReference<>();
        AtomicReference<Integer> rightRef = new AtomicReference<>();

        pair.accept((l, r) -> {
            leftRef.set(l);
            rightRef.set(r);
        });

        assertNull(leftRef.get());
        assertNull(rightRef.get());
    }

    @Test
    @DisplayName("accept() should rethrow checked exceptions from consumer")
    void testAccept_checkedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Simulated IO Error");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.accept(consumer));
        assertEquals("Simulated IO Error", thrown.getMessage());
    }

    @Test
    @DisplayName("accept() should rethrow unchecked exceptions from consumer")
    void testAccept_uncheckedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiConsumer<String, Integer, RuntimeException> consumer = (l, r) -> {
            throw new IllegalArgumentException("Invalid arguments");
        };

        IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () -> pair.accept(consumer));
        assertEquals("Invalid arguments", thrown.getMessage());
    }

    @Test
    @DisplayName("accept() should throw NullPointerException if consumer is null")
    void testAccept_nullConsumer() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertThrows(NullPointerException.class, () -> pair.accept(null));
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---
    @Test
    @DisplayName("apply() should execute function with pair elements and return result")
    void testApply_basic() throws Exception {
        Pair<String, Integer> pair = Pair.of("Value", 10);
        String result = pair.apply((l, r) -> l + "-" + (r * 2));
        assertEquals("Value-20", result);
    }

    @Test
    @DisplayName("apply() should handle null elements gracefully and return result")
    void testApply_nullElements() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        String result = pair.apply((l, r) -> String.valueOf(l) + "-" + String.valueOf(r));
        assertEquals("null-null", result);
    }

    @Test
    @DisplayName("apply() should return null if function returns null")
    void testApply_functionReturnsNull() throws Exception {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        String result = pair.apply((l, r) -> null);
        assertNull(result);
    }

    @Test
    @DisplayName("apply() should rethrow checked exceptions from function")
    void testApply_checkedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Simulated IO Error from function");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.apply(function));
        assertEquals("Simulated IO Error from function", thrown.getMessage());
    }

    @Test
    @DisplayName("apply() should rethrow unchecked exceptions from function")
    void testApply_uncheckedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiFunction<String, Integer, String, RuntimeException> function = (l, r) -> {
            throw new IllegalStateException("Invalid state in function");
        };

        IllegalStateException thrown = assertThrows(IllegalStateException.class, () -> pair.apply(function));
        assertEquals("Invalid state in function", thrown.getMessage());
    }

    @Test
    @DisplayName("apply() should throw NullPointerException if function is null")
    void testApply_nullFunction() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertThrows(NullPointerException.class, () -> pair.apply(null));
    }

    // --- compareTo(Pair<L, R> other) tests ---
    @Test
    @DisplayName("compareTo() should return 0 for equal pairs")
    void testCompareTo_equalPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(0, pair1.compareTo(pair2));
    }

    @Test
    @DisplayName("compareTo() should compare based on left element first")
    void testCompareTo_leftDifferent() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertTrue(pair1.compareTo(pair2) < 0); // "A" < "B"
        assertTrue(pair2.compareTo(pair1) > 0); // "B" > "A"
    }

    @Test
    @DisplayName("compareTo() should compare based on right element if left elements are equal")
    void testCompareTo_rightDifferent() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 2);
        assertTrue(pair1.compareTo(pair2) < 0); // 1 < 2
        assertTrue(pair2.compareTo(pair1) > 0); // 2 > 1
    }

    @Test
    @DisplayName("compareTo() should handle null left elements")
    void testCompareTo_nullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.compareTo(pair2) < 0); // null < "A"

        Pair<String, Integer> pair3 = Pair.of(null, 1);
        Pair<String, Integer> pair4 = Pair.of(null, 2);
        assertTrue(pair3.compareTo(pair4) < 0); // 1 < 2 when lefts are null
    }

    @Test
    @DisplayName("compareTo() should handle null right elements")
    void testCompareTo_nullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.compareTo(pair2) < 0); // null < 1

        Pair<String, Integer> pair3 = Pair.of("A", null);
        Pair<String, Integer> pair4 = Pair.of("B", null);
        assertTrue(pair3.compareTo(pair4) < 0); // "A" < "B" when rights are null
    }

    @Test
    @DisplayName("compareTo() should handle both null elements")
    void testCompareTo_bothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertEquals(0, pair1.compareTo(pair2));

        Pair<String, Integer> pair3 = Pair.of(null, null);
        Pair<String, Integer> pair4 = Pair.of("A", null);
        assertTrue(pair3.compareTo(pair4) < 0);
    }

    @Test
    @DisplayName("compareTo() should throw NullPointerException if other pair is null")
    void testCompareTo_nullOther() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> pair.compareTo(null));
    }

    @Test
    @DisplayName("compareTo() should throw ClassCastException if elements are not comparable")
    void testCompareTo_incomparableElements() {
        // Using a custom class that does not implement Comparable
        class NonComparable {
            int value;

            NonComparable(int value) {
                this.value = value;
            }
        }

        Pair<NonComparable, Integer> pair1 = Pair.of(new NonComparable(1), 1);
        Pair<NonComparable, Integer> pair2 = Pair.of(new NonComparable(2), 1);

        // The JML for compareTo implies that L and R must be Comparable.
        // The implementation uses ComparableComparator.INSTANCE which will throw ClassCastException
        // if the elements are not Comparable.
        assertThrows(ClassCastException.class, () -> pair1.compareTo(pair2));

        Pair<String, NonComparable> pair3 = Pair.of("A", new NonComparable(1));
        Pair<String, NonComparable> pair4 = Pair.of("A", new NonComparable(2));
        assertThrows(ClassCastException.class, () -> pair3.compareTo(pair4));
    }

    // --- equals(Object obj) tests ---
    @Test
    @DisplayName("equals() should return true for identical pairs")
    void testEquals_identical() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertTrue(pair.equals(pair));
    }

    @Test
    @DisplayName("equals() should return true for equal pairs")
    void testEquals_equal() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
    }

    @Test
    @DisplayName("equals() should return false for different left element")
    void testEquals_differentLeft() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertFalse(pair1.equals(pair2));
    }

    @Test
    @DisplayName("equals() should return false for different right element")
    void testEquals_differentRight() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 2);
        assertFalse(pair1.equals(pair2));
    }

    @Test
    @DisplayName("equals() should return false for different both elements")
    void testEquals_differentBoth() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 2);
        assertFalse(pair1.equals(pair2));
    }

    @Test
    @DisplayName("equals() should handle null left elements correctly")
    void testEquals_nullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of(null, 1);
        Pair<String, Integer> pair3 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
        assertFalse(pair1.equals(pair3));
    }

    @Test
    @DisplayName("equals() should handle null right elements correctly")
    void testEquals_nullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        Pair<String, Integer> pair3 = Pair.of("A", 1);
        assertTrue(pair1.equals(pair2));
        assertFalse(pair1.equals(pair3));
    }

    @Test
    @DisplayName("equals() should handle both null elements correctly")
    void testEquals_bothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertTrue(pair1.equals(pair2));
    }

    @Test
    @DisplayName("equals() should return false for null object")
    void testEquals_nullObject() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertFalse(pair.equals(null));
    }

    @Test
    @DisplayName("equals() should return false for different class type")
    void testEquals_differentClass() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        String notAPair = "Not a pair";
        assertFalse(pair.equals(notAPair));
    }

    // --- getKey(), getLeft(), getRight(), getValue() tests ---
    @Test
    @DisplayName("getKey() should return the left element")
    void testGetKey() {
        Pair<String, Integer> pair = Pair.of("Key", 100);
        assertEquals("Key", pair.getKey());
    }

    @Test
    @DisplayName("getLeft() should return the left element")
    void testGetLeft() {
        Pair<String, Integer> pair = Pair.of("Left", 200);
        assertEquals("Left", pair.getLeft());
    }

    @Test
    @DisplayName("getRight() should return the right element")
    void testGetRight() {
        Pair<String, Integer> pair = Pair.of("Left", 300);
        assertEquals(300, pair.getRight());
    }

    @Test
    @DisplayName("getValue() should return the right element")
    void testGetValue() {
        Pair<String, Integer> pair = Pair.of("Key", 400);
        assertEquals(400, pair.getValue());
    }

    @Test
    @DisplayName("getKey(), getLeft(), getRight(), getValue() should handle nulls")
    void testGetters_nulls() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNull(pair.getKey());
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
        assertNull(pair.getValue());
    }

    // --- hashCode() tests ---
    @Test
    @DisplayName("hashCode() should be consistent for equal pairs")
    void testHashCode_equalPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(pair1.hashCode(), pair2.hashCode());
    }

    @Test
    @DisplayName("hashCode() should be different for unequal pairs (high probability)")
    void testHashCode_unequalPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        Pair<String, Integer> pair3 = Pair.of("A", 2);
        assertNotEquals(pair1.hashCode(), pair2.hashCode());
        assertNotEquals(pair1.hashCode(), pair3.hashCode());
    }

    @Test
    @DisplayName("hashCode() should handle null elements")
    void testHashCode_nullElements() {
        Pair<String, Integer> pair1 = Pair.of(null, 1);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        Pair<String, Integer> pair3 = Pair.of(null, null);

        // Expected hash codes based on Objects.hashCode(Object)
        assertEquals(Objects.hashCode(null) ^ Objects.hashCode(1), pair1.hashCode());
        assertEquals(Objects.hashCode("A") ^ Objects.hashCode(null), pair2.hashCode());
        assertEquals(Objects.hashCode(null) ^ Objects.hashCode(null), pair3.hashCode());

        Pair<String, Integer> pair4 = Pair.of(null, 1);
        assertEquals(pair1.hashCode(), pair4.hashCode());
    }

    // --- toString() tests ---
    @Test
    @DisplayName("toString() should return default format for non-null elements")
    void testToString_nonNull() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertEquals("(Hello,123)", pair.toString());
    }

    @Test
    @DisplayName("toString() should return default format for null left element")
    void testToString_nullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertEquals("(null,123)", pair.toString());
    }

    @Test
    @DisplayName("toString() should return default format for null right element")
    void testToString_nullRight() {
        Pair<String, Integer> pair = Pair.of("Hello", null);
        assertEquals("(Hello,null)", pair.toString());
    }

    @Test
    @DisplayName("toString() should return default format for both null elements")
    void testToString_bothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("(null,null)", pair.toString());
    }

    @Test
    @DisplayName("toString() should handle empty strings")
    void testToString_emptyStrings() {
        Pair<String, String> pair = Pair.of("", "");
        assertEquals("(,)", pair.toString());
    }

    // --- toString(String format) tests ---
    @Test
    @DisplayName("toString(format) should apply custom format for non-null elements")
    void testToString_format_nonNull() {
        Pair<String, Integer> pair = Pair.of("LeftVal", 456);
        assertEquals("L:LeftVal R:456", pair.toString("L:%s R:%s"));
    }

    @Test
    @DisplayName("toString(format) should apply custom format for null left element")
    void testToString_format_nullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 456);
        assertEquals("L:null R:456", pair.toString("L:%s R:%s"));
    }

    @Test
    @DisplayName("toString(format) should apply custom format for null right element")
    void testToString_format_nullRight() {
        Pair<String, Integer> pair = Pair.of("LeftVal", null);
        assertEquals("L:LeftVal R:null", pair.toString("L:%s R:%s"));
    }

    @Test
    @DisplayName("toString(format) should apply custom format for both null elements")
    void testToString_format_bothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("L:null R:null", pair.toString("L:%s R:%s"));
    }

    @Test
    @DisplayName("toString(format) should throw IllegalArgumentException for invalid format string")
    void testToString_format_invalidFormat() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        // %s is missing for the second argument
        assertThrows(IllegalArgumentException.class, () -> pair.toString("Left: %s"));
        // Too many %s
        assertThrows(IllegalArgumentException.class, () -> pair.toString("%s %s %s"));
    }

    @Test
    @DisplayName("toString(format) should throw NullPointerException if format is null")
    void testToString_format_nullFormat() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> pair.toString(null));
    }

    @Test
    @DisplayName("toString(format) should handle empty format string")
    void testToString_format_emptyFormat() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertEquals("", pair.toString(""));
    }
}