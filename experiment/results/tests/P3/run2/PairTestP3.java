package org.apache.commons.lang3.tuple.p3;

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

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Pair Class Unit Tests")
class PairTestP3P3 {

    // --- emptyArray() tests ---
    @Test
    @DisplayName("emptyArray() should return an empty array of Pair")
    void testEmptyArray() {
        Pair<?, ?>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    @DisplayName("emptyArray() should return the same instance for performance")
    void testEmptyArrayIsSingleton() {
        Pair<?, ?>[] array1 = Pair.emptyArray();
        Pair<?, ?>[] array2 = Pair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same instance");
    }

    // --- of(L left, R right) tests ---
    @Test
    @DisplayName("of(L, R) should create a Pair with non-null elements")
    void testOfNonNullElements() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Hello", pair.getLeft(), "Left element should match");
        assertEquals(123, pair.getRight(), "Right element should match");
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with null left element")
    void testOfNullLeftElement() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match");
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with null right element")
    void testOfNullRightElement() {
        Pair<String, Integer> pair = Pair.of("Hello", null);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Hello", pair.getLeft(), "Left element should match");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with both null elements")
    void testOfBothNullElements() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    @DisplayName("of(L, R) should handle different types correctly")
    void testOfDifferentTypes() {
        Pair<Double, Boolean> pair = Pair.of(3.14, true);
        assertEquals(3.14, pair.getLeft(), "Left element should match");
        assertTrue(pair.getRight(), "Right element should match");
    }

    // --- of(Map.Entry<L, R> pair) tests ---
    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a non-null Map.Entry")
    void testOfMapEntryNonNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 42);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Key", pair.getLeft(), "Left element should match entry key");
        assertEquals(42, pair.getRight(), "Right element should match entry value");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with null key")
    void testOfMapEntryNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 42);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(42, pair.getRight(), "Right element should match entry value");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with null value")
    void testOfMapEntryNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Key", pair.getLeft(), "Left element should match entry key");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with both nulls")
    void testOfMapEntryBothNulls() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    @DisplayName("of(Map.Entry) should throw NullPointerException if entry is null")
    void testOfMapEntryNullEntry() {
        assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- ofNonNull(L left, R right) tests ---
    @Test
    @DisplayName("ofNonNull(L, R) should create a Pair with non-null elements")
    void testOfNonNullWithNonNullElements() {
        Pair<String, Integer> pair = Pair.ofNonNull("Alpha", 1);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Alpha", pair.getLeft(), "Left element should match");
        assertEquals(1, pair.getRight(), "Right element should match");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for null left element")
    void testOfNonNullWithNullLeftElement() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 1),
                "ofNonNull() should throw NullPointerException for null left element");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for null right element")
    void testOfNonNullWithNullRightElement() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("Beta", null),
                "ofNonNull() should throw NullPointerException for null right element");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for both null elements")
    void testOfNonNullWithBothNullElements() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null elements");
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---
    @Test
    @DisplayName("accept() should execute consumer with pair elements")
    void testAcceptNormalBehavior() throws Exception {
        Pair<String, Integer> pair = Pair.of("Test", 100);
        StringBuilder sb = new StringBuilder();
        FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> sb.append(l).append(":").append(r);
        pair.accept(consumer);
        assertEquals("Test:100", sb.toString(), "Consumer should process elements correctly");
    }

    @Test
    @DisplayName("accept() should handle null elements gracefully")
    void testAcceptWithNullElements() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        StringBuilder sb = new StringBuilder();
        FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> sb.append(l).append(":").append(r);
        pair.accept(consumer);
        assertEquals("null:null", sb.toString(), "Consumer should handle null elements");
    }

    @Test
    @DisplayName("accept() should rethrow checked exception from consumer")
    void testAcceptThrowsCheckedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Simulated IO Error");
        };
        assertThrows(IOException.class, () -> pair.accept(consumer),
                "accept() should rethrow IOException from consumer");
    }

    @Test
    @DisplayName("accept() should rethrow unchecked exception from consumer")
    void testAcceptThrowsUncheckedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiConsumer<String, Integer, RuntimeException> consumer = (l, r) -> {
            throw new IllegalArgumentException("Simulated IllegalArgumentException");
        };
        assertThrows(IllegalArgumentException.class, () -> pair.accept(consumer),
                "accept() should rethrow IllegalArgumentException from consumer");
    }

    @Test
    @DisplayName("accept() should throw NullPointerException if consumer is null")
    void testAcceptNullConsumer() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertThrows(NullPointerException.class, () -> pair.accept(null),
                "accept() should throw NullPointerException if consumer is null");
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---
    @Test
    @DisplayName("apply() should return result of function application")
    void testApplyNormalBehavior() throws Exception {
        Pair<String, Integer> pair = Pair.of("Value", 200);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> l + "-" + (r * 2);
        String result = pair.apply(function);
        assertEquals("Value-400", result, "Function should apply correctly");
    }

    @Test
    @DisplayName("apply() should handle null elements gracefully")
    void testApplyWithNullElements() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> "Left: " + l + ", Right: " + r;
        String result = pair.apply(function);
        assertEquals("Left: null, Right: null", result, "Function should handle null elements");
    }

    @Test
    @DisplayName("apply() should rethrow checked exception from function")
    void testApplyThrowsCheckedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Simulated IO Error from function");
        };
        assertThrows(IOException.class, () -> pair.apply(function),
                "apply() should rethrow IOException from function");
    }

    @Test
    @DisplayName("apply() should rethrow unchecked exception from function")
    void testApplyThrowsUncheckedException() {
        Pair<String, Integer> pair = Pair.of("Error", 500);
        FailableBiFunction<String, Integer, String, RuntimeException> function = (l, r) -> {
            throw new IllegalStateException("Simulated IllegalStateException from function");
        };
        assertThrows(IllegalStateException.class, () -> pair.apply(function),
                "apply() should rethrow IllegalStateException from function");
    }

    @Test
    @DisplayName("apply() should throw NullPointerException if function is null")
    void testApplyNullFunction() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertThrows(NullPointerException.class, () -> pair.apply(null),
                "apply() should throw NullPointerException if function is null");
    }

    // --- compareTo(Pair<L, R> other) tests ---
    @Test
    @DisplayName("compareTo() should return 0 for equal pairs")
    void testCompareToEqualPairs() {
        Pair<String, Integer> pair1 = Pair.of("A", 1);
        Pair<String, Integer> pair2 = Pair.of("A", 1);
        assertEquals(0, pair1.compareTo(pair2), "Equal pairs should return 0");
    }

    @Test
    @DisplayName("compareTo() should compare based on left element first (less than)")
    void testCompareToLeftLessThan() {
        Pair<String, Integer> pair1 = Pair.of("A", 10);
        Pair<String, Integer> pair2 = Pair.of("B", 1);
        assertTrue(pair1.compareTo(pair2) < 0, "Pair1 left is less than Pair2 left");
    }

    @Test
    @DisplayName("compareTo() should compare based on left element first (greater than)")
    void testCompareToLeftGreaterThan() {
        Pair<String, Integer> pair1 = Pair.of("C", 1);
        Pair<String, Integer> pair2 = Pair.of("B", 10);
        assertTrue(pair1.compareTo(pair2) > 0, "Pair1 left is greater than Pair2 left");
    }

    @Test
    @DisplayName("compareTo() should compare based on right element if left elements are equal (less than)")
    void testCompareToRightLessThan() {
        Pair<String, Integer> pair1 = Pair.of("X", 5);
        Pair<String, Integer> pair2 = Pair.of("X", 10);
        assertTrue(pair1.compareTo(pair2) < 0, "Pair1 right is less than Pair2 right when lefts are equal");
    }

    @Test
    @DisplayName("compareTo() should compare based on right element if left elements are equal (greater than)")
    void testCompareToRightGreaterThan() {
        Pair<String, Integer> pair1 = Pair.of("Y", 15);
        Pair<String, Integer> pair2 = Pair.of("Y", 10);
        assertTrue(pair1.compareTo(pair2) > 0, "Pair1 right is greater than Pair2 right when lefts are equal");
    }

    @Test
    @DisplayName("compareTo() should handle null left elements (nulls first)")
    void testCompareToNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 10);
        Pair<String, Integer> pair2 = Pair.of("A", 5);
        assertTrue(pair1.compareTo(pair2) < 0, "Null left should come before non-null left");

        Pair<String, Integer> pair3 = Pair.of("A", 5);
        Pair<String, Integer> pair4 = Pair.of(null, 10);
        assertTrue(pair3.compareTo(pair4) > 0, "Non-null left should come after null left");
    }

    @Test
    @DisplayName("compareTo() should handle null right elements (nulls first) when lefts are equal")
    void testCompareToNullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", 5);
        assertTrue(pair1.compareTo(pair2) < 0, "Null right should come before non-null right when lefts are equal");

        Pair<String, Integer> pair3 = Pair.of("A", 5);
        Pair<String, Integer> pair4 = Pair.of("A", null);
        assertTrue(pair3.compareTo(pair4) > 0, "Non-null right should come after null right when lefts are equal");
    }

    @Test
    @DisplayName("compareTo() should handle both null left elements")
    void testCompareToBothNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 10);
        Pair<String, Integer> pair2 = Pair.of(null, 5);
        assertTrue(pair1.compareTo(pair2) > 0, "When both lefts are null, compare rights (10 > 5)");
    }

    @Test
    @DisplayName("compareTo() should handle both null right elements when lefts are equal")
    void testCompareToBothNullRight() {
        Pair<String, Integer> pair1 = Pair.of("A", null);
        Pair<String, Integer> pair2 = Pair.of("A", null);
        assertEquals(0, pair1.compareTo(pair2), "When both rights are null and lefts are equal, result is 0");
    }

    @Test
    @DisplayName("compareTo() should throw NullPointerException if other pair is null")
    void testCompareToNullOther() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> pair.compareTo(null),
                "compareTo() should throw NullPointerException for null argument");
    }

    @Test
    @DisplayName("compareTo() should throw ClassCastException if elements are not comparable")
    void testCompareToIncomparableElements() {
        // Using a custom class that doesn't implement Comparable
        class NonComparable {
            int value;
            NonComparable(int value) { this.value = value; }
            @Override public String toString() { return String.valueOf(value); }
        }

        Pair<NonComparable, Integer> pair1 = Pair.of(new NonComparable(1), 1);
        Pair<NonComparable, Integer> pair2 = Pair.of(new NonComparable(2), 1);

        // The default comparison for non-comparable types will throw ClassCastException
        assertThrows(ClassCastException.class, () -> pair1.compareTo(pair2),
                "compareTo() should throw ClassCastException if elements are not comparable");

        // Test with left comparable, right non-comparable
        Pair<String, NonComparable> pair3 = Pair.of("A", new NonComparable(1));
        Pair<String, NonComparable> pair4 = Pair.of("A", new NonComparable(2));
        assertThrows(ClassCastException.class, () -> pair3.compareTo(pair4),
                "compareTo() should throw ClassCastException if right elements are not comparable");
    }

    // --- equals(Object obj) tests ---
    @Test
    @DisplayName("equals() should return true for identical pairs")
    void testEqualsIdenticalPairs() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertTrue(pair.equals(pair), "A pair should be equal to itself");
    }

    @Test
    @DisplayName("equals() should return true for pairs with equal content")
    void testEqualsEqualContent() {
        Pair<String, Integer> pair1 = Pair.of("Hello", 123);
        Pair<String, Integer> pair2 = Pair.of("Hello", 123);
        assertTrue(pair1.equals(pair2), "Pairs with equal content should be equal");
    }

    @Test
    @DisplayName("equals() should return false for pairs with different left content")
    void testEqualsDifferentLeft() {
        Pair<String, Integer> pair1 = Pair.of("Hello", 123);
        Pair<String, Integer> pair2 = Pair.of("World", 123);
        assertFalse(pair1.equals(pair2), "Pairs with different left content should not be equal");
    }

    @Test
    @DisplayName("equals() should return false for pairs with different right content")
    void testEqualsDifferentRight() {
        Pair<String, Integer> pair1 = Pair.of("Hello", 123);
        Pair<String, Integer> pair2 = Pair.of("Hello", 456);
        assertFalse(pair1.equals(pair2), "Pairs with different right content should not be equal");
    }

    @Test
    @DisplayName("equals() should return false for pairs with different types")
    void testEqualsDifferentTypes() {
        Pair<String, Integer> pair1 = Pair.of("Hello", 123);
        Pair<String, Double> pair2 = Pair.of("Hello", 123.0);
        assertFalse(pair1.equals(pair2), "Pairs with different generic types should not be equal");
    }

    @Test
    @DisplayName("equals() should return false for null object")
    void testEqualsNullObject() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertFalse(pair.equals(null), "Pair should not be equal to null");
    }

    @Test
    @DisplayName("equals() should return false for different class type")
    void testEqualsDifferentClass() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        Object obj = "Not a Pair";
        assertFalse(pair.equals(obj), "Pair should not be equal to an object of a different class");
    }

    @Test
    @DisplayName("equals() should handle null left elements correctly")
    void testEqualsNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 123);
        Pair<String, Integer> pair2 = Pair.of(null, 123);
        Pair<String, Integer> pair3 = Pair.of("Hello", 123);
        assertTrue(pair1.equals(pair2), "Pairs with null left and equal right should be equal");
        assertFalse(pair1.equals(pair3), "Pair with null left should not equal pair with non-null left");
    }

    @Test
    @DisplayName("equals() should handle null right elements correctly")
    void testEqualsNullRight() {
        Pair<String, Integer> pair1 = Pair.of("Hello", null);
        Pair<String, Integer> pair2 = Pair.of("Hello", null);
        Pair<String, Integer> pair3 = Pair.of("Hello", 123);
        assertTrue(pair1.equals(pair2), "Pairs with null right and equal left should be equal");
        assertFalse(pair1.equals(pair3), "Pair with null right should not equal pair with non-null right");
    }

    @Test
    @DisplayName("equals() should handle both null elements correctly")
    void testEqualsBothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertTrue(pair1.equals(pair2), "Pairs with both null elements should be equal");
    }

    // --- getKey() tests ---
    @Test
    @DisplayName("getKey() should return the left element")
    void testGetKey() {
        Pair<String, Integer> pair = Pair.of("Key", 10);
        assertEquals("Key", pair.getKey(), "getKey() should return the left element");
    }

    @Test
    @DisplayName("getKey() should return null if left element is null")
    void testGetKeyNull() {
        Pair<String, Integer> pair = Pair.of(null, 10);
        assertNull(pair.getKey(), "getKey() should return null if left element is null");
    }

    // --- getLeft() tests ---
    @Test
    @DisplayName("getLeft() should return the left element")
    void testGetLeft() {
        Pair<String, Integer> pair = Pair.of("LeftValue", 20);
        assertEquals("LeftValue", pair.getLeft(), "getLeft() should return the left element");
    }

    @Test
    @DisplayName("getLeft() should return null if left element is null")
    void testGetLeftNull() {
        Pair<String, Integer> pair = Pair.of(null, 20);
        assertNull(pair.getLeft(), "getLeft() should return null if left element is null");
    }

    // --- getRight() tests ---
    @Test
    @DisplayName("getRight() should return the right element")
    void testGetRight() {
        Pair<String, Integer> pair = Pair.of("RightValue", 30);
        assertEquals(30, pair.getRight(), "getRight() should return the right element");
    }

    @Test
    @DisplayName("getRight() should return null if right element is null")
    void testGetRightNull() {
        Pair<String, Integer> pair = Pair.of("RightValue", null);
        assertNull(pair.getRight(), "getRight() should return null if right element is null");
    }

    // --- getValue() tests ---
    @Test
    @DisplayName("getValue() should return the right element")
    void testGetValue() {
        Pair<String, Integer> pair = Pair.of("Value", 40);
        assertEquals(40, pair.getValue(), "getValue() should return the right element");
    }

    @Test
    @DisplayName("getValue() should return null if right element is null")
    void testGetValueNull() {
        Pair<String, Integer> pair = Pair.of("Value", null);
        assertNull(pair.getValue(), "getValue() should return null if right element is null");
    }

    // --- hashCode() tests ---
    @Test
    @DisplayName("hashCode() should be consistent for equal pairs")
    void testHashCodeConsistency() {
        Pair<String, Integer> pair1 = Pair.of("Hash", 100);
        Pair<String, Integer> pair2 = Pair.of("Hash", 100);
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be equal for equal pairs");
    }

    @Test
    @DisplayName("hashCode() should be different for unequal pairs")
    void testHashCodeDifference() {
        Pair<String, Integer> pair1 = Pair.of("Hash1", 100);
        Pair<String, Integer> pair2 = Pair.of("Hash2", 100);
        assertNotEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be different for unequal pairs");
    }

    @Test
    @DisplayName("hashCode() should handle null left element")
    void testHashCodeNullLeft() {
        Pair<String, Integer> pair1 = Pair.of(null, 100);
        Pair<String, Integer> pair2 = Pair.of(null, 100);
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be equal for pairs with null left and equal right");
    }

    @Test
    @DisplayName("hashCode() should handle null right element")
    void testHashCodeNullRight() {
        Pair<String, Integer> pair1 = Pair.of("Hash", null);
        Pair<String, Integer> pair2 = Pair.of("Hash", null);
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be equal for pairs with null right and equal left");
    }

    @Test
    @DisplayName("hashCode() should handle both null elements")
    void testHashCodeBothNull() {
        Pair<String, Integer> pair1 = Pair.of(null, null);
        Pair<String, Integer> pair2 = Pair.of(null, null);
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be equal for pairs with both null elements");
    }

    // --- toString() tests ---
    @Test
    @DisplayName("toString() should return default format for non-null elements")
    void testToStringNonNullElements() {
        Pair<String, Integer> pair = Pair.of("Alpha", 1);
        assertEquals("(Alpha,1)", pair.toString(), "toString() should return (left,right)");
    }

    @Test
    @DisplayName("toString() should return default format for null left element")
    void testToStringNullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 1);
        assertEquals("(null,1)", pair.toString(), "toString() should handle null left element");
    }

    @Test
    @DisplayName("toString() should return default format for null right element")
    void testToStringNullRight() {
        Pair<String, Integer> pair = Pair.of("Alpha", null);
        assertEquals("(Alpha,null)", pair.toString(), "toString() should handle null right element");
    }

    @Test
    @DisplayName("toString() should return default format for both null elements")
    void testToStringBothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("(null,null)", pair.toString(), "toString() should handle both null elements");
    }

    // --- toString(String format) tests ---
    @Test
    @DisplayName("toString(format) should apply custom format string")
    void testToStringWithCustomFormat() {
        Pair<String, Integer> pair = Pair.of("Custom", 99);
        assertEquals("L:Custom R:99", pair.toString("L:%s R:%s"), "toString(format) should apply custom format");
    }

    @Test
    @DisplayName("toString(format) should handle null elements with custom format")
    void testToStringWithCustomFormatAndNulls() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("Left is null, Right is null", pair.toString("Left is %s, Right is %s"),
                "toString(format) should handle nulls with custom format");
    }

    @Test
    @DisplayName("toString(format) should throw NullPointerException if format is null")
    void testToStringNullFormat() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertThrows(NullPointerException.class, () -> pair.toString(null),
                "toString(format) should throw NullPointerException for null format string");
    }

    @Test
    @DisplayName("toString(format) should throw IllegalFormatException if format is invalid")
    void testToStringInvalidFormat() {
        Pair<String, Integer> pair = Pair.of("Test", 1);
        assertThrows(java.util.IllegalFormatException.class, () -> pair.toString("%d %s"),
                "toString(format) should throw IllegalFormatException for invalid format string");
    }

    @Test
    @DisplayName("toString(format) should handle format string with single placeholder")
    void testToStringSinglePlaceholderFormat() {
        Pair<String, Integer> pair = Pair.of("Single", 1);
        assertEquals("Left: Single", pair.toString("Left: %s"),
                "toString(format) should handle single placeholder (using left)");
        assertEquals("Right: 1", pair.toString("Right: %2$s"),
                "toString(format) should handle single placeholder (using right)");
    }

    @Test
    @DisplayName("toString(format) should handle format string with more placeholders than arguments")
    void testToStringMorePlaceholders() {
        Pair<String, Integer> pair = Pair.of("Extra", 2);
        // This will typically throw MissingFormatArgumentException, but String.format handles it by reusing args
        // The JML spec doesn't explicitly cover this, but it's good to know behavior.
        // String.format("%s %s %s", "a", "b") -> "a b a"
        // String.format("%s %s %s", left, right) -> left right left
        assertEquals("Extra 2 Extra", pair.toString("%s %s %s"),
                "toString(format) should reuse arguments if more placeholders than args");
    }

    @Test
    @DisplayName("toString(format) should handle format string with fewer placeholders than arguments")
    void testToStringFewerPlaceholders() {
        Pair<String, Integer> pair = Pair.of("Fewer", 3);
        assertEquals("Fewer", pair.toString("%s"),
                "toString(format) should use only first argument if fewer placeholders");
    }
}