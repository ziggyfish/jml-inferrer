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

    // Helper for creating a simple Map.Entry
    private <L, R> Map.Entry<L, R> createMapEntry(L left, R right) {
        return new AbstractMap.SimpleEntry<>(left, right);
    }

    // --- emptyArray() tests ---
    @Test
    void testEmptyArray() {
        Pair<String, Integer>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    void testEmptyArrayIsImmutable() {
        Pair<String, Integer>[] array1 = Pair.emptyArray();
        Pair<String, Integer>[] array2 = Pair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same instance for performance");
    }

    // --- of(L left, R right) tests ---
    @Test
    void testOfNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertNotNull(pair, "Pair.of() should not return null for non-null inputs");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair, "Pair.of() should allow null left element");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullRight() {
        Pair<String, Integer> pair = Pair.of("Hello", null);
        assertNotNull(pair, "Pair.of() should allow null right element");
        assertEquals("Hello", pair.getLeft(), "Left element should match input");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithBothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair, "Pair.of() should allow both null elements");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithDifferentTypes() {
        Pair<Integer, Boolean> pair = Pair.of(42, true);
        assertEquals(42, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---
    @Test
    void testOfMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = createMapEntry("World", 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair.of(Map.Entry) should not return null for non-null entry");
        assertEquals("World", pair.getLeft(), "Left element should match entry's key");
        assertEquals(456, pair.getRight(), "Right element should match entry's value");
    }

    @Test
    void testOfMapEntryWithNullEntry() {
        // JML spec for of(Map.Entry) does not explicitly forbid null entry,
        // but it's good practice to check how it behaves.
        // Commons Lang's implementation typically handles this by creating a Pair with nulls.
        Pair<String, Integer> pair = Pair.of((Map.Entry<String, Integer>) null);
        assertNotNull(pair, "Pair.of(null Map.Entry) should return a Pair with nulls");
        assertNull(pair.getLeft(), "Left element should be null when entry is null");
        assertNull(pair.getRight(), "Right element should be null when entry is null");
    }

    @Test
    void testOfMapEntryWithNullKeyInEntry() {
        Map.Entry<String, Integer> entry = createMapEntry(null, 789);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(789, pair.getRight());
    }

    @Test
    void testOfMapEntryWithNullValueInEntry() {
        Map.Entry<String, Integer> entry = createMapEntry("Key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("Key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryWithBothNullInEntry() {
        Map.Entry<String, Integer> entry = createMapEntry(null, null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    // --- ofNonNull(L left, R right) tests ---
    @Test
    void testOfNonNullNormalBehavior() {
        Pair<String, Integer> pair = Pair.ofNonNull("Non", 101);
        assertNotNull(pair);
        assertEquals("Non", pair.getLeft());
        assertEquals(101, pair.getRight());
    }

    @Test
    void testOfNonNullWithNullLeft() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 101),
                "ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNullWithNullRight() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("Non", null),
                "ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNullWithBothNull() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                "ofNonNull() should throw NullPointerException for both null");
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---
    @Test
    void testAcceptNormalBehavior() throws Exception {
        Pair<String, Integer> pair = Pair.of("Test", 123);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicReference<Integer> consumedRight = new AtomicReference<>();

        FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> {
            consumedLeft.set(l);
            consumedRight.set(r);
        };

        pair.accept(consumer);

        assertEquals("Test", consumedLeft.get(), "Consumer should receive the left value");
        assertEquals(123, consumedRight.get(), "Consumer should receive the right value");
    }

    @Test
    void testAcceptWithNullConsumer() {
        Pair<String, Integer> pair = Pair.of("Test", 123);
        assertThrows(NullPointerException.class, () -> pair.accept(null),
                "accept() should throw NullPointerException for null consumer");
    }

    @Test
    void testAcceptConsumerThrowsException() {
        Pair<String, Integer> pair = Pair.of("Test", 123);
        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Consumer failed");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.accept(consumer),
                "accept() should rethrow exception from consumer");
        assertEquals("Consumer failed", thrown.getMessage());
    }

    @Test
    void testAcceptWithNullValuesInPair() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicReference<Integer> consumedRight = new AtomicReference<>();

        FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> {
            consumedLeft.set(l);
            consumedRight.set(r);
        };

        pair.accept(consumer);

        assertNull(consumedLeft.get(), "Consumer should receive null left value");
        assertNull(consumedRight.get(), "Consumer should receive null right value");
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---
    @Test
    void testApplyNormalBehavior() throws Exception {
        Pair<String, Integer> pair = Pair.of("Value", 42);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> l + "-" + r;

        String result = pair.apply(function);
        assertEquals("Value-42", result, "Function should apply correctly and return result");
    }

    @Test
    void testApplyWithNullFunction() {
        Pair<String, Integer> pair = Pair.of("Value", 42);
        assertThrows(NullPointerException.class, () -> pair.apply(null),
                "apply() should throw NullPointerException for null function");
    }

    @Test
    void testApplyFunctionThrowsException() {
        Pair<String, Integer> pair = Pair.of("Value", 42);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Function failed");
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.apply(function),
                "apply() should rethrow exception from function");
        assertEquals("Function failed", thrown.getMessage());
    }

    @Test
    void testApplyWithNullValuesInPair() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) ->
                (l == null ? "null" : l) + "-" + (r == null ? "null" : r);

        String result = pair.apply(function);
        assertEquals("null-null", result, "Function should handle null values correctly");
    }

    @Test
    void testApplyFunctionReturnsNull() throws Exception {
        Pair<String, Integer> pair = Pair.of("A", 1);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> null;

        assertNull(pair.apply(function), "Function can return null");
    }

    // --- compareTo(Pair<L, R> other) tests ---
    @Test
    void testCompareToEqualPairs() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("A", 1);
        assertEquals(0, p1.compareTo(p2), "Equal pairs should return 0");
    }

    @Test
    void testCompareToDifferentLeft() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("B", 1);
        assertTrue(p1.compareTo(p2) < 0, "Pair with smaller left should be less");
        assertTrue(p2.compareTo(p1) > 0, "Pair with larger left should be greater");
    }

    @Test
    void testCompareToDifferentRight() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("A", 2);
        assertTrue(p1.compareTo(p2) < 0, "Pair with smaller right should be less when left is equal");
        assertTrue(p2.compareTo(p1) > 0, "Pair with larger right should be greater when left is equal");
    }

    @Test
    void testCompareToDifferentBoth() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("B", 0); // Left is greater, right is smaller
        assertTrue(p1.compareTo(p2) < 0, "Comparison should prioritize left element");
    }

    @Test
    void testCompareToWithNullLeft() {
        Pair<String, Integer> p1 = Pair.of(null, 1);
        Pair<String, Integer> p2 = Pair.of("A", 1);
        assertTrue(p1.compareTo(p2) < 0, "Null left should be less than non-null left");
        assertTrue(p2.compareTo(p1) > 0, "Non-null left should be greater than null left");

        Pair<String, Integer> p3 = Pair.of(null, 1);
        assertEquals(0, p1.compareTo(p3), "Two pairs with null left and equal right should be equal");
    }

    @Test
    void testCompareToWithNullRight() {
        Pair<String, Integer> p1 = Pair.of("A", null);
        Pair<String, Integer> p2 = Pair.of("A", 1);
        assertTrue(p1.compareTo(p2) < 0, "Null right should be less than non-null right when left is equal");
        assertTrue(p2.compareTo(p1) > 0, "Non-null right should be greater than null right when left is equal");

        Pair<String, Integer> p3 = Pair.of("A", null);
        assertEquals(0, p1.compareTo(p3), "Two pairs with null right and equal left should be equal");
    }

    @Test
    void testCompareToWithBothNulls() {
        Pair<String, Integer> p1 = Pair.of(null, null);
        Pair<String, Integer> p2 = Pair.of(null, null);
        assertEquals(0, p1.compareTo(p2), "Two pairs with both nulls should be equal");

        Pair<String, Integer> p3 = Pair.of("A", null);
        assertTrue(p1.compareTo(p3) < 0, "Null left is less than non-null left");
        assertTrue(p3.compareTo(p1) > 0);

        Pair<String, Integer> p4 = Pair.of(null, 1);
        assertTrue(p1.compareTo(p4) < 0, "Null right is less than non-null right when left is equal");
        assertTrue(p4.compareTo(p1) > 0);
    }

    @Test
    void testCompareToWithNullOther() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> p1.compareTo(null),
                "compareTo() should throw NullPointerException for null 'other' pair");
    }

    @Test
    void testCompareToWithNonComparableElements() {
        // This test relies on the default Comparable implementation for the elements.
        // If elements are not Comparable, it will throw ClassCastException.
        // The JML spec implies L and R are Comparable, but Java generics don't enforce it directly on Pair.
        // The runtime behavior is to use ComparableUtils.compare which handles nulls and expects Comparable.
        Pair<Object, Object> p1 = Pair.of(new Object(), 1);
        Pair<Object, Object> p2 = Pair.of(new Object(), 1);

        // This will throw ClassCastException because Object is not Comparable
        assertThrows(ClassCastException.class, () -> p1.compareTo(p2),
                "compareTo() should throw ClassCastException if elements are not comparable");
    }

    // --- equals(Object obj) tests ---
    @Test
    void testEqualsSameInstance() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        assertTrue(p1.equals(p1), "A pair should be equal to itself");
    }

    @Test
    void testEqualsEqualPairs() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("A", 1);
        assertTrue(p1.equals(p2), "Pairs with same left and right should be equal");
        assertTrue(p2.equals(p1), "Equals should be symmetric");
    }

    @Test
    void testEqualsDifferentLeft() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("B", 1);
        assertFalse(p1.equals(p2), "Pairs with different left should not be equal");
    }

    @Test
    void testEqualsDifferentRight() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("A", 2);
        assertFalse(p1.equals(p2), "Pairs with different right should not be equal");
    }

    @Test
    void testEqualsDifferentBoth() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("B", 2);
        assertFalse(p1.equals(p2), "Pairs with different both should not be equal");
    }

    @Test
    void testEqualsWithNullLeft() {
        Pair<String, Integer> p1 = Pair.of(null, 1);
        Pair<String, Integer> p2 = Pair.of(null, 1);
        assertTrue(p1.equals(p2), "Pairs with null left and equal right should be equal");

        Pair<String, Integer> p3 = Pair.of("A", 1);
        assertFalse(p1.equals(p3), "Pair with null left should not equal pair with non-null left");
    }

    @Test
    void testEqualsWithNullRight() {
        Pair<String, Integer> p1 = Pair.of("A", null);
        Pair<String, Integer> p2 = Pair.of("A", null);
        assertTrue(p1.equals(p2), "Pairs with null right and equal left should be equal");

        Pair<String, Integer> p3 = Pair.of("A", 1);
        assertFalse(p1.equals(p3), "Pair with null right should not equal pair with non-null right");
    }

    @Test
    void testEqualsWithBothNulls() {
        Pair<String, Integer> p1 = Pair.of(null, null);
        Pair<String, Integer> p2 = Pair.of(null, null);
        assertTrue(p1.equals(p2), "Pairs with both nulls should be equal");
    }

    @Test
    void testEqualsWithNullObject() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        assertFalse(p1.equals(null), "A pair should not be equal to null");
    }

    @Test
    void testEqualsWithDifferentClass() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        String s = "Not a Pair";
        assertFalse(p1.equals(s), "A pair should not be equal to an object of a different class");
    }

    // --- getKey(), getLeft(), getRight(), getValue() tests ---
    @Test
    void testGettersNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Key", 100);
        assertEquals("Key", pair.getKey(), "getKey() should return the left value");
        assertEquals("Key", pair.getLeft(), "getLeft() should return the left value");
        assertEquals(100, pair.getRight(), "getRight() should return the right value");
        assertEquals(100, pair.getValue(), "getValue() should return the right value");
    }

    @Test
    void testGettersWithNullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNull(pair.getKey(), "getKey() should return null if left is null");
        assertNull(pair.getLeft(), "getLeft() should return null if left is null");
        assertNull(pair.getRight(), "getRight() should return null if right is null");
        assertNull(pair.getValue(), "getValue() should return null if right is null");
    }

    // --- hashCode() tests ---
    @Test
    void testHashCodeConsistency() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("A", 1);
        assertEquals(p1.hashCode(), p2.hashCode(), "Equal pairs must have equal hash codes");
    }

    @Test
    void testHashCodeDifferentPairs() {
        Pair<String, Integer> p1 = Pair.of("A", 1);
        Pair<String, Integer> p2 = Pair.of("B", 1);
        Pair<String, Integer> p3 = Pair.of("A", 2);
        assertNotEquals(p1.hashCode(), p2.hashCode(), "Hash codes should differ for different left values");
        assertNotEquals(p1.hashCode(), p3.hashCode(), "Hash codes should differ for different right values");
    }

    @Test
    void testHashCodeWithNullValues() {
        Pair<String, Integer> p1 = Pair.of(null, 1);
        Pair<String, Integer> p2 = Pair.of(null, 1);
        assertEquals(p1.hashCode(), p2.hashCode(), "Pairs with null left and equal right should have equal hash codes");

        Pair<String, Integer> p3 = Pair.of("A", null);
        Pair<String, Integer> p4 = Pair.of("A", null);
        assertEquals(p3.hashCode(), p4.hashCode(), "Pairs with null right and equal left should have equal hash codes");

        Pair<String, Integer> p5 = Pair.of(null, null);
        Pair<String, Integer> p6 = Pair.of(null, null);
        assertEquals(p5.hashCode(), p6.hashCode(), "Pairs with both nulls should have equal hash codes");

        // Check against non-null versions
        assertNotEquals(p1.hashCode(), Pair.of("X", 1).hashCode());
        assertNotEquals(p3.hashCode(), Pair.of("A", 99).hashCode());
    }

    // --- toString() tests ---
    @Test
    void testToStringNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertEquals("(Hello,123)", pair.toString(), "toString() should produce expected format");
    }

    @Test
    void testToStringWithNullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("(null,null)", pair.toString(), "toString() should handle null values gracefully");

        Pair<String, Integer> pairLeftNull = Pair.of(null, 456);
        assertEquals("(null,456)", pairLeftNull.toString());

        Pair<String, Integer> pairRightNull = Pair.of("World", null);
        assertEquals("(World,null)", pairRightNull.toString());
    }

    @Test
    void testToStringWithSpecialCharacters() {
        Pair<String, String> pair = Pair.of("(", ",)");
        assertEquals("((,,))", pair.toString(), "toString() should handle special characters in values");
    }

    // --- toString(String format) tests ---
    @Test
    void testToStringFormatNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertEquals("Hello=123", pair.toString("%s=%s"), "toString(format) should apply the format string");
        assertEquals("[Hello|123]", pair.toString("[%s|%s]"));
    }

    @Test
    void testToStringFormatWithNullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("null-null", pair.toString("%s-%s"), "toString(format) should handle null values in format");

        Pair<String, Integer> pairLeftNull = Pair.of(null, 456);
        assertEquals("null:456", pairLeftNull.toString("%s:%s"));

        Pair<String, Integer> pairRightNull = Pair.of("World", null);
        assertEquals("World->null", pairRightNull.toString("%s->%s"));
    }

    @Test
    void testToStringFormatWithNullFormat() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        assertThrows(NullPointerException.class, () -> pair.toString(null),
                "toString(null) should throw NullPointerException");
    }

    @Test
    void testToStringFormatWithInvalidFormatString() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        // %s is expected twice, but only one is provided
        assertThrows(java.util.MissingFormatArgumentException.class, () -> pair.toString("%s"),
                "toString(format) should throw MissingFormatArgumentException for insufficient format specifiers");
        // Too many format specifiers
        assertThrows(java.util.UnknownFormatConversionException.class, () -> pair.toString("%s%s%s"),
                "toString(format) should throw UnknownFormatConversionException for too many format specifiers (if not handled by String.format)");
        // Note: String.format("%s%s%s", "a", "b") would throw MissingFormatArgumentException.
        // String.format("%s%s", "a", "b", "c") would ignore the extra argument.
        // The Pair implementation uses String.format(format, getLeft(), getRight()).
        // So, if format has too many %s, it will throw MissingFormatArgumentException.
        // If format has too few %s, it will throw MissingFormatArgumentException.
        // Let's refine this:
        assertThrows(java.util.MissingFormatArgumentException.class, () -> pair.toString("%s %s %s"),
                "toString(format) should throw MissingFormatArgumentException if format requires more arguments than provided");
    }

    @Test
    void testToStringFormatWithEmptyFormatString() {
        Pair<String, Integer> pair = Pair.of("Hello", 123);
        // String.format("") returns ""
        assertEquals("", pair.toString(""), "toString(\"\") should return an empty string");
    }

    // --- Additional tests for immutability (where applicable) ---
    @Test
    void testPairImmutability() {
        String left = "InitialLeft";
        Integer right = 1;
        Pair<String, Integer> pair = Pair.of(left, right);

        // Attempt to modify the original objects (if they were mutable)
        // For String and Integer, they are immutable, so this is more conceptual.
        // The Pair itself should not allow modification of its internal left/right references.
        left = "ModifiedLeft";
        right = 2;

        assertEquals("InitialLeft", pair.getLeft(), "Pair's left value should not change after original variable modification");
        assertEquals(1, pair.getRight(), "Pair's right value should not change after original variable modification");

        // If L or R were mutable objects, changes to them would be reflected,
        // but the Pair itself doesn't offer methods to change its L or R references.
        StringBuilder sbLeft = new StringBuilder("MutableLeft");
        Pair<StringBuilder, Integer> mutablePair = Pair.of(sbLeft, 10);
        sbLeft.append("Appended");

        assertEquals("MutableLeftAppended", mutablePair.getLeft().toString(),
                "If elements are mutable, changes to them are reflected, but Pair's reference is immutable.");
    }
}