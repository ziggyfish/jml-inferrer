package org.apache.commons.lang3.tuple.p3;

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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

class PairTestP3P3 {

    // --- emptyArray() tests ---
    @Test
    void testEmptyArray() {
        Pair<?, ?>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
        // Verify it's always the same instance (or at least referentially equal)
        assertSame(Pair.emptyArray(), emptyArray, "emptyArray() should return the same instance");
    }

    // --- of(L left, R right) tests ---
    @Test
    void testOfNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("hello", 123);
        assertNotNull(pair, "Pair.of() should not return null for non-null inputs");
        assertEquals("hello", pair.getLeft(), "Left element should match input");
        assertEquals(123, pair.getRight(), "Right element should match input");
        assertEquals("hello", pair.getKey(), "Key should match left element");
        assertEquals(123, pair.getValue(), "Value should match right element");
    }

    @Test
    void testOfWithNullLeft() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair, "Pair.of() should not return null for null left input");
        assertNull(pair.getLeft(), "Left element should be null");
        assertEquals(123, pair.getRight(), "Right element should match input");
    }

    @Test
    void testOfWithNullRight() {
        Pair<String, Integer> pair = Pair.of("hello", null);
        assertNotNull(pair, "Pair.of() should not return null for null right input");
        assertEquals("hello", pair.getLeft(), "Left element should match input");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithBothNull() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair, "Pair.of() should not return null for both null inputs");
        assertNull(pair.getLeft(), "Left element should be null");
        assertNull(pair.getRight(), "Right element should be null");
    }

    @Test
    void testOfWithDifferentTypes() {
        Pair<Double, Boolean> pair = Pair.of(3.14, true);
        assertEquals(3.14, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---
    @Test
    void testOfMapEntryNormalBehavior() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair.of(Map.Entry) should not return null");
        assertEquals("key", pair.getLeft(), "Left element should match entry key");
        assertEquals(456, pair.getRight(), "Right element should match entry value");
    }

    @Test
    void testOfMapEntryWithNullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(456, pair.getRight());
    }

    @Test
    void testOfMapEntryWithNullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("key", pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryWithBothNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
    }

    @Test
    void testOfMapEntryNullInput() {
        assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null),
                "Pair.of(null Map.Entry) should throw NullPointerException");
    }

    @Test
    void testOfMapEntryFromHashMap() {
        Map<String, Integer> map = new HashMap<>();
        map.put("test", 100);
        Map.Entry<String, Integer> entry = map.entrySet().iterator().next();
        Pair<String, Integer> pair = Pair.of(entry);
        assertEquals("test", pair.getLeft());
        assertEquals(100, pair.getRight());
    }

    // --- ofNonNull(L left, R right) tests ---
    @Test
    void testOfNonNullNormalBehavior() {
        Pair<String, Integer> pair = Pair.ofNonNull("nonnull", 789);
        assertNotNull(pair);
        assertEquals("nonnull", pair.getLeft());
        assertEquals(789, pair.getRight());
    }

    @Test
    void testOfNonNullWithNullLeft() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 789),
                "Pair.ofNonNull() should throw NullPointerException for null left");
    }

    @Test
    void testOfNonNullWithNullRight() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("nonnull", null),
                "Pair.ofNonNull() should throw NullPointerException for null right");
    }

    @Test
    void testOfNonNullWithBothNull() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                "Pair.ofNonNull() should throw NullPointerException for both null");
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---
    @Test
    void testAcceptNormalBehavior() throws IOException {
        Pair<String, Integer> pair = Pair.of("data", 10);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicInteger consumedRight = new AtomicInteger();

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            consumedLeft.set(l);
            consumedRight.set(r);
        };

        pair.accept(consumer);

        assertEquals("data", consumedLeft.get());
        assertEquals(10, consumedRight.get());
    }

    @Test
    void testAcceptWithNullElements() throws IOException {
        Pair<String, Integer> pair = Pair.of(null, null);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicInteger consumedRight = new AtomicInteger(-1);

        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            consumedLeft.set(l);
            if (r != null) {
                consumedRight.set(r);
            }
        };

        pair.accept(consumer);

        assertNull(consumedLeft.get());
        assertEquals(-1, consumedRight.get()); // Should remain -1 as r is null
    }

    @Test
    void testAcceptConsumerThrowsException() {
        Pair<String, Integer> pair = Pair.of("error", 500);
        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Simulated consumer error: " + l + ", " + r);
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.accept(consumer),
                "accept() should rethrow the exception from the consumer");
        assertTrue(thrown.getMessage().contains("Simulated consumer error: error, 500"));
    }

    @Test
    void testAcceptNullConsumer() {
        Pair<String, Integer> pair = Pair.of("test", 1);
        assertThrows(NullPointerException.class, () -> pair.accept(null),
                "accept() should throw NullPointerException for null consumer");
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---
    @Test
    void testApplyNormalBehavior() throws IOException {
        Pair<String, Integer> pair = Pair.of("value", 20);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> l + "-" + (r * 2);

        String result = pair.apply(function);
        assertEquals("value-40", result);
    }

    @Test
    void testApplyWithNullElements() throws IOException {
        Pair<String, Integer> pair = Pair.of(null, null);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            String leftStr = (l == null) ? "null_left" : l;
            String rightStr = (r == null) ? "null_right" : String.valueOf(r);
            return leftStr + "_" + rightStr;
        };

        String result = pair.apply(function);
        assertEquals("null_left_null_right", result);
    }

    @Test
    void testApplyFunctionReturnsNull() throws IOException {
        Pair<String, Integer> pair = Pair.of("test", 1);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> null;

        assertNull(pair.apply(function));
    }

    @Test
    void testApplyFunctionThrowsException() {
        Pair<String, Integer> pair = Pair.of("fail", 100);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Function failed for: " + l + ", " + r);
        };

        IOException thrown = assertThrows(IOException.class, () -> pair.apply(function),
                "apply() should rethrow the exception from the function");
        assertTrue(thrown.getMessage().contains("Function failed for: fail, 100"));
    }

    @Test
    void testApplyNullFunction() {
        Pair<String, Integer> pair = Pair.of("test", 1);
        assertThrows(NullPointerException.class, () -> pair.apply(null),
                "apply() should throw NullPointerException for null function");
    }

    // --- compareTo(Pair<L, R> other) tests ---
    @Test
    void testCompareToEqualPairs() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("apple", 1);
        assertEquals(0, p1.compareTo(p2));
    }

    @Test
    void testCompareToDifferentLeft() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("banana", 1);
        assertTrue(p1.compareTo(p2) < 0); // "apple" < "banana"
        assertTrue(p2.compareTo(p1) > 0);
    }

    @Test
    void testCompareToDifferentRight() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("apple", 2);
        assertTrue(p1.compareTo(p2) < 0); // 1 < 2
        assertTrue(p2.compareTo(p1) > 0);
    }

    @Test
    void testCompareToDifferentBoth() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("banana", 0);
        assertTrue(p1.compareTo(p2) < 0); // "apple" < "banana" (right value doesn't matter if left is different)
    }

    @Test
    void testCompareToWithNullLeft() {
        Pair<String, Integer> p1 = Pair.of(null, 1);
        Pair<String, Integer> p2 = Pair.of("apple", 1);
        assertTrue(p1.compareTo(p2) < 0); // null is considered less than non-null
        assertTrue(p2.compareTo(p1) > 0);

        Pair<String, Integer> p3 = Pair.of(null, 1);
        Pair<String, Integer> p4 = Pair.of(null, 2);
        assertTrue(p3.compareTo(p4) < 0); // null left, compare right: 1 < 2
        assertTrue(p4.compareTo(p3) > 0);
    }

    @Test
    void testCompareToWithNullRight() {
        Pair<String, Integer> p1 = Pair.of("apple", null);
        Pair<String, Integer> p2 = Pair.of("apple", 1);
        assertTrue(p1.compareTo(p2) < 0); // null is considered less than non-null
        assertTrue(p2.compareTo(p1) > 0);

        Pair<String, Integer> p3 = Pair.of("apple", null);
        Pair<String, Integer> p4 = Pair.of("apple", null);
        assertEquals(0, p3.compareTo(p4));
    }

    @Test
    void testCompareToWithBothNullElements() {
        Pair<String, Integer> p1 = Pair.of(null, null);
        Pair<String, Integer> p2 = Pair.of(null, null);
        assertEquals(0, p1.compareTo(p2));

        Pair<String, Integer> p3 = Pair.of(null, null);
        Pair<String, Integer> p4 = Pair.of("a", null);
        assertTrue(p3.compareTo(p4) < 0);
    }

    @Test
    void testCompareToNullOther() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        assertThrows(NullPointerException.class, () -> p1.compareTo(null),
                "compareTo() should throw NullPointerException for null other pair");
    }

    @Test
    void testCompareToNonComparableElements() {
        // This test relies on the fact that Pair uses Comparable for comparison.
        // If elements are not Comparable, a ClassCastException should occur.
        Pair<Object, Object> p1 = Pair.of(new Object(), new Object());
        Pair<Object, Object> p2 = Pair.of(new Object(), new Object());

        // The default implementation of Pair uses ComparableUtils.compare which handles non-comparable types
        // by throwing ClassCastException if they are not null and not comparable.
        // However, if both are non-comparable and not null, it might throw.
        // Let's test with a specific scenario where it's expected to fail.
        Pair<NonComparable, Integer> nc1 = Pair.of(new NonComparable(1), 1);
        Pair<NonComparable, Integer> nc2 = Pair.of(new NonComparable(2), 1);

        assertThrows(ClassCastException.class, () -> nc1.compareTo(nc2),
                "compareTo() should throw ClassCastException if elements are not Comparable");

        // Test with a mix, where one is comparable and the other isn't
        Pair<String, NonComparable> mix1 = Pair.of("A", new NonComparable(1));
        Pair<String, NonComparable> mix2 = Pair.of("A", new NonComparable(2));
        assertThrows(ClassCastException.class, () -> mix1.compareTo(mix2),
                "compareTo() should throw ClassCastException if right element is not Comparable");
    }

    private static class NonComparable {
        int value;

        NonComparable(int value) {
            this.value = value;
        }
    }

    // --- equals(Object obj) tests ---
    @Test
    void testEqualsSameInstance() {
        Pair<String, Integer> p = Pair.of("test", 1);
        assertTrue(p.equals(p));
    }

    @Test
    void testEqualsNullObject() {
        Pair<String, Integer> p = Pair.of("test", 1);
        assertFalse(p.equals(null));
    }

    @Test
    void testEqualsDifferentClass() {
        Pair<String, Integer> p = Pair.of("test", 1);
        assertFalse(p.equals("not a pair"));
    }

    @Test
    void testEqualsEqualPairs() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("apple", 1);
        assertTrue(p1.equals(p2));
        assertTrue(p2.equals(p1));
    }

    @Test
    void testEqualsDifferentLeft() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("banana", 1);
        assertFalse(p1.equals(p2));
    }

    @Test
    void testEqualsDifferentRight() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("apple", 2);
        assertFalse(p1.equals(p2));
    }

    @Test
    void testEqualsDifferentBoth() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("banana", 2);
        assertFalse(p1.equals(p2));
    }

    @Test
    void testEqualsWithNullLeft() {
        Pair<String, Integer> p1 = Pair.of(null, 1);
        Pair<String, Integer> p2 = Pair.of(null, 1);
        assertTrue(p1.equals(p2));

        Pair<String, Integer> p3 = Pair.of(null, 1);
        Pair<String, Integer> p4 = Pair.of("apple", 1);
        assertFalse(p3.equals(p4));
    }

    @Test
    void testEqualsWithNullRight() {
        Pair<String, Integer> p1 = Pair.of("apple", null);
        Pair<String, Integer> p2 = Pair.of("apple", null);
        assertTrue(p1.equals(p2));

        Pair<String, Integer> p3 = Pair.of("apple", null);
        Pair<String, Integer> p4 = Pair.of("apple", 1);
        assertFalse(p3.equals(p4));
    }

    @Test
    void testEqualsWithBothNullElements() {
        Pair<String, Integer> p1 = Pair.of(null, null);
        Pair<String, Integer> p2 = Pair.of(null, null);
        assertTrue(p1.equals(p2));

        Pair<String, Integer> p3 = Pair.of(null, null);
        Pair<String, Integer> p4 = Pair.of("a", null);
        assertFalse(p3.equals(p4));
    }

    // --- getKey(), getLeft(), getRight(), getValue() tests ---
    @Test
    void testGettersNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("key_val", 99);
        assertEquals("key_val", pair.getKey());
        assertEquals("key_val", pair.getLeft());
        assertEquals(99, pair.getRight());
        assertEquals(99, pair.getValue());
    }

    @Test
    void testGettersWithNullElements() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNull(pair.getKey());
        assertNull(pair.getLeft());
        assertNull(pair.getRight());
        assertNull(pair.getValue());
    }

    // --- hashCode() tests ---
    @Test
    void testHashCodeEqualPairsHaveSameHashCode() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("apple", 1);
        assertEquals(p1.hashCode(), p2.hashCode());
    }

    @Test
    void testHashCodeDifferentPairsHaveDifferentHashCode() {
        Pair<String, Integer> p1 = Pair.of("apple", 1);
        Pair<String, Integer> p2 = Pair.of("banana", 1);
        assertNotEquals(p1.hashCode(), p2.hashCode());

        Pair<String, Integer> p3 = Pair.of("apple", 1);
        Pair<String, Integer> p4 = Pair.of("apple", 2);
        assertNotEquals(p3.hashCode(), p4.hashCode());
    }

    @Test
    void testHashCodeWithNullElements() {
        Pair<String, Integer> p1 = Pair.of(null, 1);
        Pair<String, Integer> p2 = Pair.of(null, 1);
        assertEquals(p1.hashCode(), p2.hashCode());

        Pair<String, Integer> p3 = Pair.of("apple", null);
        Pair<String, Integer> p4 = Pair.of("apple", null);
        assertEquals(p3.hashCode(), p4.hashCode());

        Pair<String, Integer> p5 = Pair.of(null, null);
        Pair<String, Integer> p6 = Pair.of(null, null);
        assertEquals(p5.hashCode(), p6.hashCode());

        // Hash code of null is 0
        assertEquals(Objects.hashCode(null) ^ Objects.hashCode(1), p1.hashCode());
        assertEquals(Objects.hashCode("apple") ^ Objects.hashCode(null), p3.hashCode());
        assertEquals(Objects.hashCode(null) ^ Objects.hashCode(null), p5.hashCode());
    }

    // --- toString() tests ---
    @Test
    void testToStringNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        assertEquals("(left,100)", pair.toString());
    }

    @Test
    void testToStringWithNullElements() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("(null,null)", pair.toString());

        Pair<String, Integer> pairLeftNull = Pair.of(null, 200);
        assertEquals("(null,200)", pairLeftNull.toString());

        Pair<String, Integer> pairRightNull = Pair.of("right", null);
        assertEquals("(right,null)", pairRightNull.toString());
    }

    @Test
    void testToStringWithSpecialCharacters() {
        Pair<String, String> pair = Pair.of("key,value", "val(ue)");
        assertEquals("(key,value,val(ue))", pair.toString()); // Note: The default toString doesn't escape commas or parentheses
    }

    // --- toString(String format) tests ---
    @Test
    void testToStringFormatNormalBehavior() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        assertEquals("L:left R:100", pair.toString("L:%s R:%s"));
        assertEquals("Pair{left=left, right=100}", pair.toString("Pair{left=%s, right=%s}"));
    }

    @Test
    void testToStringFormatWithNullElements() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("L:null R:null", pair.toString("L:%s R:%s"));

        Pair<String, Integer> pairLeftNull = Pair.of(null, 200);
        assertEquals("L:null R:200", pairLeftNull.toString("L:%s R:%s"));

        Pair<String, Integer> pairRightNull = Pair.of("right", null);
        assertEquals("L:right R:null", pairRightNull.toString("L:%s R:%s"));
    }

    @Test
    void testToStringFormatEmptyFormatString() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        assertEquals("", pair.toString(""));
    }

    @Test
    void testToStringFormatOnlyLeftPlaceholder() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        assertEquals("Left: left", pair.toString("Left: %s"));
    }

    @Test
    void testToStringFormatOnlyRightPlaceholder() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        assertEquals("Right: 100", pair.toString("Right: %2$s"));
    }

    @Test
    void testToStringFormatTooFewPlaceholders() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        // This will use the first placeholder for the left, and the second for the right.
        // If only one is provided, it will use it for the left and then potentially throw if another is needed.
        // Or, if the format string only has one %s, it will only format the first argument.
        assertEquals("Left: left", pair.toString("Left: %s"));
    }

    @Test
    void testToStringFormatTooManyPlaceholders() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        // This is handled by String.format, which will ignore extra placeholders if not enough arguments.
        // Or, if there are more arguments than placeholders, it will ignore extra arguments.
        // For %s, it expects two arguments.
        assertEquals("L:left R:100 Extra: %s", pair.toString("L:%s R:%s Extra: %s"));
    }

    @Test
    void testToStringFormatNullFormatString() {
        Pair<String, Integer> pair = Pair.of("left", 100);
        assertThrows(NullPointerException.class, () -> pair.toString(null),
                "toString(null format) should throw NullPointerException");
    }

    // --- General Tests for Immutability (assuming Pair is immutable) ---
    @Test
    void testImmutabilityOfElements() {
        StringBuilder left = new StringBuilder("initial");
        Integer right = 123;
        Pair<StringBuilder, Integer> pair = Pair.of(left, right);

        left.append(" changed"); // Modify the original object
        right = 456; // Reassign the reference

        assertEquals("initial changed", pair.getLeft().toString(),
                "Left element should reflect changes if it's a mutable object");
        assertEquals(123, pair.getRight(),
                "Right element should remain the original value as Integer is immutable");

        // This shows that Pair itself is immutable (references don't change),
        // but the objects *referred to* by the pair's elements can be mutable.
        // The specification doesn't explicitly state deep immutability,
        // so this behavior is acceptable.
    }
}