package org.apache.commons.lang3.tuple.p3;

import org.apache.commons.lang3.function.FailableBiConsumer;
import org.apache.commons.lang3.function.FailableBiFunction;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Pair Class Unit Tests")
class PairTestP3P3 {

    // --- emptyArray() tests ---
    @Test
    @DisplayName("emptyArray() should return an empty array")
    void testEmptyArray_returnsEmptyArray() {
        Pair<?, ?>[] emptyArray = Pair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    @DisplayName("emptyArray() should return the same instance on multiple calls")
    void testEmptyArray_returnsSameInstance() {
        Pair<?, ?>[] array1 = Pair.emptyArray();
        Pair<?, ?>[] array2 = Pair.emptyArray();
        assertSame(array1, array2, "emptyArray() should return the same array instance");
    }

    // --- of(L left, R right) tests ---
    @Test
    @DisplayName("of(L, R) should create a Pair with non-null values")
    void testOf_nonNullValues() {
        Pair<String, Integer> pair = Pair.of("hello", 123);
        assertNotNull(pair, "Pair.of() should not return null for non-null values");
        assertEquals("hello", pair.getLeft(), "Left value should match input");
        assertEquals(123, pair.getRight(), "Right value should match input");
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with null left value")
    void testOf_nullLeftValue() {
        Pair<String, Integer> pair = Pair.of(null, 123);
        assertNotNull(pair, "Pair.of() should not return null for null left value");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(123, pair.getRight(), "Right value should match input");
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with null right value")
    void testOf_nullRightValue() {
        Pair<String, Integer> pair = Pair.of("hello", null);
        assertNotNull(pair, "Pair.of() should not return null for null right value");
        assertEquals("hello", pair.getLeft(), "Left value should match input");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    @DisplayName("of(L, R) should create a Pair with both null values")
    void testOf_bothNullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNotNull(pair, "Pair.of() should not return null for both null values");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    // --- of(Map.Entry<L, R> pair) tests ---
    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a non-null Map.Entry")
    void testOf_mapEntry_nonNull() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", 42);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair, "Pair.of(Map.Entry) should not return null");
        assertEquals("key", pair.getLeft(), "Left value should match entry key");
        assertEquals(42, pair.getRight(), "Right value should match entry value");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with null key")
    void testOf_mapEntry_nullKey() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 42);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertNull(pair.getLeft());
        assertEquals(42, pair.getRight());
    }

    @Test
    @DisplayName("of(Map.Entry) should create a Pair from a Map.Entry with null value")
    void testOf_mapEntry_nullValue() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", null);
        Pair<String, Integer> pair = Pair.of(entry);
        assertNotNull(pair);
        assertEquals("key", pair.getLeft());
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
    @DisplayName("of(Map.Entry) should throw NullPointerException for null Map.Entry")
    void testOf_mapEntry_nullEntry() {
        assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null),
                "Pair.of(null Map.Entry) should throw NullPointerException");
    }

    // --- ofNonNull(L left, R right) tests ---
    @Test
    @DisplayName("ofNonNull(L, R) should create a Pair with non-null values")
    void testOfNonNull_nonNullValues() {
        Pair<String, Integer> pair = Pair.ofNonNull("hello", 123);
        assertNotNull(pair, "Pair.ofNonNull() should not return null for non-null values");
        assertEquals("hello", pair.getLeft(), "Left value should match input");
        assertEquals(123, pair.getRight(), "Right value should match input");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for null left value")
    void testOfNonNull_nullLeftValue() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 123),
                "Pair.ofNonNull() should throw NullPointerException for null left value");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for null right value")
    void testOfNonNull_nullRightValue() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull("hello", null),
                "Pair.ofNonNull() should throw NullPointerException for null right value");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for both null values")
    void testOfNonNull_bothNullValues() {
        assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                "Pair.ofNonNull() should throw NullPointerException for both null values");
    }

    // --- accept(FailableBiConsumer<L, R, E> consumer) tests ---
    @Test
    @DisplayName("accept() should execute consumer with pair values")
    void testAccept_normalBehavior() throws Exception {
        Pair<String, Integer> pair = Pair.of("test", 100);
        AtomicReference<String> consumedLeft = new AtomicReference<>();
        AtomicReference<Integer> consumedRight = new AtomicReference<>();

        FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> {
            consumedLeft.set(l);
            consumedRight.set(r);
        };

        pair.accept(consumer);

        assertEquals("test", consumedLeft.get(), "Consumer should receive left value");
        assertEquals(100, consumedRight.get(), "Consumer should receive right value");
    }

    @Test
    @DisplayName("accept() should handle null values gracefully")
    void testAccept_nullValues() throws Exception {
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

    @Test
    @DisplayName("accept() should rethrow exception from consumer")
    void testAccept_consumerThrowsException() {
        Pair<String, Integer> pair = Pair.of("test", 100);
        FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
            throw new IOException("Test exception");
        };

        assertThrows(IOException.class, () -> pair.accept(consumer),
                "accept() should rethrow the exception from the consumer");
    }

    @Test
    @DisplayName("accept() should throw NullPointerException if consumer is null")
    void testAccept_nullConsumer() {
        Pair<String, Integer> pair = Pair.of("test", 100);
        assertThrows(NullPointerException.class, () -> pair.accept(null),
                "accept() should throw NullPointerException if consumer is null");
    }

    // --- apply(FailableBiFunction<L, R, V, E> function) tests ---
    @Test
    @DisplayName("apply() should execute function with pair values and return result")
    void testApply_normalBehavior() throws Exception {
        Pair<String, Integer> pair = Pair.of("test", 100);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> l + ":" + r;

        String result = pair.apply(function);

        assertEquals("test:100", result, "apply() should return the result of the function");
    }

    @Test
    @DisplayName("apply() should handle null values gracefully")
    void testApply_nullValues() throws Exception {
        Pair<String, Integer> pair = Pair.of(null, null);
        FailableBiFunction<String, Integer, String, Exception> function = (l, r) ->
                (l == null ? "null" : l) + ":" + (r == null ? "null" : r);

        String result = pair.apply(function);

        assertEquals("null:null", result, "apply() should handle null values in function");
    }

    @Test
    @DisplayName("apply() should rethrow exception from function")
    void testApply_functionThrowsException() {
        Pair<String, Integer> pair = Pair.of("test", 100);
        FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
            throw new IOException("Test exception from function");
        };

        assertThrows(IOException.class, () -> pair.apply(function),
                "apply() should rethrow the exception from the function");
    }

    @Test
    @DisplayName("apply() should throw NullPointerException if function is null")
    void testApply_nullFunction() {
        Pair<String, Integer> pair = Pair.of("test", 100);
        assertThrows(NullPointerException.class, () -> pair.apply(null),
                "apply() should throw NullPointerException if function is null");
    }

    // --- compareTo(Pair<L, R> other) tests ---
    static Stream<Arguments> compareToData() {
        return Stream.of(
                // Equal pairs
                Arguments.of(Pair.of("A", 1), Pair.of("A", 1), 0),
                Arguments.of(Pair.of(null, 1), Pair.of(null, 1), 0),
                Arguments.of(Pair.of("A", null), Pair.of("A", null), 0),
                Arguments.of(Pair.of(null, null), Pair.of(null, null), 0),

                // Left value differs
                Arguments.of(Pair.of("A", 1), Pair.of("B", 1), -1),
                Arguments.of(Pair.of("B", 1), Pair.of("A", 1), 1),
                Arguments.of(Pair.of(null, 1), Pair.of("A", 1), -1), // null < non-null
                Arguments.of(Pair.of("A", 1), Pair.of(null, 1), 1), // non-null > null

                // Left value equal, Right value differs
                Arguments.of(Pair.of("A", 1), Pair.of("A", 2), -1),
                Arguments.of(Pair.of("A", 2), Pair.of("A", 1), 1),
                Arguments.of(Pair.of("A", null), Pair.of("A", 1), -1), // null < non-null
                Arguments.of(Pair.of("A", 1), Pair.of("A", null), 1), // non-null > null

                // Mixed types (assuming they are Comparable)
                Arguments.of(Pair.of(1, "A"), Pair.of(1, "B"), -1),
                Arguments.of(Pair.of(1, "B"), Pair.of(1, "A"), 1)
        );
    }

    @ParameterizedTest
    @MethodSource("compareToData")
    @DisplayName("compareTo() should correctly compare pairs")
    <L extends Comparable<L>, R extends Comparable<R>>
    void testCompareTo_variousPairs(Pair<L, R> pair1, Pair<L, R> pair2, int expectedSign) {
        int result = pair1.compareTo(pair2);
        if (expectedSign == 0) {
            assertEquals(0, result, () -> String.format("Expected %s to be equal to %s", pair1, pair2));
        } else if (expectedSign < 0) {
            assertTrue(result < 0, () -> String.format("Expected %s to be less than %s", pair1, pair2));
        } else {
            assertTrue(result > 0, () -> String.format("Expected %s to be greater than %s", pair1, pair2));
        }
    }

    @Test
    @DisplayName("compareTo() should throw NullPointerException if other is null")
    void testCompareTo_nullOther() {
        Pair<String, Integer> pair = Pair.of("A", 1);
        assertThrows(NullPointerException.class, () -> pair.compareTo(null),
                "compareTo() should throw NullPointerException if other is null");
    }

    @Test
    @DisplayName("compareTo() should throw ClassCastException if elements are not comparable")
    void testCompareTo_nonComparableElements() {
        // Create a class that is not Comparable
        class NonComparable {
            int value;
            NonComparable(int value) { this.value = value; }
        }

        Pair<NonComparable, Integer> pair1 = Pair.of(new NonComparable(1), 1);
        Pair<NonComparable, Integer> pair2 = Pair.of(new NonComparable(2), 1);

        // The first element is not comparable, so it should throw ClassCastException
        assertThrows(ClassCastException.class, () -> pair1.compareTo(pair2),
                "compareTo() should throw ClassCastException if elements are not comparable");

        // Test with comparable left, non-comparable right
        Pair<Integer, NonComparable> pair3 = Pair.of(1, new NonComparable(1));
        Pair<Integer, NonComparable> pair4 = Pair.of(1, new NonComparable(2));
        assertThrows(ClassCastException.class, () -> pair3.compareTo(pair4),
                "compareTo() should throw ClassCastException if right element is not comparable");
    }


    // --- equals(Object obj) tests ---
    static Stream<Arguments> equalsData() {
        return Stream.of(
                // Equal pairs
                Arguments.of(Pair.of("A", 1), Pair.of("A", 1), true),
                Arguments.of(Pair.of(null, 1), Pair.of(null, 1), true),
                Arguments.of(Pair.of("A", null), Pair.of("A", null), true),
                Arguments.of(Pair.of(null, null), Pair.of(null, null), true),

                // Different left
                Arguments.of(Pair.of("A", 1), Pair.of("B", 1), false),
                Arguments.of(Pair.of(null, 1), Pair.of("A", 1), false),
                Arguments.of(Pair.of("A", 1), Pair.of(null, 1), false),

                // Different right
                Arguments.of(Pair.of("A", 1), Pair.of("A", 2), false),
                Arguments.of(Pair.of("A", null), Pair.of("A", 1), false),
                Arguments.of(Pair.of("A", 1), Pair.of("A", null), false),

                // Different both
                Arguments.of(Pair.of("A", 1), Pair.of("B", 2), false),
                Arguments.of(Pair.of(null, 1), Pair.of("A", null), false),

                // Different object types
                Arguments.of(Pair.of("A", 1), "not a pair", false),
                Arguments.of(Pair.of("A", 1), null, false)
        );
    }

    @ParameterizedTest
    @MethodSource("equalsData")
    @DisplayName("equals() should correctly compare pairs for equality")
    void testEquals_variousPairs(Pair<?, ?> pair1, Object obj, boolean expected) {
        assertEquals(expected, pair1.equals(obj),
                () -> String.format("Expected %s.equals(%s) to be %b", pair1, obj, expected));
    }

    @Test
    @DisplayName("equals() should be reflexive")
    void testEquals_reflexive() {
        Pair<String, Integer> pair = Pair.of("test", 123);
        assertTrue(pair.equals(pair), "equals() should be reflexive");
    }

    @Test
    @DisplayName("equals() should be symmetric")
    void testEquals_symmetric() {
        Pair<String, Integer> pair1 = Pair.of("test", 123);
        Pair<String, Integer> pair2 = Pair.of("test", 123);
        assertTrue(pair1.equals(pair2) == pair2.equals(pair1), "equals() should be symmetric");
    }

    @Test
    @DisplayName("equals() should be transitive")
    void testEquals_transitive() {
        Pair<String, Integer> pair1 = Pair.of("test", 123);
        Pair<String, Integer> pair2 = Pair.of("test", 123);
        Pair<String, Integer> pair3 = Pair.of("test", 123);
        if (pair1.equals(pair2) && pair2.equals(pair3)) {
            assertTrue(pair1.equals(pair3), "equals() should be transitive");
        }
    }

    @Test
    @DisplayName("equals() should return false for different types")
    void testEquals_differentTypes() {
        Pair<String, Integer> pair = Pair.of("test", 123);
        assertFalse(pair.equals("a string"), "equals() should return false for different types");
        assertFalse(pair.equals(new HashMap<>()), "equals() should return false for different types");
    }

    // --- getKey(), getLeft(), getRight(), getValue() tests ---
    @Test
    @DisplayName("getKey() should return the left value")
    void testGetKey() {
        Pair<String, Integer> pair = Pair.of("key", 100);
        assertEquals("key", pair.getKey(), "getKey() should return the left value");
    }

    @Test
    @DisplayName("getLeft() should return the left value")
    void testGetLeft() {
        Pair<String, Integer> pair = Pair.of("left", 200);
        assertEquals("left", pair.getLeft(), "getLeft() should return the left value");
    }

    @Test
    @DisplayName("getRight() should return the right value")
    void testGetRight() {
        Pair<String, Integer> pair = Pair.of("left", 300);
        assertEquals(300, pair.getRight(), "getRight() should return the right value");
    }

    @Test
    @DisplayName("getValue() should return the right value")
    void testGetValue() {
        Pair<String, Integer> pair = Pair.of("key", 400);
        assertEquals(400, pair.getValue(), "getValue() should return the right value");
    }

    @Test
    @DisplayName("getters should return null if values are null")
    void testGetters_nullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertNull(pair.getKey(), "getKey() should return null for null left value");
        assertNull(pair.getLeft(), "getLeft() should return null for null left value");
        assertNull(pair.getRight(), "getRight() should return null for null right value");
        assertNull(pair.getValue(), "getValue() should return null for null right value");
    }

    // --- hashCode() tests ---
    @Test
    @DisplayName("hashCode() should be consistent with equals() for equal pairs")
    void testHashCode_consistentWithEquals() {
        Pair<String, Integer> pair1 = Pair.of("test", 123);
        Pair<String, Integer> pair2 = Pair.of("test", 123);
        assertTrue(pair1.equals(pair2), "Pairs should be equal for hashCode test");
        assertEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be equal for equal pairs");
    }

    @Test
    @DisplayName("hashCode() should be consistent for pairs with null values")
    void testHashCode_withNullValues() {
        Pair<String, Integer> pair1 = Pair.of(null, 123);
        Pair<String, Integer> pair2 = Pair.of(null, 123);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        Pair<String, Integer> pair3 = Pair.of("test", null);
        Pair<String, Integer> pair4 = Pair.of("test", null);
        assertEquals(pair3.hashCode(), pair4.hashCode());

        Pair<String, Integer> pair5 = Pair.of(null, null);
        Pair<String, Integer> pair6 = Pair.of(null, null);
        assertEquals(pair5.hashCode(), pair6.hashCode());
    }

    @Test
    @DisplayName("hashCode() should return 0 for a pair of (null, null)")
    void testHashCode_bothNull() {
        Pair<Object, Object> pair = Pair.of(null, null);
        assertEquals(0, pair.hashCode(), "hashCode() for (null, null) should be 0");
    }

    @Test
    @DisplayName("hashCode() should return hash of right for (null, R)")
    void testHashCode_nullLeft() {
        Pair<Object, Integer> pair = Pair.of(null, 123);
        assertEquals(Objects.hashCode(123), pair.hashCode(), "hashCode() for (null, R) should be hash of R");
    }

    @Test
    @DisplayName("hashCode() should return hash of left for (L, null)")
    void testHashCode_nullRight() {
        Pair<String, Object> pair = Pair.of("test", null);
        assertEquals(Objects.hashCode("test"), pair.hashCode(), "hashCode() for (L, null) should be hash of L");
    }

    // --- toString() tests ---
    @Test
    @DisplayName("toString() should return default string representation for non-null values")
    void testToString_nonNullValues() {
        Pair<String, Integer> pair = Pair.of("hello", 123);
        assertEquals("(hello,123)", pair.toString(), "toString() should format correctly");
    }

    @Test
    @DisplayName("toString() should handle null values gracefully")
    void testToString_nullValues() {
        Pair<String, Integer> pair1 = Pair.of(null, 123);
        assertEquals("(null,123)", pair1.toString(), "toString() should handle null left value");

        Pair<String, Integer> pair2 = Pair.of("hello", null);
        assertEquals("(hello,null)", pair2.toString(), "toString() should handle null right value");

        Pair<String, Integer> pair3 = Pair.of(null, null);
        assertEquals("(null,null)", pair3.toString(), "toString() should handle both null values");
    }

    // --- toString(String format) tests ---
    @ParameterizedTest
    @ValueSource(strings = {
            "%s", "%s%s", "%s %s", "%s:%s", "[%s,%s]", "<%1$s|%2$s>",
            "Left: %1$s, Right: %2$s", "Right: %2$s, Left: %1$s"
    })
    @DisplayName("toString(format) should format correctly with various valid formats")
    void testToString_withValidFormat(String format) {
        Pair<String, Integer> pair = Pair.of("test", 42);
        String expected = String.format(format, "test", 42);
        assertEquals(expected, pair.toString(format), "toString(format) should apply the format string");
    }

    @Test
    @DisplayName("toString(format) should handle null values with format string")
    void testToString_withFormat_nullValues() {
        Pair<String, Integer> pair = Pair.of(null, null);
        assertEquals("null:null", pair.toString("%s:%s"), "toString(format) should handle nulls with format");
        assertEquals("L:null, R:null", pair.toString("L:%1$s, R:%2$s"), "toString(format) should handle nulls with indexed format");
    }

    @Test
    @DisplayName("toString(format) should throw NullPointerException if format is null")
    void testToString_nullFormat() {
        Pair<String, Integer> pair = Pair.of("test", 123);
        assertThrows(NullPointerException.class, () -> pair.toString(null),
                "toString(null format) should throw NullPointerException");
    }

    @Test
    @DisplayName("toString(format) should throw IllegalFormatException for invalid format string")
    void testToString_invalidFormat() {
        Pair<String, Integer> pair = Pair.of("test", 123);
        assertThrows(java.util.IllegalFormatException.class, () -> pair.toString("%d"), // Expects int, gets String
                "toString(format) should throw IllegalFormatException for incompatible format specifiers");
        assertThrows(java.util.IllegalFormatException.class, () -> pair.toString("%s %s %s"), // Too many specifiers
                "toString(format) should throw IllegalFormatException for too many format specifiers");
    }
}