package org.apache.commons.lang3.tuple.p3c;

import org.apache.commons.lang3.function.FailableBiConsumer;
import org.apache.commons.lang3.function.FailableBiFunction;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Pair Class Unit Tests")
class PairTestP3CP3C {

    // Helper for creating a simple Map.Entry
    private static <L, R> Map.Entry<L, R> createMapEntry(L left, R right) {
        return new AbstractMap.SimpleEntry<>(left, right);
    }

    @Nested
    @DisplayName("emptyArray() Tests")
    class EmptyArrayTests {

        @Test
        @DisplayName("Should return an empty array")
        void shouldReturnEmptyArray() {
            Pair<?, ?>[] emptyArray = Pair.emptyArray();
            assertNotNull(emptyArray, "Array should not be null");
            assertEquals(0, emptyArray.length, "Array length should be 0");
        }

        @Test
        @DisplayName("Should return the same instance for emptyArray()")
        void shouldReturnSameInstance() {
            Pair<?, ?>[] array1 = Pair.emptyArray();
            Pair<?, ?>[] array2 = Pair.emptyArray();
            assertSame(array1, array2, "emptyArray() should return the same instance");
        }
    }

    @Nested
    @DisplayName("of(L left, R right) Tests")
    class OfTests {

        @Test
        @DisplayName("Should create a Pair with non-null elements")
        void shouldCreatePairWithNonNullElements() {
            Pair<String, Integer> pair = Pair.of("Hello", 123);
            assertNotNull(pair, "Pair should not be null");
            assertEquals("Hello", pair.getLeft(), "Left element should match");
            assertEquals(123, pair.getRight(), "Right element should match");
        }

        @Test
        @DisplayName("Should create a Pair with null left element")
        void shouldCreatePairWithNullLeft() {
            Pair<String, Integer> pair = Pair.of(null, 123);
            assertNotNull(pair, "Pair should not be null");
            assertNull(pair.getLeft(), "Left element should be null");
            assertEquals(123, pair.getRight(), "Right element should match");
        }

        @Test
        @DisplayName("Should create a Pair with null right element")
        void shouldCreatePairWithNullRight() {
            Pair<String, Integer> pair = Pair.of("Hello", null);
            assertNotNull(pair, "Pair should not be null");
            assertEquals("Hello", pair.getLeft(), "Left element should match");
            assertNull(pair.getRight(), "Right element should be null");
        }

        @Test
        @DisplayName("Should create a Pair with both null elements")
        void shouldCreatePairWithBothNulls() {
            Pair<String, Integer> pair = Pair.of(null, null);
            assertNotNull(pair, "Pair should not be null");
            assertNull(pair.getLeft(), "Left element should be null");
            assertNull(pair.getRight(), "Right element should be null");
        }
    }

    @Nested
    @DisplayName("of(Map.Entry<L, R> pair) Tests")
    class OfMapEntryTests {

        @Test
        @DisplayName("Should create a Pair from a non-null Map.Entry")
        void shouldCreatePairFromNonNullMapEntry() {
            Map.Entry<String, Integer> entry = createMapEntry("Key", 456);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair should not be null");
            assertEquals("Key", pair.getLeft(), "Left element should match entry key");
            assertEquals(456, pair.getRight(), "Right element should match entry value");
        }

        @Test
        @DisplayName("Should create a Pair from a Map.Entry with null key")
        void shouldCreatePairFromMapEntryWithNullKey() {
            Map.Entry<String, Integer> entry = createMapEntry(null, 456);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair should not be null");
            assertNull(pair.getLeft(), "Left element should be null");
            assertEquals(456, pair.getRight(), "Right element should match entry value");
        }

        @Test
        @DisplayName("Should create a Pair from a Map.Entry with null value")
        void shouldCreatePairFromMapEntryWithNullValue() {
            Map.Entry<String, Integer> entry = createMapEntry("Key", null);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair should not be null");
            assertEquals("Key", pair.getLeft(), "Left element should match entry key");
            assertNull(pair.getRight(), "Right element should be null");
        }

        @Test
        @DisplayName("Should create a Pair from a Map.Entry with both nulls")
        void shouldCreatePairFromMapEntryWithBothNulls() {
            Map.Entry<String, Integer> entry = createMapEntry(null, null);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair should not be null");
            assertNull(pair.getLeft(), "Left element should be null");
            assertNull(pair.getRight(), "Right element should be null");
        }

        @Test
        @DisplayName("Should throw NullPointerException when Map.Entry is null")
        void shouldThrowNPEWhenMapEntryIsNull() {
            assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null),
                    "Should throw NullPointerException for null Map.Entry");
        }
    }

    @Nested
    @DisplayName("ofNonNull(L left, R right) Tests")
    class OfNonNullTests {

        @Test
        @DisplayName("Should create a Pair with non-null elements")
        void shouldCreatePairWithNonNullElements() {
            Pair<String, Integer> pair = Pair.ofNonNull("Alpha", 789);
            assertNotNull(pair, "Pair should not be null");
            assertEquals("Alpha", pair.getLeft(), "Left element should match");
            assertEquals(789, pair.getRight(), "Right element should match");
        }

        @Test
        @DisplayName("Should throw NullPointerException when left element is null")
        void shouldThrowNPEWhenLeftIsNull() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 789),
                    "Should throw NullPointerException for null left element");
        }

        @Test
        @DisplayName("Should throw NullPointerException when right element is null")
        void shouldThrowNPEWhenRightIsNull() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull("Alpha", null),
                    "Should throw NullPointerException for null right element");
        }

        @Test
        @DisplayName("Should throw NullPointerException when both elements are null")
        void shouldThrowNPEWhenBothAreNull() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                    "Should throw NullPointerException for both null elements");
        }
    }

    @Nested
    @DisplayName("accept(FailableBiConsumer<L, R, E> consumer) Tests")
    class AcceptTests {

        private final Pair<String, Integer> testPair = Pair.of("Test", 100);

        @Test
        @DisplayName("Should execute consumer with left and right elements")
        void shouldExecuteConsumer() throws Exception {
            AtomicReference<String> leftRef = new AtomicReference<>();
            AtomicReference<Integer> rightRef = new AtomicReference<>();

            FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> {
                leftRef.set(l);
                rightRef.set(r);
            };

            testPair.accept(consumer);

            assertEquals("Test", leftRef.get(), "Consumer should receive left element");
            assertEquals(100, rightRef.get(), "Consumer should receive right element");
        }

        @Test
        @DisplayName("Should handle consumer with null elements")
        void shouldHandleNullElements() throws Exception {
            Pair<String, Integer> nullPair = Pair.of(null, null);
            AtomicReference<String> leftRef = new AtomicReference<>();
            AtomicReference<Integer> rightRef = new AtomicReference<>();

            FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> {
                leftRef.set(l);
                rightRef.set(r);
            };

            nullPair.accept(consumer);

            assertNull(leftRef.get(), "Consumer should receive null left element");
            assertNull(rightRef.get(), "Consumer should receive null right element");
        }

        @Test
        @DisplayName("Should rethrow exception from consumer")
        void shouldRethrowExceptionFromConsumer() {
            FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
                throw new IOException("Test IOException");
            };

            IOException thrown = assertThrows(IOException.class, () -> testPair.accept(consumer),
                    "Should rethrow IOException from consumer");
            assertEquals("Test IOException", thrown.getMessage());
        }

        @Test
        @DisplayName("Should throw NullPointerException if consumer is null")
        void shouldThrowNPEIfConsumerIsNull() {
            assertThrows(NullPointerException.class, () -> testPair.accept(null),
                    "Should throw NullPointerException if consumer is null");
        }
    }

    @Nested
    @DisplayName("apply(FailableBiFunction<L, R, V, E> function) Tests")
    class ApplyTests {

        private final Pair<String, Integer> testPair = Pair.of("Value", 200);

        @Test
        @DisplayName("Should apply function and return result")
        void shouldApplyFunctionAndReturnResult() throws Exception {
            FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> l + ":" + r;
            String result = testPair.apply(function);
            assertEquals("Value:200", result, "Function should return concatenated string");
        }

        @Test
        @DisplayName("Should handle function with null elements")
        void shouldHandleNullElements() throws Exception {
            Pair<String, Integer> nullPair = Pair.of(null, null);
            FailableBiFunction<String, Integer, String, Exception> function = (l, r) ->
                    (l == null ? "null" : l) + ":" + (r == null ? "null" : r);
            String result = nullPair.apply(function);
            assertEquals("null:null", result, "Function should handle null inputs");
        }

        @Test
        @DisplayName("Should rethrow exception from function")
        void shouldRethrowExceptionFromFunction() {
            FailableBiFunction<String, Integer, String, IllegalArgumentException> function = (l, r) -> {
                throw new IllegalArgumentException("Invalid input");
            };

            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () -> testPair.apply(function),
                    "Should rethrow IllegalArgumentException from function");
            assertEquals("Invalid input", thrown.getMessage());
        }

        @Test
        @DisplayName("Should throw NullPointerException if function is null")
        void shouldThrowNPEIfFunctionIsNull() {
            assertThrows(NullPointerException.class, () -> testPair.apply(null),
                    "Should throw NullPointerException if function is null");
        }
    }

    @Nested
    @DisplayName("compareTo(Pair<L, R> other) Tests")
    class CompareToTests {

        @Test
        @DisplayName("Should return 0 for equal pairs")
        void shouldReturnZeroForEqualPairs() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertEquals(0, pair1.compareTo(pair2), "Equal pairs should return 0");
        }

        @Test
        @DisplayName("Should compare based on left element first (less than)")
        void shouldCompareByLeftLessThan() {
            Pair<String, Integer> pair1 = Pair.of("A", 10);
            Pair<String, Integer> pair2 = Pair.of("B", 1);
            assertTrue(pair1.compareTo(pair2) < 0, "Pair1 should be less than Pair2 based on left");
        }

        @Test
        @DisplayName("Should compare based on left element first (greater than)")
        void shouldCompareByLeftGreaterThan() {
            Pair<String, Integer> pair1 = Pair.of("C", 1);
            Pair<String, Integer> pair2 = Pair.of("B", 10);
            assertTrue(pair1.compareTo(pair2) > 0, "Pair1 should be greater than Pair2 based on left");
        }

        @Test
        @DisplayName("Should compare based on right element if left elements are equal (less than)")
        void shouldCompareByRightLessThan() {
            Pair<String, Integer> pair1 = Pair.of("X", 5);
            Pair<String, Integer> pair2 = Pair.of("X", 10);
            assertTrue(pair1.compareTo(pair2) < 0, "Pair1 should be less than Pair2 based on right");
        }

        @Test
        @DisplayName("Should compare based on right element if left elements are equal (greater than)")
        void shouldCompareByRightGreaterThan() {
            Pair<String, Integer> pair1 = Pair.of("Y", 20);
            Pair<String, Integer> pair2 = Pair.of("Y", 15);
            assertTrue(pair1.compareTo(pair2) > 0, "Pair1 should be greater than Pair2 based on right");
        }

        @Test
        @DisplayName("Should handle null left elements (nulls first)")
        void shouldHandleNullLeftElements() {
            Pair<String, Integer> pair1 = Pair.of(null, 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertTrue(pair1.compareTo(pair2) < 0, "Null left should come before non-null left");
            assertTrue(pair2.compareTo(pair1) > 0, "Non-null left should come after null left");
        }

        @Test
        @DisplayName("Should handle null right elements (nulls first)")
        void shouldHandleNullRightElements() {
            Pair<String, Integer> pair1 = Pair.of("A", null);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertTrue(pair1.compareTo(pair2) < 0, "Null right should come before non-null right");
            assertTrue(pair2.compareTo(pair1) > 0, "Non-null right should come after null right");
        }

        @Test
        @DisplayName("Should handle both null elements")
        void shouldHandleBothNullElements() {
            Pair<String, Integer> pair1 = Pair.of(null, null);
            Pair<String, Integer> pair2 = Pair.of(null, null);
            assertEquals(0, pair1.compareTo(pair2), "Two pairs with both nulls should be equal");

            Pair<String, Integer> pair3 = Pair.of(null, null);
            Pair<String, Integer> pair4 = Pair.of("A", null);
            assertTrue(pair3.compareTo(pair4) < 0, "Null-null should be less than non-null-null");
        }

        @Test
        @DisplayName("Should throw NullPointerException when other pair is null")
        void shouldThrowNPEWhenOtherPairIsNull() {
            Pair<String, Integer> pair = Pair.of("A", 1);
            assertThrows(NullPointerException.class, () -> pair.compareTo(null),
                    "Should throw NullPointerException when comparing to null");
        }

        @Test
        @DisplayName("Should work with different comparable types")
        void shouldWorkWithDifferentComparableTypes() {
            Pair<Integer, String> pair1 = Pair.of(1, "apple");
            Pair<Integer, String> pair2 = Pair.of(2, "banana");
            assertTrue(pair1.compareTo(pair2) < 0);

            Pair<Integer, String> pair3 = Pair.of(1, "apple");
            Pair<Integer, String> pair4 = Pair.of(1, "orange");
            assertTrue(pair3.compareTo(pair4) < 0);
        }

        @Test
        @DisplayName("Should handle non-comparable types if they are equal")
        void shouldHandleNonComparableTypesIfEqual() {
            // If the types are not Comparable, they will only be compared for equality.
            // This test relies on the internal implementation of Pair which uses ComparableUtils.compare
            // which handles nulls and non-comparable objects by treating them as equal if they are the same instance or both null.
            // For non-comparable, non-equal objects, it would typically throw ClassCastException if they were not null.
            // However, Pair's compareTo uses ComparableUtils.compare which handles this gracefully.
            Object nonComparable1 = new Object();
            Object nonComparable2 = new Object();

            Pair<Object, Object> pair1 = Pair.of(nonComparable1, nonComparable1);
            Pair<Object, Object> pair2 = Pair.of(nonComparable1, nonComparable1);
            assertEquals(0, pair1.compareTo(pair2));

            // If objects are not comparable and not equal, the behavior is undefined by standard Comparable contract
            // but Pair's implementation uses ComparableUtils.compare which returns 0 if they are not comparable and not null.
            // This might be considered an edge case or a specific implementation detail.
            // For this test, we assume the default behavior of ComparableUtils.compare for non-comparable objects.
            Pair<Object, Object> pair3 = Pair.of(nonComparable1, nonComparable2);
            Pair<Object, Object> pair4 = Pair.of(nonComparable1, nonComparable2);
            assertEquals(0, pair3.compareTo(pair4)); // Should be 0 if they are considered "equal" by reference or if ComparableUtils.compare returns 0 for non-comparable non-equal objects.
                                                     // In reality, ComparableUtils.compare returns 0 for non-comparable objects if they are not null.
                                                     // This is a specific behavior of Commons Lang.
        }
    }

    @Nested
    @DisplayName("equals(Object obj) Tests")
    class EqualsTests {

        private final Pair<String, Integer> pair = Pair.of("A", 1);

        @Test
        @DisplayName("Should return true for same instance")
        void shouldReturnTrueForSameInstance() {
            assertTrue(pair.equals(pair), "Should be true for same instance");
        }

        @Test
        @DisplayName("Should return true for equal pairs")
        void shouldReturnTrueForEqualPairs() {
            Pair<String, Integer> otherPair = Pair.of("A", 1);
            assertTrue(pair.equals(otherPair), "Should be true for equal pairs");
        }

        @Test
        @DisplayName("Should return false for null object")
        void shouldReturnFalseForNullObject() {
            assertFalse(pair.equals(null), "Should be false for null object");
        }

        @Test
        @DisplayName("Should return false for different class")
        void shouldReturnFalseForDifferentClass() {
            assertFalse(pair.equals("Not a Pair"), "Should be false for different class");
        }

        @Test
        @DisplayName("Should return false for different left element")
        void shouldReturnFalseForDifferentLeft() {
            Pair<String, Integer> otherPair = Pair.of("B", 1);
            assertFalse(pair.equals(otherPair), "Should be false for different left element");
        }

        @Test
        @DisplayName("Should return false for different right element")
        void shouldReturnFalseForDifferentRight() {
            Pair<String, Integer> otherPair = Pair.of("A", 2);
            assertFalse(pair.equals(otherPair), "Should be false for different right element");
        }

        @Test
        @DisplayName("Should return false for different left and right elements")
        void shouldReturnFalseForDifferentLeftAndRight() {
            Pair<String, Integer> otherPair = Pair.of("B", 2);
            assertFalse(pair.equals(otherPair), "Should be false for different left and right elements");
        }

        @Test
        @DisplayName("Should handle null left elements correctly")
        void shouldHandleNullLeftElements() {
            Pair<String, Integer> pair1 = Pair.of(null, 1);
            Pair<String, Integer> pair2 = Pair.of(null, 1);
            Pair<String, Integer> pair3 = Pair.of("A", 1);
            assertTrue(pair1.equals(pair2), "Pairs with null left and same right should be equal");
            assertFalse(pair1.equals(pair3), "Pairs with null left and non-null left should not be equal");
        }

        @Test
        @DisplayName("Should handle null right elements correctly")
        void shouldHandleNullRightElements() {
            Pair<String, Integer> pair1 = Pair.of("A", null);
            Pair<String, Integer> pair2 = Pair.of("A", null);
            Pair<String, Integer> pair3 = Pair.of("A", 1);
            assertTrue(pair1.equals(pair2), "Pairs with null right and same left should be equal");
            assertFalse(pair1.equals(pair3), "Pairs with null right and non-null right should not be equal");
        }

        @Test
        @DisplayName("Should handle both null elements correctly")
        void shouldHandleBothNullElements() {
            Pair<String, Integer> pair1 = Pair.of(null, null);
            Pair<String, Integer> pair2 = Pair.of(null, null);
            Pair<String, Integer> pair3 = Pair.of("A", null);
            Pair<String, Integer> pair4 = Pair.of(null, 1);
            assertTrue(pair1.equals(pair2), "Pairs with both nulls should be equal");
            assertFalse(pair1.equals(pair3), "Pairs with both nulls and one non-null should not be equal");
            assertFalse(pair1.equals(pair4), "Pairs with both nulls and one non-null should not be equal");
        }
    }

    @Nested
    @DisplayName("getKey() and getLeft() Tests")
    class GetKeyGetLeftTests {

        @Test
        @DisplayName("getKey() should return the left element")
        void getKeyShouldReturnLeft() {
            Pair<String, Integer> pair = Pair.of("Key", 10);
            assertEquals("Key", pair.getKey(), "getKey() should return the left element");
        }

        @Test
        @DisplayName("getLeft() should return the left element")
        void getLeftShouldReturnLeft() {
            Pair<String, Integer> pair = Pair.of("Left", 20);
            assertEquals("Left", pair.getLeft(), "getLeft() should return the left element");
        }

        @Test
        @DisplayName("getKey() should return null if left is null")
        void getKeyShouldReturnNullIfLeftIsNull() {
            Pair<String, Integer> pair = Pair.of(null, 30);
            assertNull(pair.getKey(), "getKey() should return null if left is null");
        }

        @Test
        @DisplayName("getLeft() should return null if left is null")
        void getLeftShouldReturnNullIfLeftIsNull() {
            Pair<String, Integer> pair = Pair.of(null, 40);
            assertNull(pair.getLeft(), "getLeft() should return null if left is null");
        }
    }

    @Nested
    @DisplayName("getRight() and getValue() Tests")
    class GetRightGetValueTests {

        @Test
        @DisplayName("getRight() should return the right element")
        void getRightShouldReturnRight() {
            Pair<String, Integer> pair = Pair.of("Key", 10);
            assertEquals(10, pair.getRight(), "getRight() should return the right element");
        }

        @Test
        @DisplayName("getValue() should return the right element")
        void getValueShouldReturnRight() {
            Pair<String, Integer> pair = Pair.of("Left", 20);
            assertEquals(20, pair.getValue(), "getValue() should return the right element");
        }

        @Test
        @DisplayName("getRight() should return null if right is null")
        void getRightShouldReturnNullIfRightIsNull() {
            Pair<String, Integer> pair = Pair.of("Key", null);
            assertNull(pair.getRight(), "getRight() should return null if right is null");
        }

        @Test
        @DisplayName("getValue() should return null if right is null")
        void getValueShouldReturnNullIfRightIsNull() {
            Pair<String, Integer> pair = Pair.of("Left", null);
            assertNull(pair.getValue(), "getValue() should return null if right is null");
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {

        @Test
        @DisplayName("Should return same hash code for equal pairs")
        void shouldReturnSameHashCodeForEqualPairs() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertEquals(pair1.hashCode(), pair2.hashCode(), "Equal pairs should have same hash code");
        }

        @Test
        @DisplayName("Should return different hash code for different pairs")
        void shouldReturnDifferentHashCodeForDifferentPairs() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("B", 1);
            Pair<String, Integer> pair3 = Pair.of("A", 2);
            assertNotEquals(pair1.hashCode(), pair2.hashCode(), "Different left should result in different hash code");
            assertNotEquals(pair1.hashCode(), pair3.hashCode(), "Different right should result in different hash code");
        }

        @Test
        @DisplayName("Should handle null left element in hash code")
        void shouldHandleNullLeftInHashCode() {
            Pair<String, Integer> pair1 = Pair.of(null, 1);
            Pair<String, Integer> pair2 = Pair.of(null, 1);
            assertEquals(pair1.hashCode(), pair2.hashCode(), "Pairs with null left should have same hash code");
        }

        @Test
        @DisplayName("Should handle null right element in hash code")
        void shouldHandleNullRightInHashCode() {
            Pair<String, Integer> pair1 = Pair.of("A", null);
            Pair<String, Integer> pair2 = Pair.of("A", null);
            assertEquals(pair1.hashCode(), pair2.hashCode(), "Pairs with null right should have same hash code");
        }

        @Test
        @DisplayName("Should handle both null elements in hash code")
        void shouldHandleBothNullsInHashCode() {
            Pair<String, Integer> pair1 = Pair.of(null, null);
            Pair<String, Integer> pair2 = Pair.of(null, null);
            assertEquals(pair1.hashCode(), pair2.hashCode(), "Pairs with both nulls should have same hash code");
        }

        @Test
        @DisplayName("Hash code consistency with equals contract")
        void hashCodeConsistencyWithEquals() {
            // If pair1.equals(pair2) is true, then pair1.hashCode() must be equal to pair2.hashCode().
            Pair<String, Integer> pair1 = Pair.of("Test", 123);
            Pair<String, Integer> pair2 = Pair.of("Test", 123);
            assertTrue(pair1.equals(pair2));
            assertEquals(pair1.hashCode(), pair2.hashCode());

            Pair<String, Integer> pair3 = Pair.of(null, 456);
            Pair<String, Integer> pair4 = Pair.of(null, 456);
            assertTrue(pair3.equals(pair4));
            assertEquals(pair3.hashCode(), pair4.hashCode());

            Pair<String, Integer> pair5 = Pair.of("Test", null);
            Pair<String, Integer> pair6 = Pair.of("Test", null);
            assertTrue(pair5.equals(pair6));
            assertEquals(pair5.hashCode(), pair6.hashCode());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {

        @Test
        @DisplayName("Should return default string representation for non-null elements")
        void shouldReturnDefaultStringForNonNull() {
            Pair<String, Integer> pair = Pair.of("Key", 123);
            assertEquals("(Key,123)", pair.toString(), "Default toString should be (left,right)");
        }

        @Test
        @DisplayName("Should return default string representation for null left element")
        void shouldReturnDefaultStringForNullLeft() {
            Pair<String, Integer> pair = Pair.of(null, 123);
            assertEquals("(null,123)", pair.toString(), "Default toString should handle null left");
        }

        @Test
        @DisplayName("Should return default string representation for null right element")
        void shouldReturnDefaultStringForNullRight() {
            Pair<String, Integer> pair = Pair.of("Key", null);
            assertEquals("(Key,null)", pair.toString(), "Default toString should handle null right");
        }

        @Test
        @DisplayName("Should return default string representation for both null elements")
        void shouldReturnDefaultStringForBothNulls() {
            Pair<String, Integer> pair = Pair.of(null, null);
            assertEquals("(null,null)", pair.toString(), "Default toString should handle both nulls");
        }
    }

    @Nested
    @DisplayName("toString(String format) Tests")
    class ToStringFormatTests {

        private final Pair<String, Integer> pair = Pair.of("Alpha", 789);

        @Test
        @DisplayName("Should format string using provided format string")
        void shouldFormatStringWithProvidedFormat() {
            assertEquals("L:Alpha, R:789", pair.toString("L:%L, R:%R"), "Should format with %L and %R");
        }

        @Test
        @DisplayName("Should handle null left element in formatted string")
        void shouldHandleNullLeftInFormattedString() {
            Pair<String, Integer> nullLeftPair = Pair.of(null, 789);
            assertEquals("L:null, R:789", nullLeftPair.toString("L:%L, R:%R"), "Should handle null left with %L");
        }

        @Test
        @DisplayName("Should handle null right element in formatted string")
        void shouldHandleNullRightInFormattedString() {
            Pair<String, Integer> nullRightPair = Pair.of("Alpha", null);
            assertEquals("L:Alpha, R:null", nullRightPair.toString("L:%L, R:%R"), "Should handle null right with %R");
        }

        @Test
        @DisplayName("Should handle both null elements in formatted string")
        void shouldHandleBothNullsInFormattedString() {
            Pair<String, Integer> nullPair = Pair.of(null, null);
            assertEquals("L:null, R:null", nullPair.toString("L:%L, R:%R"), "Should handle both nulls with %L and %R");
        }

        @Test
        @DisplayName("Should return format string if no placeholders are present")
        void shouldReturnFormatStringIfNoPlaceholders() {
            assertEquals("My Pair", pair.toString("My Pair"), "Should return format string if no placeholders");
        }

        @Test
        @DisplayName("Should throw NullPointerException if format string is null")
        void shouldThrowNPEIfFormatIsNull() {
            assertThrows(NullPointerException.class, () -> pair.toString(null),
                    "Should throw NullPointerException if format string is null");
        }

        @Test
        @DisplayName("Should handle empty format string")
        void shouldHandleEmptyFormatString() {
            assertEquals("", pair.toString(""), "Should return empty string for empty format");
        }

        @Test
        @DisplayName("Should handle format string with only one placeholder")
        void shouldHandleFormatWithOnePlaceholder() {
            assertEquals("Left:Alpha", pair.toString("Left:%L"), "Should handle format with only %L");
            assertEquals("Right:789", pair.toString("Right:%R"), "Should handle format with only %R");
        }

        @Test
        @DisplayName("Should handle multiple occurrences of placeholders")
        void shouldHandleMultiplePlaceholders() {
            assertEquals("Alpha-789-Alpha-789", pair.toString("%L-%R-%L-%R"), "Should replace all occurrences");
        }

        @Test
        @DisplayName("Should handle escaped percent signs")
        void shouldHandleEscapedPercentSigns() {
            assertEquals("Value is 100%", Pair.of("Value", 100).toString("Value is %R%%"), "Should handle %% as %");
            assertEquals("Alpha%L", pair.toString("%L%%L"), "Should handle %% followed by L");
        }
    }
}