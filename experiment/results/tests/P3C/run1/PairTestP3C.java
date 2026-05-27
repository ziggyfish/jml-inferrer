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
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Pair Class Unit Tests")
class PairTestP3CP3C {

    // Helper class for testing FailableBiConsumer and FailableBiFunction
    static class TestConsumer<L, R, E extends Throwable> implements FailableBiConsumer<L, R, E> {
        private L lastLeft;
        private R lastRight;
        private boolean called = false;
        private final boolean shouldThrow;
        private final E exceptionToThrow;

        public TestConsumer(boolean shouldThrow, E exceptionToThrow) {
            this.shouldThrow = shouldThrow;
            this.exceptionToThrow = exceptionToThrow;
        }

        @Override
        public void accept(L l, R r) throws E {
            called = true;
            lastLeft = l;
            lastRight = r;
            if (shouldThrow) {
                throw exceptionToThrow;
            }
        }

        public L getLastLeft() {
            return lastLeft;
        }

        public R getLastRight() {
            return lastRight;
        }

        public boolean isCalled() {
            return called;
        }
    }

    static class TestFunction<L, R, V, E extends Throwable> implements FailableBiFunction<L, R, V, E> {
        private L lastLeft;
        private R lastRight;
        private boolean called = false;
        private final boolean shouldThrow;
        private final E exceptionToThrow;
        private final V returnValue;

        public TestFunction(boolean shouldThrow, E exceptionToThrow, V returnValue) {
            this.shouldThrow = shouldThrow;
            this.exceptionToThrow = exceptionToThrow;
            this.returnValue = returnValue;
        }

        @Override
        public V apply(L l, R r) throws E {
            called = true;
            lastLeft = l;
            lastRight = r;
            if (shouldThrow) {
                throw exceptionToThrow;
            }
            return returnValue;
        }

        public L getLastLeft() {
            return lastLeft;
        }

        public R getLastRight() {
            return lastRight;
        }

        public boolean isCalled() {
            return called;
        }
    }


    @Nested
    @DisplayName("Static Factory Methods")
    class StaticFactoryMethods {

        @Test
        @DisplayName("emptyArray(): Should return an empty array of Pair")
        void emptyArray_shouldReturnEmptyArray() {
            Pair<?, ?>[] emptyArray = Pair.emptyArray();
            assertNotNull(emptyArray);
            assertEquals(0, emptyArray.length);
            // Ensure it's the same instance (optimization)
            assertSame(Pair.emptyArray(), emptyArray);
        }

        @Test
        @DisplayName("of(L left, R right): Should create a Pair with non-null values")
        void of_nonNullValues_shouldCreatePair() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertNotNull(pair);
            assertEquals("hello", pair.getLeft());
            assertEquals(123, pair.getRight());
        }

        @Test
        @DisplayName("of(L left, R right): Should create a Pair with null left value")
        void of_nullLeftValue_shouldCreatePair() {
            Pair<String, Integer> pair = Pair.of(null, 123);
            assertNotNull(pair);
            assertNull(pair.getLeft());
            assertEquals(123, pair.getRight());
        }

        @Test
        @DisplayName("of(L left, R right): Should create a Pair with null right value")
        void of_nullRightValue_shouldCreatePair() {
            Pair<String, Integer> pair = Pair.of("hello", null);
            assertNotNull(pair);
            assertEquals("hello", pair.getLeft());
            assertNull(pair.getRight());
        }

        @Test
        @DisplayName("of(L left, R right): Should create a Pair with both null values")
        void of_bothNullValues_shouldCreatePair() {
            Pair<String, Integer> pair = Pair.of(null, null);
            assertNotNull(pair);
            assertNull(pair.getLeft());
            assertNull(pair.getRight());
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair): Should create a Pair from a non-null Map.Entry")
        void of_mapEntry_nonNullEntry_shouldCreatePair() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", 42);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair);
            assertEquals("key", pair.getLeft());
            assertEquals(42, pair.getRight());
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair): Should create a Pair from a Map.Entry with null key")
        void of_mapEntry_nullKey_shouldCreatePair() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 42);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair);
            assertNull(pair.getLeft());
            assertEquals(42, pair.getRight());
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair): Should create a Pair from a Map.Entry with null value")
        void of_mapEntry_nullValue_shouldCreatePair() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("key", null);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair);
            assertEquals("key", pair.getLeft());
            assertNull(pair.getRight());
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair): Should create a Pair from a Map.Entry with both nulls")
        void of_mapEntry_bothNulls_shouldCreatePair() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair);
            assertNull(pair.getLeft());
            assertNull(pair.getRight());
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair): Should throw NullPointerException if Map.Entry is null")
        void of_mapEntry_nullEntry_shouldThrowNPE() {
            assertThrows(NullPointerException.class, () -> Pair.of((Map.Entry<String, Integer>) null));
        }

        @Test
        @DisplayName("ofNonNull(L left, R right): Should create a Pair with non-null values")
        void ofNonNull_nonNullValues_shouldCreatePair() {
            Pair<String, Integer> pair = Pair.ofNonNull("hello", 123);
            assertNotNull(pair);
            assertEquals("hello", pair.getLeft());
            assertEquals(123, pair.getRight());
        }

        @Test
        @DisplayName("ofNonNull(L left, R right): Should throw NullPointerException if left is null")
        void ofNonNull_nullLeft_shouldThrowNPE() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 123));
        }

        @Test
        @DisplayName("ofNonNull(L left, R right): Should throw NullPointerException if right is null")
        void ofNonNull_nullRight_shouldThrowNPE() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull("hello", null));
        }

        @Test
        @DisplayName("ofNonNull(L left, R right): Should throw NullPointerException if both are null")
        void ofNonNull_bothNull_shouldThrowNPE() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null));
        }
    }

    @Nested
    @DisplayName("Getter Methods")
    class GetterMethods {

        private final Pair<String, Integer> pair = Pair.of("test", 100);
        private final Pair<String, Integer> nullLeftPair = Pair.of(null, 100);
        private final Pair<String, Integer> nullRightPair = Pair.of("test", null);
        private final Pair<String, Integer> bothNullPair = Pair.of(null, null);

        @Test
        @DisplayName("getKey(): Should return the left value")
        void getKey_shouldReturnLeftValue() {
            assertEquals("test", pair.getKey());
            assertNull(nullLeftPair.getKey());
            assertEquals("test", nullRightPair.getKey());
            assertNull(bothNullPair.getKey());
        }

        @Test
        @DisplayName("getLeft(): Should return the left value")
        void getLeft_shouldReturnLeftValue() {
            assertEquals("test", pair.getLeft());
            assertNull(nullLeftPair.getLeft());
            assertEquals("test", nullRightPair.getLeft());
            assertNull(bothNullPair.getLeft());
        }

        @Test
        @DisplayName("getRight(): Should return the right value")
        void getRight_shouldReturnRightValue() {
            assertEquals(100, pair.getRight());
            assertEquals(100, nullLeftPair.getRight());
            assertNull(nullRightPair.getRight());
            assertNull(bothNullPair.getRight());
        }

        @Test
        @DisplayName("getValue(): Should return the right value")
        void getValue_shouldReturnRightValue() {
            assertEquals(100, pair.getValue());
            assertEquals(100, nullLeftPair.getValue());
            assertNull(nullRightPair.getValue());
            assertNull(bothNullPair.getValue());
        }
    }

    @Nested
    @DisplayName("Functional Methods")
    class FunctionalMethods {

        private final Pair<String, Integer> pair = Pair.of("hello", 123);

        @Test
        @DisplayName("accept(FailableBiConsumer): Should execute consumer with pair values")
        void accept_shouldExecuteConsumer() throws Exception {
            TestConsumer<String, Integer, Exception> consumer = new TestConsumer<>(false, null);
            pair.accept(consumer);

            assertTrue(consumer.isCalled());
            assertEquals("hello", consumer.getLastLeft());
            assertEquals(123, consumer.getLastRight());
        }

        @Test
        @DisplayName("accept(FailableBiConsumer): Should rethrow exception from consumer")
        void accept_shouldRethrowException() {
            IOException expectedException = new IOException("Test exception");
            TestConsumer<String, Integer, IOException> consumer = new TestConsumer<>(true, expectedException);

            IOException thrown = assertThrows(IOException.class, () -> pair.accept(consumer));
            assertSame(expectedException, thrown);
            assertTrue(consumer.isCalled());
        }

        @Test
        @DisplayName("accept(FailableBiConsumer): Should throw NullPointerException if consumer is null")
        void accept_nullConsumer_shouldThrowNPE() {
            assertThrows(NullPointerException.class, () -> pair.accept(null));
        }

        @Test
        @DisplayName("apply(FailableBiFunction): Should execute function with pair values and return result")
        void apply_shouldExecuteFunctionAndReturnResult() throws Exception {
            String expectedResult = "hello_123";
            TestFunction<String, Integer, String, Exception> function = new TestFunction<>(false, null, expectedResult);
            String result = pair.apply(function);

            assertTrue(function.isCalled());
            assertEquals("hello", function.getLastLeft());
            assertEquals(123, function.getLastRight());
            assertEquals(expectedResult, result);
        }

        @Test
        @DisplayName("apply(FailableBiFunction): Should rethrow exception from function")
        void apply_shouldRethrowException() {
            IOException expectedException = new IOException("Test exception");
            TestFunction<String, Integer, String, IOException> function = new TestFunction<>(true, expectedException, null);

            IOException thrown = assertThrows(IOException.class, () -> pair.apply(function));
            assertSame(expectedException, thrown);
            assertTrue(function.isCalled());
        }

        @Test
        @DisplayName("apply(FailableBiFunction): Should throw NullPointerException if function is null")
        void apply_nullFunction_shouldThrowNPE() {
            assertThrows(NullPointerException.class, () -> pair.apply(null));
        }
    }

    @Nested
    @DisplayName("Comparison and Equality Methods")
    class ComparisonAndEqualityMethods {

        @Test
        @DisplayName("compareTo(Pair<L, R> other): Should return 0 for equal pairs")
        void compareTo_equalPairs_shouldReturnZero() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertEquals(0, pair1.compareTo(pair2));
        }

        @Test
        @DisplayName("compareTo(Pair<L, R> other): Should compare based on left value first")
        void compareTo_differentLeft_shouldCompareByLeft() {
            Pair<String, Integer> pair1 = Pair.of("A", 10);
            Pair<String, Integer> pair2 = Pair.of("B", 1);
            assertTrue(pair1.compareTo(pair2) < 0); // "A" < "B"

            Pair<String, Integer> pair3 = Pair.of("C", 5);
            Pair<String, Integer> pair4 = Pair.of("B", 100);
            assertTrue(pair3.compareTo(pair4) > 0); // "C" > "B"
        }

        @Test
        @DisplayName("compareTo(Pair<L, R> other): Should compare based on right value if left values are equal")
        void compareTo_equalLeft_shouldCompareByRight() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 2);
            assertTrue(pair1.compareTo(pair2) < 0); // 1 < 2

            Pair<String, Integer> pair3 = Pair.of("A", 5);
            Pair<String, Integer> pair4 = Pair.of("A", 3);
            assertTrue(pair3.compareTo(pair4) > 0); // 5 > 3
        }

        @Test
        @DisplayName("compareTo(Pair<L, R> other): Should handle null left values correctly")
        void compareTo_nullLeftValues() {
            Pair<String, Integer> pair1 = Pair.of(null, 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertTrue(pair1.compareTo(pair2) < 0); // null < "A"

            Pair<String, Integer> pair3 = Pair.of("A", 1);
            Pair<String, Integer> pair4 = Pair.of(null, 1);
            assertTrue(pair3.compareTo(pair4) > 0); // "A" > null

            Pair<String, Integer> pair5 = Pair.of(null, 1);
            Pair<String, Integer> pair6 = Pair.of(null, 2);
            assertTrue(pair5.compareTo(pair6) < 0); // null == null, then 1 < 2
        }

        @Test
        @DisplayName("compareTo(Pair<L, R> other): Should handle null right values correctly")
        void compareTo_nullRightValues() {
            Pair<String, Integer> pair1 = Pair.of("A", null);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertTrue(pair1.compareTo(pair2) < 0); // null < 1

            Pair<String, Integer> pair3 = Pair.of("A", 1);
            Pair<String, Integer> pair4 = Pair.of("A", null);
            assertTrue(pair3.compareTo(pair4) > 0); // 1 > null

            Pair<String, Integer> pair5 = Pair.of("A", null);
            Pair<String, Integer> pair6 = Pair.of("A", null);
            assertEquals(0, pair5.compareTo(pair6)); // null == null
        }

        @Test
        @DisplayName("compareTo(Pair<L, R> other): Should throw NullPointerException if other pair is null")
        void compareTo_nullOther_shouldThrowNPE() {
            Pair<String, Integer> pair = Pair.of("A", 1);
            assertThrows(NullPointerException.class, () -> pair.compareTo(null));
        }

        @Test
        @DisplayName("equals(Object obj): Should return true for identical pairs")
        void equals_identicalPairs_shouldReturnTrue() {
            Pair<String, Integer> pair = Pair.of("A", 1);
            assertTrue(pair.equals(pair));
        }

        @Test
        @DisplayName("equals(Object obj): Should return true for equal pairs")
        void equals_equalPairs_shouldReturnTrue() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertTrue(pair1.equals(pair2));
        }

        @Test
        @DisplayName("equals(Object obj): Should return false for different left values")
        void equals_differentLeft_shouldReturnFalse() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("B", 1);
            assertFalse(pair1.equals(pair2));
        }

        @Test
        @DisplayName("equals(Object obj): Should return false for different right values")
        void equals_differentRight_shouldReturnFalse() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 2);
            assertFalse(pair1.equals(pair2));
        }

        @Test
        @DisplayName("equals(Object obj): Should return false for different left and right values")
        void equals_differentBoth_shouldReturnFalse() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("B", 2);
            assertFalse(pair1.equals(pair2));
        }

        @Test
        @DisplayName("equals(Object obj): Should return false for null object")
        void equals_nullObject_shouldReturnFalse() {
            Pair<String, Integer> pair = Pair.of("A", 1);
            assertFalse(pair.equals(null));
        }

        @Test
        @DisplayName("equals(Object obj): Should return false for different class type")
        void equals_differentClass_shouldReturnFalse() {
            Pair<String, Integer> pair = Pair.of("A", 1);
            assertFalse(pair.equals("A,1")); // Compare with a String
            assertFalse(pair.equals(new HashMap<>())); // Compare with a different object
        }

        @Test
        @DisplayName("equals(Object obj): Should handle null left values correctly")
        void equals_nullLeft_shouldBeEqual() {
            Pair<String, Integer> pair1 = Pair.of(null, 1);
            Pair<String, Integer> pair2 = Pair.of(null, 1);
            assertTrue(pair1.equals(pair2));

            Pair<String, Integer> pair3 = Pair.of(null, 1);
            Pair<String, Integer> pair4 = Pair.of("A", 1);
            assertFalse(pair3.equals(pair4));
        }

        @Test
        @DisplayName("equals(Object obj): Should handle null right values correctly")
        void equals_nullRight_shouldBeEqual() {
            Pair<String, Integer> pair1 = Pair.of("A", null);
            Pair<String, Integer> pair2 = Pair.of("A", null);
            assertTrue(pair1.equals(pair2));

            Pair<String, Integer> pair3 = Pair.of("A", null);
            Pair<String, Integer> pair4 = Pair.of("A", 1);
            assertFalse(pair3.equals(pair4));
        }

        @Test
        @DisplayName("equals(Object obj): Should handle both null values correctly")
        void equals_bothNull_shouldBeEqual() {
            Pair<String, Integer> pair1 = Pair.of(null, null);
            Pair<String, Integer> pair2 = Pair.of(null, null);
            assertTrue(pair1.equals(pair2));

            Pair<String, Integer> pair3 = Pair.of(null, null);
            Pair<String, Integer> pair4 = Pair.of("A", null);
            assertFalse(pair3.equals(pair4));

            Pair<String, Integer> pair5 = Pair.of(null, null);
            Pair<String, Integer> pair6 = Pair.of(null, 1);
            assertFalse(pair5.equals(pair6));
        }

        @Test
        @DisplayName("hashCode(): Should return same hash code for equal pairs")
        void hashCode_equalPairs_shouldReturnSameHashCode() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("A", 1);
            assertEquals(pair1.hashCode(), pair2.hashCode());
        }

        @Test
        @DisplayName("hashCode(): Should return different hash code for different pairs (not guaranteed, but likely)")
        void hashCode_differentPairs_shouldReturnDifferentHashCode() {
            Pair<String, Integer> pair1 = Pair.of("A", 1);
            Pair<String, Integer> pair2 = Pair.of("B", 2);
            assertNotEquals(pair1.hashCode(), pair2.hashCode());
        }

        @Test
        @DisplayName("hashCode(): Should handle null values correctly")
        void hashCode_nullValues_shouldBeConsistent() {
            Pair<String, Integer> pair1 = Pair.of(null, 1);
            Pair<String, Integer> pair2 = Pair.of(null, 1);
            assertEquals(pair1.hashCode(), pair2.hashCode());

            Pair<String, Integer> pair3 = Pair.of("A", null);
            Pair<String, Integer> pair4 = Pair.of("A", null);
            assertEquals(pair3.hashCode(), pair4.hashCode());

            Pair<String, Integer> pair5 = Pair.of(null, null);
            Pair<String, Integer> pair6 = Pair.of(null, null);
            assertEquals(pair5.hashCode(), pair6.hashCode());

            // Expected hash code for (null, null) is 0
            assertEquals(Objects.hashCode(null) ^ Objects.hashCode(null), pair5.hashCode());
            assertEquals(0, pair5.hashCode());
        }
    }

    @Nested
    @DisplayName("String Representation Methods")
    class StringRepresentationMethods {

        @Test
        @DisplayName("toString(): Should return default string representation for non-null values")
        void toString_nonNullValues_shouldReturnDefaultFormat() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertEquals("(hello,123)", pair.toString());
        }

        @Test
        @DisplayName("toString(): Should return default string representation for null left value")
        void toString_nullLeft_shouldReturnDefaultFormat() {
            Pair<String, Integer> pair = Pair.of(null, 123);
            assertEquals("(null,123)", pair.toString());
        }

        @Test
        @DisplayName("toString(): Should return default string representation for null right value")
        void toString_nullRight_shouldReturnDefaultFormat() {
            Pair<String, Integer> pair = Pair.of("hello", null);
            assertEquals("(hello,null)", pair.toString());
        }

        @Test
        @DisplayName("toString(): Should return default string representation for both null values")
        void toString_bothNull_shouldReturnDefaultFormat() {
            Pair<String, Integer> pair = Pair.of(null, null);
            assertEquals("(null,null)", pair.toString());
        }

        @Test
        @DisplayName("toString(String format): Should return formatted string for non-null values")
        void toString_format_nonNullValues_shouldReturnFormattedString() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertEquals("Left: hello, Right: 123", pair.toString("Left: %L, Right: %R"));
        }

        @Test
        @DisplayName("toString(String format): Should return formatted string for null left value")
        void toString_format_nullLeft_shouldReturnFormattedString() {
            Pair<String, Integer> pair = Pair.of(null, 123);
            assertEquals("Left: null, Right: 123", pair.toString("Left: %L, Right: %R"));
        }

        @Test
        @DisplayName("toString(String format): Should return formatted string for null right value")
        void toString_format_nullRight_shouldReturnFormattedString() {
            Pair<String, Integer> pair = Pair.of("hello", null);
            assertEquals("Left: hello, Right: null", pair.toString("Left: %L, Right: %R"));
        }

        @Test
        @DisplayName("toString(String format): Should return formatted string for both null values")
        void toString_format_bothNull_shouldReturnFormattedString() {
            Pair<String, Integer> pair = Pair.of(null, null);
            assertEquals("Left: null, Right: null", pair.toString("Left: %L, Right: %R"));
        }

        @Test
        @DisplayName("toString(String format): Should handle empty format string")
        void toString_format_emptyFormat_shouldReturnEmptyString() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertEquals("", pair.toString(""));
        }

        @Test
        @DisplayName("toString(String format): Should handle format string without placeholders")
        void toString_format_noPlaceholders_shouldReturnFormatStringAsIs() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertEquals("Just a string", pair.toString("Just a string"));
        }

        @Test
        @DisplayName("toString(String format): Should handle format string with only %L")
        void toString_format_onlyLeftPlaceholder_shouldReturnLeftValue() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertEquals("Left: hello", pair.toString("Left: %L"));
        }

        @Test
        @DisplayName("toString(String format): Should handle format string with only %R")
        void toString_format_onlyRightPlaceholder_shouldReturnRightValue() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertEquals("Right: 123", pair.toString("Right: %R"));
        }

        @Test
        @DisplayName("toString(String format): Should throw NullPointerException if format is null")
        void toString_nullFormat_shouldThrowNPE() {
            Pair<String, Integer> pair = Pair.of("hello", 123);
            assertThrows(NullPointerException.class, () -> pair.toString(null));
        }
    }
}