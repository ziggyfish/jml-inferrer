package org.apache.commons.lang3.tuple.p3;

import org.apache.commons.lang3.function.FailableBiConsumer;
import org.apache.commons.lang3.function.FailableBiFunction;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
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
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Pair Class Unit Tests")
class PairTestP3P3 {

    // Helper for creating pairs
    private static <L, R> Pair<L, R> createPair(L left, R right) {
        return Pair.of(left, right);
    }

    @Nested
    @DisplayName("Static Factory Methods")
    class StaticFactoryMethods {

        @Test
        @DisplayName("emptyArray() should return an empty array of Pair")
        void testEmptyArray() {
            Pair<?, ?>[] emptyArray = Pair.emptyArray();
            assertNotNull(emptyArray, "emptyArray() should not return null");
            assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
            // Verify it's a new array each time (or at least not the same instance)
            assertNotSame(Pair.emptyArray(), Pair.emptyArray(), "emptyArray() should return distinct array instances");
        }

        @Test
        @DisplayName("of(L left, R right) with non-null values")
        void testOfNonNullValues() {
            Pair<String, Integer> pair = Pair.of("Hello", 123);
            assertNotNull(pair, "Pair.of() should not return null for non-null inputs");
            assertEquals("Hello", pair.getLeft(), "Left value should match input");
            assertEquals(123, pair.getRight(), "Right value should match input");
        }

        @Test
        @DisplayName("of(L left, R right) with null left value")
        void testOfNullLeftValue() {
            Pair<String, Integer> pair = Pair.of(null, 123);
            assertNotNull(pair, "Pair.of() should not return null for null left input");
            assertNull(pair.getLeft(), "Left value should be null");
            assertEquals(123, pair.getRight(), "Right value should match input");
        }

        @Test
        @DisplayName("of(L left, R right) with null right value")
        void testOfNullRightValue() {
            Pair<String, Integer> pair = Pair.of("Hello", null);
            assertNotNull(pair, "Pair.of() should not return null for null right input");
            assertEquals("Hello", pair.getLeft(), "Left value should match input");
            assertNull(pair.getRight(), "Right value should be null");
        }

        @Test
        @DisplayName("of(L left, R right) with both null values")
        void testOfBothNullValues() {
            Pair<String, Integer> pair = Pair.of(null, null);
            assertNotNull(pair, "Pair.of() should not return null for both null inputs");
            assertNull(pair.getLeft(), "Left value should be null");
            assertNull(pair.getRight(), "Right value should be null");
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair) with non-null entry")
        void testOfMapEntryNonNull() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair.of(Map.Entry) should not return null for non-null entry");
            assertEquals("Key", pair.getLeft(), "Left value should match entry key");
            assertEquals(456, pair.getRight(), "Right value should match entry value");
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair) with null entry")
        void testOfMapEntryNull() {
            Pair<String, Integer> pair = Pair.of((Map.Entry<String, Integer>) null);
            assertNull(pair, "Pair.of(Map.Entry) should return null for null entry");
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair) with entry containing null key")
        void testOfMapEntryNullKey() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair.of(Map.Entry) should not return null for entry with null key");
            assertNull(pair.getLeft(), "Left value should be null");
            assertEquals(456, pair.getRight(), "Right value should match entry value");
        }

        @Test
        @DisplayName("of(Map.Entry<L, R> pair) with entry containing null value")
        void testOfMapEntryNullValue() {
            Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
            Pair<String, Integer> pair = Pair.of(entry);
            assertNotNull(pair, "Pair.of(Map.Entry) should not return null for entry with null value");
            assertEquals("Key", pair.getLeft(), "Left value should match entry key");
            assertNull(pair.getRight(), "Right value should be null");
        }

        @Test
        @DisplayName("ofNonNull(L left, R right) with non-null values")
        void testOfNonNullWithNonNullValues() {
            Pair<String, Integer> pair = Pair.ofNonNull("Alpha", 1);
            assertNotNull(pair, "Pair.ofNonNull() should not return null for non-null inputs");
            assertEquals("Alpha", pair.getLeft(), "Left value should match input");
            assertEquals(1, pair.getRight(), "Right value should match input");
        }

        @Test
        @DisplayName("ofNonNull(L left, R right) with null left value should throw NullPointerException")
        void testOfNonNullWithNullLeftValue() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, 1),
                    "Pair.ofNonNull() should throw NullPointerException for null left input");
        }

        @Test
        @DisplayName("ofNonNull(L left, R right) with null right value should throw NullPointerException")
        void testOfNonNullWithNullRightValue() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull("Alpha", null),
                    "Pair.ofNonNull() should throw NullPointerException for null right input");
        }

        @Test
        @DisplayName("ofNonNull(L left, R right) with both null values should throw NullPointerException")
        void testOfNonNullWithBothNullValues() {
            assertThrows(NullPointerException.class, () -> Pair.ofNonNull(null, null),
                    "Pair.ofNonNull() should throw NullPointerException for both null inputs");
        }
    }

    @Nested
    @DisplayName("Getter Methods")
    class GetterMethods {

        private final Pair<String, Integer> testPair = createPair("Test", 100);
        private final Pair<String, Integer> nullLeftPair = createPair(null, 200);
        private final Pair<String, Integer> nullRightPair = createPair("Test2", null);
        private final Pair<String, Integer> bothNullPair = createPair(null, null);

        @Test
        @DisplayName("getKey() should return the left value")
        void testGetKey() {
            assertEquals("Test", testPair.getKey(), "getKey() should return the left value");
            assertNull(nullLeftPair.getKey(), "getKey() should return null for null left value");
            assertEquals("Test2", nullRightPair.getKey(), "getKey() should return the left value when right is null");
            assertNull(bothNullPair.getKey(), "getKey() should return null when both values are null");
        }

        @Test
        @DisplayName("getLeft() should return the left value")
        void testGetLeft() {
            assertEquals("Test", testPair.getLeft(), "getLeft() should return the left value");
            assertNull(nullLeftPair.getLeft(), "getLeft() should return null for null left value");
            assertEquals("Test2", nullRightPair.getLeft(), "getLeft() should return the left value when right is null");
            assertNull(bothNullPair.getLeft(), "getLeft() should return null when both values are null");
        }

        @Test
        @DisplayName("getRight() should return the right value")
        void testGetRight() {
            assertEquals(100, testPair.getRight(), "getRight() should return the right value");
            assertEquals(200, nullLeftPair.getRight(), "getRight() should return the right value when left is null");
            assertNull(nullRightPair.getRight(), "getRight() should return null for null right value");
            assertNull(bothNullPair.getRight(), "getRight() should return null when both values are null");
        }

        @Test
        @DisplayName("getValue() should return the right value")
        void testGetValue() {
            assertEquals(100, testPair.getValue(), "getValue() should return the right value");
            assertEquals(200, nullLeftPair.getValue(), "getValue() should return the right value when left is null");
            assertNull(nullRightPair.getValue(), "getValue() should return null for null right value");
            assertNull(bothNullPair.getValue(), "getValue() should return null when both values are null");
        }
    }

    @Nested
    @DisplayName("Functional Interface Methods")
    class FunctionalInterfaceMethods {

        private final Pair<String, Integer> testPair = createPair("Hello", 42);
        private final Pair<String, Integer> nullPair = createPair(null, null);

        @Test
        @DisplayName("accept(FailableBiConsumer) should execute consumer with left and right values")
        void testAccept() throws Exception {
            AtomicReference<String> leftRef = new AtomicReference<>();
            AtomicReference<Integer> rightRef = new AtomicReference<>();

            FailableBiConsumer<String, Integer, Exception> consumer = (l, r) -> {
                leftRef.set(l);
                rightRef.set(r);
            };

            testPair.accept(consumer);
            assertEquals("Hello", leftRef.get(), "Consumer should receive left value");
            assertEquals(42, rightRef.get(), "Consumer should receive right value");

            nullPair.accept(consumer);
            assertNull(leftRef.get(), "Consumer should receive null left value");
            assertNull(rightRef.get(), "Consumer should receive null right value");
        }

        @Test
        @DisplayName("accept(FailableBiConsumer) should rethrow checked exception")
        void testAcceptThrowsCheckedException() {
            FailableBiConsumer<String, Integer, IOException> consumer = (l, r) -> {
                throw new IOException("Test IOException");
            };

            IOException thrown = assertThrows(IOException.class, () -> testPair.accept(consumer),
                    "accept() should rethrow IOException");
            assertEquals("Test IOException", thrown.getMessage());
        }

        @Test
        @DisplayName("accept(FailableBiConsumer) should rethrow unchecked exception")
        void testAcceptThrowsUncheckedException() {
            FailableBiConsumer<String, Integer, RuntimeException> consumer = (l, r) -> {
                throw new IllegalArgumentException("Test IllegalArgumentException");
            };

            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () -> testPair.accept(consumer),
                    "accept() should rethrow IllegalArgumentException");
            assertEquals("Test IllegalArgumentException", thrown.getMessage());
        }

        @Test
        @DisplayName("accept(FailableBiConsumer) with null consumer should throw NullPointerException")
        void testAcceptWithNullConsumer() {
            assertThrows(NullPointerException.class, () -> testPair.accept(null),
                    "accept() should throw NullPointerException for null consumer");
        }


        @Test
        @DisplayName("apply(FailableBiFunction) should execute function and return its result")
        void testApply() throws Exception {
            FailableBiFunction<String, Integer, String, Exception> function = (l, r) -> l + "-" + r;

            String result = testPair.apply(function);
            assertEquals("Hello-42", result, "Function should return concatenated string");

            FailableBiFunction<String, Integer, String, Exception> nullFunction = (l, r) -> l + "-" + r;
            String nullResult = nullPair.apply(nullFunction);
            assertEquals("null-null", nullResult, "Function should handle null inputs correctly");
        }

        @Test
        @DisplayName("apply(FailableBiFunction) should rethrow checked exception")
        void testApplyThrowsCheckedException() {
            FailableBiFunction<String, Integer, String, IOException> function = (l, r) -> {
                throw new IOException("Test IOException from apply");
            };

            IOException thrown = assertThrows(IOException.class, () -> testPair.apply(function),
                    "apply() should rethrow IOException");
            assertEquals("Test IOException from apply", thrown.getMessage());
        }

        @Test
        @DisplayName("apply(FailableBiFunction) should rethrow unchecked exception")
        void testApplyThrowsUncheckedException() {
            FailableBiFunction<String, Integer, String, RuntimeException> function = (l, r) -> {
                throw new IllegalStateException("Test IllegalStateException from apply");
            };

            IllegalStateException thrown = assertThrows(IllegalStateException.class, () -> testPair.apply(function),
                    "apply() should rethrow IllegalStateException");
            assertEquals("Test IllegalStateException from apply", thrown.getMessage());
        }

        @Test
        @DisplayName("apply(FailableBiFunction) with null function should throw NullPointerException")
        void testApplyWithNullFunction() {
            assertThrows(NullPointerException.class, () -> testPair.apply(null),
                    "apply() should throw NullPointerException for null function");
        }
    }

    @Nested
    @DisplayName("Equality and Hashing")
    class EqualityAndHashing {

        private final Pair<String, Integer> pair1 = createPair("A", 1);
        private final Pair<String, Integer> pair2 = createPair("A", 1);
        private final Pair<String, Integer> pair3 = createPair("B", 1);
        private final Pair<String, Integer> pair4 = createPair("A", 2);
        private final Pair<String, Integer> pairNullLeft1 = createPair(null, 1);
        private final Pair<String, Integer> pairNullLeft2 = createPair(null, 1);
        private final Pair<String, Integer> pairNullRight1 = createPair("A", null);
        private final Pair<String, Integer> pairNullRight2 = createPair("A", null);
        private final Pair<String, Integer> pairBothNull1 = createPair(null, null);
        private final Pair<String, Integer> pairBothNull2 = createPair(null, null);

        @Test
        @DisplayName("equals() should return true for identical pairs")
        void testEqualsIdenticalPairs() {
            assertTrue(pair1.equals(pair1), "A pair should be equal to itself");
            assertTrue(pair1.equals(pair2), "Two pairs with same values should be equal");
            assertTrue(pairNullLeft1.equals(pairNullLeft2), "Pairs with null left and same right should be equal");
            assertTrue(pairNullRight1.equals(pairNullRight2), "Pairs with same left and null right should be equal");
            assertTrue(pairBothNull1.equals(pairBothNull2), "Pairs with both null values should be equal");
        }

        @Test
        @DisplayName("equals() should return false for different pairs")
        void testEqualsDifferentPairs() {
            assertFalse(pair1.equals(pair3), "Pairs with different left values should not be equal");
            assertFalse(pair1.equals(pair4), "Pairs with different right values should not be equal");
            assertFalse(pair1.equals(pairNullLeft1), "Pairs with null vs non-null left should not be equal");
            assertFalse(pair1.equals(pairNullRight1), "Pairs with null vs non-null right should not be equal");
            assertFalse(pairNullLeft1.equals(pairNullRight1), "Pairs with different null positions should not be equal");
        }

        @Test
        @DisplayName("equals() should return false for null object")
        void testEqualsNullObject() {
            assertFalse(pair1.equals(null), "A pair should not be equal to null");
        }

        @Test
        @DisplayName("equals() should return false for different object types")
        void testEqualsDifferentObjectType() {
            assertFalse(pair1.equals("A string"), "A pair should not be equal to an object of a different type");
            assertFalse(pair1.equals(new HashMap<>()), "A pair should not be equal to an object of a different type");
        }

        @Test
        @DisplayName("hashCode() should be consistent with equals()")
        void testHashCodeConsistency() {
            assertEquals(pair1.hashCode(), pair2.hashCode(), "Hash codes should be equal for equal pairs");
            assertEquals(pairNullLeft1.hashCode(), pairNullLeft2.hashCode(), "Hash codes should be equal for equal pairs with null left");
            assertEquals(pairNullRight1.hashCode(), pairNullRight2.hashCode(), "Hash codes should be equal for equal pairs with null right");
            assertEquals(pairBothNull1.hashCode(), pairBothNull2.hashCode(), "Hash codes should be equal for equal pairs with both null");

            assertNotEquals(pair1.hashCode(), pair3.hashCode(), "Hash codes should be different for unequal pairs (left)");
            assertNotEquals(pair1.hashCode(), pair4.hashCode(), "Hash codes should be different for unequal pairs (right)");
        }

        @Test
        @DisplayName("hashCode() should return 0 for a pair of nulls")
        void testHashCodeBothNull() {
            assertEquals(0, createPair(null, null).hashCode(), "Hash code for (null, null) should be 0");
        }

        @Test
        @DisplayName("hashCode() for pair with one null value")
        void testHashCodeOneNull() {
            assertEquals(Objects.hashCode("Left") ^ 0, createPair("Left", null).hashCode());
            assertEquals(0 ^ Objects.hashCode(123), createPair(null, 123).hashCode());
        }
    }

    @Nested
    @DisplayName("Comparison (compareTo)")
    class ComparisonTests {

        private static Stream<Arguments> compareToData() {
            return Stream.of(
                    // Equal pairs
                    Arguments.of(createPair("A", 1), createPair("A", 1), 0),
                    Arguments.of(createPair(null, 1), createPair(null, 1), 0),
                    Arguments.of(createPair("A", null), createPair("A", null), 0),
                    Arguments.of(createPair(null, null), createPair(null, null), 0),

                    // Left value differences
                    Arguments.of(createPair("A", 1), createPair("B", 1), -1), // A < B
                    Arguments.of(createPair("B", 1), createPair("A", 1), 1),  // B > A
                    Arguments.of(createPair(null, 1), createPair("A", 1), -1), // null < A
                    Arguments.of(createPair("A", 1), createPair(null, 1), 1),  // A > null

                    // Right value differences (when left values are equal)
                    Arguments.of(createPair("A", 1), createPair("A", 2), -1), // 1 < 2
                    Arguments.of(createPair("A", 2), createPair("A", 1), 1),  // 2 > 1
                    Arguments.of(createPair("A", null), createPair("A", 1), -1), // null < 1
                    Arguments.of(createPair("A", 1), createPair("A", null), 1),  // 1 > null

                    // Mixed differences (left takes precedence)
                    Arguments.of(createPair("A", 5), createPair("B", 1), -1), // A < B, right values don't matter
                    Arguments.of(createPair("B", 1), createPair("A", 5), 1)   // B > A, right values don't matter
            );
        }

        @ParameterizedTest(name = "compareTo({0}, {1}) should return {2}")
        @MethodSource("compareToData")
        @DisplayName("compareTo() should correctly compare pairs based on left then right")
        <L extends Comparable<L>, R extends Comparable<R>>
        void testCompareTo(Pair<L, R> pair1, Pair<L, R> pair2, int expectedSign) {
            int result = pair1.compareTo(pair2);
            if (expectedSign == 0) {
                assertEquals(0, result, () -> String.format("%s should be equal to %s", pair1, pair2));
            } else if (expectedSign < 0) {
                assertTrue(result < 0, () -> String.format("%s should be less than %s", pair1, pair2));
            } else {
                assertTrue(result > 0, () -> String.format("%s should be greater than %s", pair1, pair2));
            }
        }

        @Test
        @DisplayName("compareTo() with null 'other' pair should throw NullPointerException")
        void testCompareToNullOther() {
            Pair<String, Integer> pair = createPair("A", 1);
            assertThrows(NullPointerException.class, () -> pair.compareTo(null),
                    "compareTo() should throw NullPointerException for null 'other' pair");
        }

        @Test
        @DisplayName("compareTo() with non-comparable types should throw ClassCastException")
        void testCompareToNonComparableTypes() {
            // Create a Pair with non-comparable types
            Pair<Object, Object> pair1 = createPair(new Object(), new Object());
            Pair<Object, Object> pair2 = createPair(new Object(), new Object());

            // This should ideally be caught at compile time if types are strict,
            // but if raw types or Object are used, it will fail at runtime.
            // The JML specification implies L and R are Comparable, but the method signature doesn't enforce it.
            // Commons Lang Pair actually implements Comparable<Pair<L,R>> only if L and R are Comparable.
            // So, this test case might not be directly applicable if Pair is correctly typed.
            // However, if someone creates Pair<NonComparable, NonComparable>, compareTo will fail.
            // Let's simulate this by casting to a type that *could* be comparable, but isn't.
            Pair<String, Object> pairNonComparableRight = createPair("A", new Object());
            Pair<String, Object> pairNonComparableRight2 = createPair("A", new Object());

            // The actual implementation of Pair.compareTo uses ComparableUtils.compare,
            // which handles nulls and non-comparable types by throwing ClassCastException.
            assertThrows(ClassCastException.class, () -> pairNonComparableRight.compareTo(pairNonComparableRight2),
                    "compareTo() should throw ClassCastException if types are not comparable");

            Pair<Object, String> pairNonComparableLeft = createPair(new Object(), "B");
            Pair<Object, String> pairNonComparableLeft2 = createPair(new Object(), "B");
            assertThrows(ClassCastException.class, () -> pairNonComparableLeft.compareTo(pairNonComparableLeft2),
                    "compareTo() should throw ClassCastException if types are not comparable");
        }
    }

    @Nested
    @DisplayName("String Representation")
    class StringRepresentation {

        @Test
        @DisplayName("toString() should return default format '(left,right)'")
        void testToStringDefaultFormat() {
            Pair<String, Integer> pair = createPair("Key", 123);
            assertEquals("(Key,123)", pair.toString(), "Default toString format incorrect");

            Pair<String, Integer> nullLeft = createPair(null, 456);
            assertEquals("(null,456)", nullLeft.toString(), "Default toString format with null left incorrect");

            Pair<String, Integer> nullRight = createPair("Value", null);
            assertEquals("(Value,null)", nullRight.toString(), "Default toString format with null right incorrect");

            Pair<String, Integer> bothNull = createPair(null, null);
            assertEquals("(null,null)", bothNull.toString(), "Default toString format with both null incorrect");
        }

        @ParameterizedTest(name = "toString(\"{0}\") for ('A', 1) should be \"{1}\"")
        @MethodSource("toStringFormatData")
        @DisplayName("toString(String format) should apply custom format")
        void testToStringCustomFormat(String format, String expected) {
            Pair<String, Integer> pair = createPair("A", 1);
            assertEquals(expected, pair.toString(format), "Custom toString format incorrect");
        }

        private static Stream<Arguments> toStringFormatData() {
            return Stream.of(
                    Arguments.of("%s=%s", "A=1"),
                    Arguments.of("Left: %s, Right: %s", "Left: A, Right: 1"),
                    Arguments.of("[%s|%s]", "[A|1]"),
                    Arguments.of("L:%1$s R:%2$s", "L:A R:1"), // Using argument index
                    Arguments.of("Only Left: %1$s", "Only Left: A"), // Only left
                    Arguments.of("Only Right: %2$s", "Only Right: 1"), // Only right
                    Arguments.of("No values", "No values") // No placeholders
            );
        }

        @Test
        @DisplayName("toString(String format) with null values should handle them correctly")
        void testToStringCustomFormatWithNullValues() {
            Pair<String, Integer> nullLeft = createPair(null, 456);
            assertEquals("Left: null, Right: 456", nullLeft.toString("Left: %s, Right: %s"));

            Pair<String, Integer> nullRight = createPair("Value", null);
            assertEquals("Left: Value, Right: null", nullRight.toString("Left: %s, Right: %s"));

            Pair<String, Integer> bothNull = createPair(null, null);
            assertEquals("Left: null, Right: null", bothNull.toString("Left: %s, Right: %s"));
        }

        @ParameterizedTest
        @NullSource
        @ValueSource(strings = {"", " "})
        @DisplayName("toString(String format) with null or empty format should throw IllegalArgumentException")
        void testToStringCustomFormatWithInvalidFormat(String format) {
            Pair<String, Integer> pair = createPair("A", 1);
            assertThrows(IllegalArgumentException.class, () -> pair.toString(format),
                    "toString(format) should throw IllegalArgumentException for null/empty format");
        }

        @Test
        @DisplayName("toString(String format) with malformed format string should throw IllegalFormatException")
        void testToStringCustomFormatWithMalformedFormat() {
            Pair<String, Integer> pair = createPair("A", 1);
            assertThrows(java.util.IllegalFormatException.class, () -> pair.toString("%z"),
                    "toString(format) should throw IllegalFormatException for malformed format string");
        }
    }
}