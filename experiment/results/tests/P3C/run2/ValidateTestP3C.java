```java
package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.Validate;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

public class ValidateTestP3CP3C {

    // Helper method to create an executable for assertions
    private Executable assertThrowsIAE(Executable executable) {
        return () -> assertThrows(IllegalArgumentException.class, executable);
    }

    private Executable assertThrowsISE(Executable executable) {
        return () -> assertThrows(IllegalStateException.class, executable);
    }

    @Nested
    class ExclusiveBetweenTests {

        // double overloads
        @Test
        void exclusiveBetweenDouble_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0));
            assertDoesNotThrow(() -> Validate.exclusiveBetween(-10.0, 0.0, -5.0));
            assertDoesNotThrow(() -> Validate.exclusiveBetween(-5.0, 5.0, 0.0));
        }

        @Test
        void exclusiveBetweenDouble_EdgeCases_ValueAtStartBoundary() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0.0, 10.0, 0.0)).execute();
        }

        @Test
        void exclusiveBetweenDouble_EdgeCases_ValueAtEndBoundary() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0.0, 10.0, 10.0)).execute();
        }

        @Test
        void exclusiveBetweenDouble_EdgeCases_StartEqualsEnd() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(5.0, 5.0, 5.0)).execute();
            assertThrowsIAE(() -> Validate.exclusiveBetween(5.0, 5.0, 4.0)).execute();
            assertThrowsIAE(() -> Validate.exclusiveBetween(5.0, 5.0, 6.0)).execute();
        }

        @Test
        void exclusiveBetweenDouble_FailureScenarios_ValueLessThanStart() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0.0, 10.0, -1.0)).execute();
        }

        @Test
        void exclusiveBetweenDouble_FailureScenarios_ValueGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0.0, 10.0, 11.0)).execute();
        }

        @Test
        void exclusiveBetweenDouble_FailureScenarios_StartGreaterThanEnd() {
            // This is not explicitly forbidden by JML, but it's an invalid range.
            // The current implementation will correctly throw if value is not between them.
            assertThrowsIAE(() -> Validate.exclusiveBetween(10.0, 0.0, 5.0)).execute();
            assertThrowsIAE(() -> Validate.exclusiveBetween(10.0, 0.0, 10.0)).execute();
            assertThrowsIAE(() -> Validate.exclusiveBetween(10.0, 0.0, 0.0)).execute();
            assertDoesNotThrow(() -> Validate.exclusiveBetween(10.0, 0.0, 15.0)); // value > start and value > end
            assertDoesNotThrow(() -> Validate.exclusiveBetween(10.0, 0.0, -5.0)); // value < start and value < end
        }

        @Test
        void exclusiveBetweenDoubleWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0, "Custom message"));
        }

        @Test
        void exclusiveBetweenDoubleWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not exclusive between %s and %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, 0.0, message));
            assertEquals(message, e.getMessage());

            e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, 10.0, message));
            assertEquals(message, e.getMessage());

            e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, -1.0, message));
            assertEquals(message, e.getMessage());
        }

        // long overloads
        @Test
        void exclusiveBetweenLong_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L));
            assertDoesNotThrow(() -> Validate.exclusiveBetween(-10L, 0L, -5L));
            assertDoesNotThrow(() -> Validate.exclusiveBetween(-5L, 5L, 0L));
        }

        @Test
        void exclusiveBetweenLong_EdgeCases_ValueAtStartBoundary() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0L, 10L, 0L)).execute();
        }

        @Test
        void exclusiveBetweenLong_EdgeCases_ValueAtEndBoundary() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0L, 10L, 10L)).execute();
        }

        @Test
        void exclusiveBetweenLong_EdgeCases_StartEqualsEnd() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(5L, 5L, 5L)).execute();
        }

        @Test
        void exclusiveBetweenLong_FailureScenarios_ValueLessThanStart() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0L, 10L, -1L)).execute();
        }

        @Test
        void exclusiveBetweenLong_FailureScenarios_ValueGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.exclusiveBetween(0L, 10L, 11L)).execute();
        }

        @Test
        void exclusiveBetweenLongWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L, "Custom message"));
        }

        @Test
        void exclusiveBetweenLongWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not exclusive between %s and %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0L, 10L, 0L, message));
            assertEquals(message, e.getMessage());
        }

        // Comparable overloads
        @Test
        void exclusiveBetweenComparable_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "z", "m"));
            assertDoesNotThrow(() -> Validate.exclusiveBetween(Integer.valueOf(0), Integer.valueOf(10), Integer.valueOf(5)));
        }

        @Test
        void exclusiveBetweenComparable_EdgeCases_ValueAtStartBoundary() {
            assertThrowsIAE(() -> Validate.exclusiveBetween("a", "z", "a")).execute();
            assertThrowsIAE(() -> Validate.exclusiveBetween(Integer.valueOf(0), Integer.valueOf(10), Integer.valueOf(0))).execute();
        }

        @Test
        void exclusiveBetweenComparable_EdgeCases_ValueAtEndBoundary() {
            assertThrowsIAE(() -> Validate.exclusiveBetween("a", "z", "z")).execute();
            assertThrowsIAE(() -> Validate.exclusiveBetween(Integer.valueOf(0), Integer.valueOf(10), Integer.valueOf(10))).execute();
        }

        @Test
        void exclusiveBetweenComparable_EdgeCases_StartEqualsEnd() {
            assertThrowsIAE(() -> Validate.exclusiveBetween("a", "a", "a")).execute();
        }

        @Test
        void exclusiveBetweenComparable_FailureScenarios_ValueLessThanStart() {
            assertThrowsIAE(() -> Validate.exclusiveBetween("b", "z", "a")).execute();
        }

        @Test
        void exclusiveBetweenComparable_FailureScenarios_ValueGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.exclusiveBetween("a", "y", "z")).execute();
        }

        @Test
        void exclusiveBetweenComparable_FailureScenarios_NullStart() {
            assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween(null, "z", "m"));
        }

        @Test
        void exclusiveBetweenComparable_FailureScenarios_NullEnd() {
            assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween("a", null, "m"));
        }

        @Test
        void exclusiveBetweenComparable_FailureScenarios_NullValue() {
            assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween("a", "z", null));
        }

        @Test
        void exclusiveBetweenComparableWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "z", "m", "Custom message %s", "arg"));
        }

        @Test
        void exclusiveBetweenComparableWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not exclusive between %s and %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween("a", "z", "a", message, "val", "start", "end"));
            assertEquals(String.format(message, "val", "start", "end"), e.getMessage());
        }
    }

    @Nested
    class FiniteTests {

        @Test
        void finiteDouble_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.finite(0.0));
            assertDoesNotThrow(() -> Validate.finite(1.0));
            assertDoesNotThrow(() -> Validate.finite(-1.0));
            assertDoesNotThrow(() -> Validate.finite(Double.MAX_VALUE));
            assertDoesNotThrow(() -> Validate.finite(Double.MIN_VALUE));
        }

        @Test
        void finiteDouble_FailureScenarios_NaN() {
            assertThrowsIAE(() -> Validate.finite(Double.NaN)).execute();
        }

        @Test
        void finiteDouble_FailureScenarios_PositiveInfinity() {
            assertThrowsIAE(() -> Validate.finite(Double.POSITIVE_INFINITY)).execute();
        }

        @Test
        void finiteDouble_FailureScenarios_NegativeInfinity() {
            assertThrowsIAE(() -> Validate.finite(Double.NEGATIVE_INFINITY)).execute();
        }

        @Test
        void finiteDoubleWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.finite(0.0, "Custom message %s", "arg"));
        }

        @Test
        void finiteDoubleWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not finite";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.finite(Double.NaN, message, "NaN"));
            assertEquals(String.format(message, "NaN"), e.getMessage());

            e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.finite(Double.POSITIVE_INFINITY, message, "Infinity"));
            assertEquals(String.format(message, "Infinity"), e.getMessage());
        }
    }

    @Nested
    class InclusiveBetweenTests {

        // double overloads
        @Test
        void inclusiveBetweenDouble_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0));
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 0.0)); // Edge: start
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 10.0)); // Edge: end
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5.0, 5.0, 5.0)); // Edge: start == end == value
        }

        @Test
        void inclusiveBetweenDouble_FailureScenarios_ValueLessThanStart() {
            assertThrowsIAE(() -> Validate.inclusiveBetween(0.0, 10.0, -1.0)).execute();
        }

        @Test
        void inclusiveBetweenDouble_FailureScenarios_ValueGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.inclusiveBetween(0.0, 10.0, 11.0)).execute();
        }

        @Test
        void inclusiveBetweenDouble_FailureScenarios_StartGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.inclusiveBetween(10.0, 0.0, 5.0)).execute();
            assertThrowsIAE(() -> Validate.inclusiveBetween(10.0, 0.0, 10.0)).execute();
            assertThrowsIAE(() -> Validate.inclusiveBetween(10.0, 0.0, 0.0)).execute();
            assertDoesNotThrow(() -> Validate.inclusiveBetween(10.0, 0.0, 15.0)); // value > start and value > end
            assertDoesNotThrow(() -> Validate.inclusiveBetween(10.0, 0.0, -5.0)); // value < start and value < end
        }

        @Test
        void inclusiveBetweenDoubleWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0, "Custom message"));
        }

        @Test
        void inclusiveBetweenDoubleWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not inclusive between %s and %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0.0, 10.0, -1.0, message));
            assertEquals(message, e.getMessage());
        }

        // long overloads
        @Test
        void inclusiveBetweenLong_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L));
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 0L));
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 10L));
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5L, 5L, 5L));
        }

        @Test
        void inclusiveBetweenLong_FailureScenarios_ValueLessThanStart() {
            assertThrowsIAE(() -> Validate.inclusiveBetween(0L, 10L, -1L)).execute();
        }

        @Test
        void inclusiveBetweenLong_FailureScenarios_ValueGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.inclusiveBetween(0L, 10L, 11L)).execute();
        }

        @Test
        void inclusiveBetweenLongWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L, "Custom message"));
        }

        @Test
        void inclusiveBetweenLongWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not inclusive between %s and %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0L, 10L, -1L, message));
            assertEquals(message, e.getMessage());
        }

        // Comparable overloads
        @Test
        void inclusiveBetweenComparable_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "m"));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "a"));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "z"));
            assertDoesNotThrow(() -> Validate.inclusiveBetween(Integer.valueOf(0), Integer.valueOf(10), Integer.valueOf(5)));
        }

        @Test
        void inclusiveBetweenComparable_FailureScenarios_ValueLessThanStart() {
            assertThrowsIAE(() -> Validate.inclusiveBetween("b", "z", "a")).execute();
        }

        @Test
        void inclusiveBetweenComparable_FailureScenarios_ValueGreaterThanEnd() {
            assertThrowsIAE(() -> Validate.inclusiveBetween("a", "y", "z")).execute();
        }

        @Test
        void inclusiveBetweenComparable_FailureScenarios_NullStart() {
            assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween(null, "z", "m"));
        }

        @Test
        void inclusiveBetweenComparable_FailureScenarios_NullEnd() {
            assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween("a", null, "m"));
        }

        @Test
        void inclusiveBetweenComparable_FailureScenarios_NullValue() {
            assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween("a", "z", null));
        }

        @Test
        void inclusiveBetweenComparableWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "m", "Custom message %s", "arg"));
        }

        @Test
        void inclusiveBetweenComparableWithMessage_FailureScenarios_CustomMessage() {
            String message = "Value %s is not inclusive between %s and %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween("a", "z", "!", message, "!", "a", "z"));
            assertEquals(String.format(message, "!", "a", "z"), e.getMessage());
        }
    }

    @Nested
    class IsAssignableFromTests {

        @Test
        void isAssignableFrom_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, String.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(List.class, ArrayList.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Number.class, Integer.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(String.class, String.class)); // Same class
        }

        @Test
        void isAssignableFrom_FailureScenarios_NotAssignableFrom() {
            assertThrowsIAE(() -> Validate.isAssignableFrom(String.class, Object.class)).execute();
            assertThrowsIAE(() -> Validate.isAssignableFrom(ArrayList.class, List.class)).execute();
            assertThrowsIAE(() -> Validate.isAssignableFrom(Integer.class, Double.class)).execute();
        }

        @Test
        void isAssignableFrom_FailureScenarios_NullSuperType() {
            assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(null, String.class));
        }

        @Test
        void isAssignableFrom_FailureScenarios_NullType() {
            assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(Object.class, null));
        }

        @Test
        void isAssignableFromWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, String.class, "Msg %s", "arg"));
        }

        @Test
        void isAssignableFromWithMessage_FailureScenarios_CustomMessage() {
            String message = "%s is not assignable from %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isAssignableFrom(String.class, Object.class, message, "String", "Object"));
            assertEquals(String.format(message, "String", "Object"), e.getMessage());
        }
    }

    @Nested
    class IsInstanceOfTests {

        @Test
        void isInstanceOf_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isInstanceOf(String.class, "hello"));
            assertDoesNotThrow(() -> Validate.isInstanceOf(Object.class, "hello"));
            assertDoesNotThrow(() -> Validate.isInstanceOf(List.class, new ArrayList<>()));
            assertDoesNotThrow(() -> Validate.isInstanceOf(Integer.class, 10));
        }

        @Test
        void isInstanceOf_FailureScenarios_NotInstanceOf() {
            assertThrowsIAE(() -> Validate.isInstanceOf(Integer.class, "hello")).execute();
            assertThrowsIAE(() -> Validate.isInstanceOf(String.class, 10)).execute();
            assertThrowsIAE(() -> Validate.isInstanceOf(ArrayList.class, new LinkedList<>())).execute();
        }

        @Test
        void isInstanceOf_FailureScenarios_NullType() {
            assertThrows(NullPointerException.class, () -> Validate.isInstanceOf(null, "hello"));
        }

        @Test
        void isInstanceOf_FailureScenarios_NullObject() {
            assertThrowsIAE(() -> Validate.isInstanceOf(String.class, null)).execute();
        }

        @Test
        void isInstanceOfWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isInstanceOf(String.class, "hello", "Msg %s", "arg"));
        }

        @Test
        void isInstanceOfWithMessage_FailureScenarios_CustomMessage() {
            String message = "Expected instance of %s but got %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isInstanceOf(Integer.class, "hello", message, "Integer", "String"));
            assertEquals(String.format(message, "Integer", "String"), e.getMessage());
        }
    }

    @Nested
    class IsTrueTests {

        @Test
        void isTrue_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isTrue(true));
        }

        @Test
        void isTrue_FailureScenarios_FalseExpression() {
            assertThrowsIAE(() -> Validate.isTrue(false)).execute();
        }

        @Test
        void isTrueWithMessageDouble_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isTrue(true, "Msg %s", 1.0));
        }

        @Test
        void isTrueWithMessageDouble_FailureScenarios_CustomMessage() {
            String message = "Expression is false, value: %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isTrue(false, message, 123.45));
            assertEquals(String.format(message, 123.45), e.getMessage());
        }

        @Test
        void isTrueWithMessageLong_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isTrue(true, "Msg %s", 1L));
        }

        @Test
        void isTrueWithMessageLong_FailureScenarios_CustomMessage() {
            String message = "Expression is false, value: %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isTrue(false, message, 123L));
            assertEquals(String.format(message, 123L), e.getMessage());
        }

        @Test
        void isTrueWithMessageObject_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isTrue(true, "Msg %s", "arg"));
        }

        @Test
        void isTrueWithMessageObject_FailureScenarios_CustomMessage() {
            String message = "Expression is false, arg: %s";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isTrue(false, message, "test"));
            assertEquals(String.format(message, "test"), e.getMessage());
        }

        @Test
        void isTrueWithMessageSupplier_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.isTrue(true, () -> "Supplier message"));
        }

        @Test
        void isTrueWithMessageSupplier_FailureScenarios_CustomMessage() {
            Supplier<String> supplier = () -> "Lazy message";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isTrue(false, supplier));
            assertEquals("Lazy message", e.getMessage());
        }

        @Test
        void isTrueWithMessageSupplier_FailureScenarios_NullSupplier() {
            assertThrows(NullPointerException.class, () -> Validate.isTrue(false, (Supplier<String>) null));
        }
    }

    @Nested
    class MatchesPatternTests {

        @Test
        void matchesPattern_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.matchesPattern("abc", "abc"));
            assertDoesNotThrow(() -> Validate.matchesPattern("hello world", "hello.*"));
            assertDoesNotThrow(() -> Validate.matchesPattern("12345", "\\d+"));
            assertDoesNotThrow(() -> Validate.matchesPattern("abc", "[a-c]+"));
        }

        @Test
        void matchesPattern_FailureScenarios_NoMatch() {
            assertThrowsIAE(() -> Validate.matchesPattern("abc", "xyz")).execute();
            assertThrowsIAE(() -> Validate.matchesPattern("hello", "world")).execute();
            assertThrowsIAE(() -> Validate.matchesPattern("123", "[a-z]+")).execute();
        }

        @Test
        void matchesPattern_FailureScenarios_NullInput() {
            assertThrowsIAE(() -> Validate.matchesPattern(null, ".*")).execute();
        }

        @Test
        void matchesPattern_FailureScenarios_NullPattern() {
            assertThrows(NullPointerException.class, () -> Validate.matchesPattern("abc", null));
        }

        @Test
        void matchesPattern_FailureScenarios_InvalidPattern() {
            assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("abc", "[")); // Malformed pattern
        }

        @Test
        void matchesPatternWithMessage_NormalBehavior() {
            assertDoesNotThrow(() -> Validate.matchesPattern("abc", "abc", "Msg %s", "arg"));
        }

        @Test
        void matchesPatternWithMessage_FailureScenarios_CustomMessage() {
            String message = "Input '%s' does not match pattern '%s'";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.matchesPattern("abc", "xyz", message, "abc", "xyz"));
            assertEquals(String.format(message, "abc", "xyz"), e.getMessage());
        }
    }

    @Nested
    class NoNullElementsTests {

        // Iterable overloads
        @Test
        void noNullElementsIterable_NormalBehavior() {
            List<String> list = Arrays.asList("a", "b", "c");
            assertEquals(list, Validate.noNullElements(list));

            Set<Integer> set = new HashSet<>(Arrays.asList(1, 2, 3));
            assertEquals(set, Validate.noNullElements(set));
        }

        @Test
        void noNullElementsIterable_EdgeCases_EmptyIterable() {
            List<String> emptyList = Collections.emptyList();
            assertEquals(emptyList, Validate.noNullElements(emptyList));
        }

        @Test
        void noNullElementsIterable_FailureScenarios_NullIterable() {
            assertThrows(NullPointerException.class, () -> Validate.noNullElements((Iterable<?>) null));
        }

        @Test
        void noNullElementsIterable_FailureScenarios_ContainsNull() {
            List<String> listWithNull = new ArrayList<>(Arrays.asList("a", null, "c"));
            assertThrowsIAE(() -> Validate.noNullElements(listWithNull)).execute();
        }

        @Test
        void noNullElementsIterableWithMessage_NormalBehavior() {
            List<String> list = Arrays.asList("a", "b");
            assertEquals(list, Validate.noNullElements(list, "Msg %s", "arg"));
        }

        @Test
        void noNullElementsIterableWithMessage_FailureScenarios_CustomMessage() {
            String message = "Iterable contains null at index %d";
            List<String> listWithNull = new ArrayList<>(Arrays.asList("a", null, "c"));
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.noNullElements(listWithNull, message, 1));
            assertEquals(String.format(message, 1), e.getMessage());
        }

        // Array overloads
        @Test
        void noNullElementsArray_NormalBehavior() {
            String[] array = {"a", "b", "c"};
            assertEquals(array, Validate.noNullElements(array));

            Integer[] intArray = {1, 2, 3};
            assertEquals(intArray, Validate.noNullElements(intArray));
        }

        @Test
        void noNullElementsArray_EdgeCases_EmptyArray() {
            String[] emptyArray = {};
            assertEquals(emptyArray, Validate.noNullElements(emptyArray));
        }

        @Test
        void noNullElementsArray_FailureScenarios_NullArray() {
            assertThrows(NullPointerException.class, () -> Validate.noNullElements((Object[]) null));
        }

        @Test
        void noNullElementsArray_FailureScenarios_ContainsNull() {
            String[] arrayWithNull = {"a", null, "c"};
            assertThrowsIAE(() -> Validate.noNullElements(arrayWithNull)).execute();
        }

        @Test
        void noNullElementsArrayWithMessage_NormalBehavior() {
            String[] array = {"a", "b"};
            assertEquals(array, Validate.noNullElements(array, "Msg %s", "arg"));
        }

        @Test
        void noNullElementsArrayWithMessage_FailureScenarios_CustomMessage() {
            String message = "Array contains null at index %d";
            String[] arrayWithNull = {"a", null, "c"};
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.noNullElements(arrayWithNull, message, 1));
            assertEquals(String.format(message, 1), e.getMessage());
        }
    }

    @Nested
    class NotBlankTests {

        @Test
        void notBlank_NormalBehavior() {
            assertEquals("hello", Validate.notBlank("hello"));
            assertEquals("  a  ", Validate.notBlank("  a  "));
            assertEquals("123", Validate.notBlank("123"));
        }

        @Test
        void notBlank_FailureScenarios_NullCharSequence() {
            assertThrowsIAE(() -> Validate.notBlank((String) null)).execute();
        }

        @Test
        void notBlank_FailureScenarios_EmptyCharSequence() {
            assertThrowsIAE(() -> Validate.notBlank("")).execute();
        }

        @Test
        void notBlank_FailureScenarios_BlankCharSequence() {
            assertThrowsIAE(() -> Validate.notBlank(" ")).execute();
            assertThrowsIAE(() -> Validate.notBlank("\t\n")).execute();
        }

        @Test
        void notBlankWithMessage_NormalBehavior() {
            assertEquals("hello", Validate.notBlank("hello", "Msg %s", "arg"));
        }

        @Test
        void notBlankWithMessage_FailureScenarios_CustomMessage() {
            String message = "Input '%s' cannot be blank";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.notBlank(" ", message, " "));
            assertEquals(String.format(message, " "), e.getMessage());
        }
    }

    @Nested
    class NotEmptyTests {

        // Collection overloads
        @Test
        void notEmptyCollection_NormalBehavior() {
            List<String> list = Arrays.asList("a", "b");
            assertEquals(list, Validate.notEmpty(list));
        }

        @Test
        void notEmptyCollection_FailureScenarios_NullCollection() {
            assertThrowsIAE(() -> Validate.notEmpty((Collection<?>) null)).execute();
        }

        @Test
        void notEmptyCollection_FailureScenarios_EmptyCollection() {
            assertThrowsIAE(() -> Validate.notEmpty(Collections.emptyList())).execute();
        }

        @Test
        void notEmptyCollectionWithMessage_NormalBehavior() {
            List<String> list = Arrays.asList("a", "b");
            assertEquals(list, Validate.notEmpty(list, "Msg %s", "arg"));
        }

        @Test
        void notEmptyCollectionWithMessage_FailureScenarios_CustomMessage() {
            String message = "Collection cannot be empty";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.notEmpty(Collections.emptySet(), message));
            assertEquals(message, e.getMessage());
        }

        // Map overloads
        @Test
        void notEmptyMap_NormalBehavior() {
            Map<String, String> map = new HashMap<>();
            map.put("key", "value");
            assertEquals(map, Validate.notEmpty(map));
        }

        @Test
        void notEmptyMap_FailureScenarios_NullMap() {
            assertThrowsIAE(() -> Validate.notEmpty((Map<?, ?>) null)).execute();
        }

        @Test
        void notEmptyMap_FailureScenarios_EmptyMap() {
            assertThrowsIAE(() -> Validate.notEmpty(Collections.emptyMap())).execute();
        }

        @Test
        void notEmptyMapWithMessage_NormalBehavior() {
            Map<String, String> map = new HashMap<>();
            map.put("key", "value");
            assertEquals(map, Validate.notEmpty(map, "Msg %s", "arg"));
        }

        @Test
        void notEmptyMapWithMessage_FailureScenarios_CustomMessage() {
            String message = "Map cannot be empty";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.notEmpty(Collections.emptyMap(), message));
            assertEquals(message, e.getMessage());
        }

        // CharSequence overloads
        @Test
        void notEmptyCharSequence_NormalBehavior() {
            assertEquals("hello", Validate.notEmpty("hello"));
        }

        @Test
        void notEmptyCharSequence_FailureScenarios_NullCharSequence() {
            assertThrowsIAE(() -> Validate.notEmpty((String) null)).execute();
        }

        @Test
        void notEmptyCharSequence_FailureScenarios_EmptyCharSequence() {
            assertThrowsIAE(() -> Validate.notEmpty("")).execute();
        }

        @Test
        void notEmptyCharSequenceWithMessage_NormalBehavior() {
            assertEquals("hello", Validate.notEmpty("hello", "Msg %s", "arg"));
        }

        @Test
        void notEmptyCharSequenceWithMessage_FailureScenarios_CustomMessage() {
            String message = "String cannot be empty";
            IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                    () -> Validate.notEmpty