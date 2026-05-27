```java
package org.apache.commons.lang3.p3;

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

public class ValidateTestP3P3 {

    // Helper for custom messages
    private static final String CUSTOM_MESSAGE = "Custom message: %s";
    private static final String CUSTOM_MESSAGE_FORMAT = "Custom message: %s, %d";
    private static final String DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE = "The value %s is not exclusively between the start %s and end %s.";
    private static final String DEFAULT_FINITE_MESSAGE = "The value is not finite: %s";
    private static final String DEFAULT_INCLUSIVE_BETWEEN_MESSAGE = "The value %s is not inclusively between the start %s and end %s.";
    private static final String DEFAULT_IS_ASSIGNABLE_FROM_MESSAGE = "Cannot assign a %s to a %s";
    private static final String DEFAULT_IS_INSTANCE_OF_MESSAGE = "Expected type %s, actual type %s";
    private static final String DEFAULT_IS_TRUE_MESSAGE = "The validated expression is false";
    private static final String DEFAULT_MATCHES_PATTERN_MESSAGE = "The string %s does not match the pattern %s";
    private static final String DEFAULT_NO_NULL_ELEMENTS_MESSAGE = "The validated collection contains null element at index %d";
    private static final String DEFAULT_NOT_BLANK_MESSAGE = "The validated character sequence is blank";
    private static final String DEFAULT_NOT_EMPTY_MESSAGE = "The validated object is empty";
    private static final String DEFAULT_NOT_NAN_MESSAGE = "The validated value is not a number";
    private static final String DEFAULT_NOT_NULL_MESSAGE = "The validated object is null";
    private static final String DEFAULT_VALID_INDEX_MESSAGE = "The validated index is invalid: %d";
    private static final String DEFAULT_VALID_STATE_MESSAGE = "The validated state is false";


    @Nested
    class ExclusiveBetweenTests {

        @Nested
        class DoubleExclusiveBetweenTests {
            @Test
            void testExclusiveBetweenDouble_NormalBehavior_ValueBetween() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0));
            }

            @Test
            void testExclusiveBetweenDouble_NormalBehavior_ValueBetweenWithMessage() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0, CUSTOM_MESSAGE, "test"));
            }

            @Test
            void testExclusiveBetweenDouble_EdgeCase_ValueEqualsStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, 0.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 0.0, 0.0, 10.0), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_EdgeCase_ValueEqualsEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, 10.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 10.0, 0.0, 10.0), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_EdgeCase_ValueEqualsStartWithMessage() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, 0.0, CUSTOM_MESSAGE, "start"));
                assertEquals(String.format(CUSTOM_MESSAGE, "start"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_EdgeCase_ValueEqualsEndWithMessage() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, 10.0, CUSTOM_MESSAGE, "end"));
                assertEquals(String.format(CUSTOM_MESSAGE, "end"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_FailureScenario_ValueLessThanStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, -1.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, -1.0, 0.0, 10.0), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_FailureScenario_ValueGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, 11.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 11.0, 0.0, 10.0), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_FailureScenario_StartGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(10.0, 0.0, 5.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 5.0, 10.0, 0.0), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_FailureScenario_StartEqualsEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(5.0, 5.0, 5.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 5.0, 5.0, 5.0), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_FailureScenario_NaNValues() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, Double.NaN));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, Double.NaN, 0.0, 10.0), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(Double.NaN, 10.0, 5.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 5.0, Double.NaN, 10.0), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, Double.NaN, 5.0));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 5.0, 0.0, Double.NaN), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenDouble_FailureScenario_InfinityValues() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0));

                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, Double.POSITIVE_INFINITY));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, Double.POSITIVE_INFINITY, 0.0, 10.0), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0.0, 10.0, Double.NEGATIVE_INFINITY));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, Double.NEGATIVE_INFINITY, 0.0, 10.0), thrown.getMessage());
            }
        }

        @Nested
        class LongExclusiveBetweenTests {
            @Test
            void testExclusiveBetweenLong_NormalBehavior_ValueBetween() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L));
            }

            @Test
            void testExclusiveBetweenLong_NormalBehavior_ValueBetweenWithMessage() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L, CUSTOM_MESSAGE, "test"));
            }

            @Test
            void testExclusiveBetweenLong_EdgeCase_ValueEqualsStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0L, 10L, 0L));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 0L, 0L, 10L), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_EdgeCase_ValueEqualsEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0L, 10L, 10L));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 10L, 0L, 10L), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_EdgeCase_ValueEqualsStartWithMessage() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0L, 10L, 0L, CUSTOM_MESSAGE, "start"));
                assertEquals(String.format(CUSTOM_MESSAGE, "start"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_EdgeCase_ValueEqualsEndWithMessage() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0L, 10L, 10L, CUSTOM_MESSAGE, "end"));
                assertEquals(String.format(CUSTOM_MESSAGE, "end"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_FailureScenario_ValueLessThanStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0L, 10L, -1L));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, -1L, 0L, 10L), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_FailureScenario_ValueGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(0L, 10L, 11L));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 11L, 0L, 10L), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_FailureScenario_StartGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(10L, 0L, 5L));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 5L, 10L, 0L), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_FailureScenario_StartEqualsEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(5L, 5L, 5L));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, 5L, 5L, 5L), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenLong_EdgeCase_MinMaxLongValues() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, 0L));

                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, Long.MIN_VALUE, Long.MIN_VALUE, Long.MAX_VALUE), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MAX_VALUE));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, Long.MAX_VALUE, Long.MIN_VALUE, Long.MAX_VALUE), thrown.getMessage());
            }
        }

        @Nested
        class ComparableExclusiveBetweenTests {
            @Test
            void testExclusiveBetweenComparable_NormalBehavior_ValueBetween() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "c", "b"));
            }

            @Test
            void testExclusiveBetweenComparable_NormalBehavior_ValueBetweenWithMessage() {
                assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "c", "b", CUSTOM_MESSAGE, "test"));
            }

            @Test
            void testExclusiveBetweenComparable_EdgeCase_ValueEqualsStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("a", "c", "a"));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, "a", "a", "c"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_EdgeCase_ValueEqualsEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("a", "c", "c"));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, "c", "a", "c"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_EdgeCase_ValueEqualsStartWithMessage() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("a", "c", "a", CUSTOM_MESSAGE, "start"));
                assertEquals(String.format(CUSTOM_MESSAGE, "start"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_EdgeCase_ValueEqualsEndWithMessage() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("a", "c", "c", CUSTOM_MESSAGE, "end"));
                assertEquals(String.format(CUSTOM_MESSAGE, "end"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_ValueLessThanStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("b", "d", "a"));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, "a", "b", "d"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_ValueGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("a", "c", "d"));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, "d", "a", "c"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_StartGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("c", "a", "b"));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, "b", "c", "a"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_StartEqualsEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.exclusiveBetween("b", "b", "b"));
                assertEquals(String.format(DEFAULT_EXCLUSIVE_BETWEEN_MESSAGE, "b", "b", "b"), thrown.getMessage());
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_NullStart() {
                assertThrows(NullPointerException.class, () ->
                        Validate.exclusiveBetween(null, "c", "b"));
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_NullEnd() {
                assertThrows(NullPointerException.class, () ->
                        Validate.exclusiveBetween("a", null, "b"));
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_NullValue() {
                assertThrows(NullPointerException.class, () ->
                        Validate.exclusiveBetween("a", "c", null));
            }

            @Test
            void testExclusiveBetweenComparable_FailureScenario_NullStartWithMessage() {
                assertThrows(NullPointerException.class, () ->
                        Validate.exclusiveBetween(null, "c", "b", CUSTOM_MESSAGE, "start"));
            }
        }
    }

    @Nested
    class FiniteTests {
        @Test
        void testFinite_NormalBehavior_FiniteValue() {
            assertDoesNotThrow(() -> Validate.finite(0.0));
            assertDoesNotThrow(() -> Validate.finite(123.45));
            assertDoesNotThrow(() -> Validate.finite(-123.45));
            assertDoesNotThrow(() -> Validate.finite(Double.MAX_VALUE));
            assertDoesNotThrow(() -> Validate.finite(Double.MIN_VALUE));
        }

        @Test
        void testFinite_NormalBehavior_FiniteValueWithMessage() {
            assertDoesNotThrow(() -> Validate.finite(0.0, CUSTOM_MESSAGE, "test"));
        }

        @Test
        void testFinite_FailureScenario_PositiveInfinity() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.finite(Double.POSITIVE_INFINITY));
            assertEquals(String.format(DEFAULT_FINITE_MESSAGE, Double.POSITIVE_INFINITY), thrown.getMessage());
        }

        @Test
        void testFinite_FailureScenario_NegativeInfinity() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.finite(Double.NEGATIVE_INFINITY));
            assertEquals(String.format(DEFAULT_FINITE_MESSAGE, Double.NEGATIVE_INFINITY), thrown.getMessage());
        }

        @Test
        void testFinite_FailureScenario_NaN() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.finite(Double.NaN));
            assertEquals(String.format(DEFAULT_FINITE_MESSAGE, Double.NaN), thrown.getMessage());
        }

        @Test
        void testFinite_FailureScenario_PositiveInfinityWithMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.finite(Double.POSITIVE_INFINITY, CUSTOM_MESSAGE, "infinity"));
            assertEquals(String.format(CUSTOM_MESSAGE, "infinity"), thrown.getMessage());
        }

        @Test
        void testFinite_FailureScenario_NaNWithMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.finite(Double.NaN, CUSTOM_MESSAGE, "NaN"));
            assertEquals(String.format(CUSTOM_MESSAGE, "NaN"), thrown.getMessage());
        }
    }

    // getMessage is private, so it's tested implicitly through other methods that use it.

    @Nested
    class InclusiveBetweenTests {

        @Nested
        class DoubleInclusiveBetweenTests {
            @Test
            void testInclusiveBetweenDouble_NormalBehavior_ValueBetween() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0));
            }

            @Test
            void testInclusiveBetweenDouble_NormalBehavior_ValueEqualsStart() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 0.0));
            }

            @Test
            void testInclusiveBetweenDouble_NormalBehavior_ValueEqualsEnd() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 10.0));
            }

            @Test
            void testInclusiveBetweenDouble_NormalBehavior_ValueBetweenWithMessage() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0, CUSTOM_MESSAGE, "test"));
            }

            @Test
            void testInclusiveBetweenDouble_FailureScenario_ValueLessThanStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0.0, 10.0, -1.0));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, -1.0, 0.0, 10.0), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenDouble_FailureScenario_ValueGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0.0, 10.0, 11.0));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 11.0, 0.0, 10.0), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenDouble_FailureScenario_StartGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(10.0, 0.0, 5.0));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 5.0, 10.0, 0.0), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenDouble_EdgeCase_StartEqualsEnd_ValueEquals() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(5.0, 5.0, 5.0));
            }

            @Test
            void testInclusiveBetweenDouble_EdgeCase_StartEqualsEnd_ValueNotEquals() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(5.0, 5.0, 4.0));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 4.0, 5.0, 5.0), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenDouble_FailureScenario_NaNValues() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0.0, 10.0, Double.NaN));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, Double.NaN, 0.0, 10.0), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(Double.NaN, 10.0, 5.0));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 5.0, Double.NaN, 10.0), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0.0, Double.NaN, 5.0));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 5.0, 0.0, Double.NaN), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenDouble_FailureScenario_InfinityValues() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0));
                assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY));
                assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY));

                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0.0, 10.0, Double.POSITIVE_INFINITY));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, Double.POSITIVE_INFINITY, 0.0, 10.0), thrown.getMessage());

                thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0.0, 10.0, Double.NEGATIVE_INFINITY));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, Double.NEGATIVE_INFINITY, 0.0, 10.0), thrown.getMessage());
            }
        }

        @Nested
        class LongInclusiveBetweenTests {
            @Test
            void testInclusiveBetweenLong_NormalBehavior_ValueBetween() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L));
            }

            @Test
            void testInclusiveBetweenLong_NormalBehavior_ValueEqualsStart() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 0L));
            }

            @Test
            void testInclusiveBetweenLong_NormalBehavior_ValueEqualsEnd() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 10L));
            }

            @Test
            void testInclusiveBetweenLong_NormalBehavior_ValueBetweenWithMessage() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L, CUSTOM_MESSAGE, "test"));
            }

            @Test
            void testInclusiveBetweenLong_FailureScenario_ValueLessThanStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0L, 10L, -1L));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, -1L, 0L, 10L), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenLong_FailureScenario_ValueGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(0L, 10L, 11L));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 11L, 0L, 10L), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenLong_FailureScenario_StartGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(10L, 0L, 5L));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 5L, 10L, 0L), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenLong_EdgeCase_StartEqualsEnd_ValueEquals() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(5L, 5L, 5L));
            }

            @Test
            void testInclusiveBetweenLong_EdgeCase_StartEqualsEnd_ValueNotEquals() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween(5L, 5L, 4L));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, 4L, 5L, 5L), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenLong_EdgeCase_MinMaxLongValues() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, 0L));
                assertDoesNotThrow(() -> Validate.inclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE));
                assertDoesNotThrow(() -> Validate.inclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MAX_VALUE));
            }
        }

        @Nested
        class ComparableInclusiveBetweenTests {
            @Test
            void testInclusiveBetweenComparable_NormalBehavior_ValueBetween() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "c", "b"));
            }

            @Test
            void testInclusiveBetweenComparable_NormalBehavior_ValueEqualsStart() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "c", "a"));
            }

            @Test
            void testInclusiveBetweenComparable_NormalBehavior_ValueEqualsEnd() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "c", "c"));
            }

            @Test
            void testInclusiveBetweenComparable_NormalBehavior_ValueBetweenWithMessage() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "c", "b", CUSTOM_MESSAGE, "test"));
            }

            @Test
            void testInclusiveBetweenComparable_FailureScenario_ValueLessThanStart() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween("b", "d", "a"));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, "a", "b", "d"), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenComparable_FailureScenario_ValueGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween("a", "c", "d"));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, "d", "a", "c"), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenComparable_FailureScenario_StartGreaterThanEnd() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween("c", "a", "b"));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, "b", "c", "a"), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenComparable_EdgeCase_StartEqualsEnd_ValueEquals() {
                assertDoesNotThrow(() -> Validate.inclusiveBetween("b", "b", "b"));
            }

            @Test
            void testInclusiveBetweenComparable_EdgeCase_StartEqualsEnd_ValueNotEquals() {
                IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                        Validate.inclusiveBetween("b", "b", "a"));
                assertEquals(String.format(DEFAULT_INCLUSIVE_BETWEEN_MESSAGE, "a", "b", "b"), thrown.getMessage());
            }

            @Test
            void testInclusiveBetweenComparable_FailureScenario_NullStart() {
                assertThrows(NullPointerException.class, () ->
                        Validate.inclusiveBetween(null, "c", "b"));
            }

            @Test
            void testInclusiveBetweenComparable_FailureScenario_NullEnd() {
                assertThrows(NullPointerException.class, () ->
                        Validate.inclusiveBetween("a", null, "b"));
            }

            @Test
            void testInclusiveBetweenComparable_FailureScenario_NullValue() {
                assertThrows(NullPointerException.class, () ->
                        Validate.inclusiveBetween("a", "c", null));
            }
        }
    }

    @Nested
    class IsAssignableFromTests {
        @Test
        void testIsAssignableFrom_NormalBehavior_Assignable() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, String.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(List.class, ArrayList.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Number.class, Integer.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Runnable.class, Thread.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, Object.class));
        }

        @Test
        void testIsAssignableFrom_NormalBehavior_AssignableWithMessage() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, String.class, CUSTOM_MESSAGE, "test"));
        }

        @Test
        void testIsAssignableFrom_FailureScenario_NotAssignableFrom() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.isAssignableFrom(String.class, Object.class));
            assertEquals(String.format(DEFAULT_IS_ASSIGNABLE_FROM_MESSAGE, Object.class.getName(), String.class.getName()), thrown.getMessage());
        }

        @Test
        void testIsAssignableFrom_FailureScenario_NotAssignableFromWithMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.isAssignableFrom(String.class, Object.class, CUSTOM_MESSAGE, "type mismatch"));
            assertEquals(String.format(CUSTOM_MESSAGE, "type mismatch"), thrown.getMessage());
        }

        @Test
        void testIsAssignableFrom_FailureScenario_NullSuperType() {
            assertThrows(NullPointerException.class, () ->
                    Validate.isAssignableFrom(null, String.class));
        }

        @Test
        void testIsAssignableFrom_FailureScenario_NullType() {
            assertThrows(NullPointerException.class, () ->
                    Validate.isAssignableFrom(Object.class, null));
        }

        @Test
        void testIsAssignableFrom_FailureScenario_NullSuperTypeWithMessage() {
            assertThrows(NullPointerException.class, () ->
                    Validate.isAssignableFrom(null, String.class, CUSTOM_MESSAGE, "null super"));
        }
    }

    @Nested
    class IsInstanceOfTests {
        @Test
        void testIsInstanceOf_NormalBehavior_IsInstance() {
            assertDoesNotThrow(() -> Validate.isInstanceOf(String.class, "hello"));
            assertDoesNotThrow(() -> Validate.isInstanceOf(Object.class, 123));
            assertDoesNotThrow(() -> Validate.isInstanceOf(List.class, new ArrayList<>()));
        }

        @Test
        void testIsInstanceOf_NormalBehavior_IsInstanceWithMessage() {
            assertDoesNotThrow(() -> Validate.isInstanceOf(String.class, "hello", CUSTOM_MESSAGE, "test"));
        }

        @Test
        void testIsInstanceOf_FailureScenario_NotInstanceOf() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.isInstanceOf(Integer.class, "hello"));
            assertEquals(String.format(DEFAULT_IS_INSTANCE_OF_MESSAGE, Integer.class.getName(), String.class.getName()), thrown.getMessage());
        }

        @Test
        void testIsInstanceOf_FailureScenario_NotInstanceOfWithMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.isInstanceOf(Integer.class, "hello", CUSTOM_MESSAGE, "type mismatch"));
            assertEquals(String.format(CUSTOM_MESSAGE, "type mismatch"), thrown.getMessage());
        }

        @Test
        void testIsInstanceOf_FailureScenario_NullType() {
            assertThrows(NullPointerException.class, () ->
                    Validate.isInstanceOf(null, "hello"));
        }

        @Test
        void testIsInstanceOf_FailureScenario_NullObject() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class, () ->
                    Validate.isInstanceOf(String.class, null));
            assertEquals(String.format(DEFAULT_IS_INSTANCE_OF_MESSAGE, String.class