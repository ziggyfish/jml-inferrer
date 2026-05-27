```java
package org.apache.commons.lang3.p3;

import org.apache.commons.lang3.Validate;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

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
import java.util.regex.PatternSyntaxException;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

public class ValidateTestP3P3 {

    private static final String DEFAULT_MESSAGE = "Validation failed";
    private static final String CUSTOM_MESSAGE = "Custom message: %s";
    private static final String CUSTOM_MESSAGE_FORMATTED = "Custom message: %d";

    // Helper to create a custom message supplier
    private Supplier<String> createMessageSupplier(String message) {
        return () -> message;
    }

    @Nested
    class ExclusiveBetweenTests {

        // double overloads
        @Test
        void exclusiveBetweenDouble_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0));
        }

        @Test
        void exclusiveBetweenDouble_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0, CUSTOM_MESSAGE, 5));
        }

        @Test
        void exclusiveBetweenDouble_valueEqualsStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 0.0));
        }

        @Test
        void exclusiveBetweenDouble_valueEqualsStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, 0.0, CUSTOM_MESSAGE, 0));
            assertEquals(String.format(CUSTOM_MESSAGE, 0), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenDouble_valueEqualsEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 10.0));
        }

        @Test
        void exclusiveBetweenDouble_valueEqualsEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, 10.0, CUSTOM_MESSAGE, 10));
            assertEquals(String.format(CUSTOM_MESSAGE, 10), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenDouble_valueLessThanStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, -1.0));
        }

        @Test
        void exclusiveBetweenDouble_valueLessThanStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, -1.0, CUSTOM_MESSAGE, -1));
            assertEquals(String.format(CUSTOM_MESSAGE, -1), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenDouble_valueGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 11.0));
        }

        @Test
        void exclusiveBetweenDouble_valueGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0.0, 10.0, 11.0, CUSTOM_MESSAGE, 11));
            assertEquals(String.format(CUSTOM_MESSAGE, 11), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenDouble_startGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10.0, 0.0, 5.0));
        }

        @Test
        void exclusiveBetweenDouble_startGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(10.0, 0.0, 5.0, CUSTOM_MESSAGE, 5));
            assertEquals(String.format(CUSTOM_MESSAGE, 5), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenDouble_startEqualsEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 5.0));
        }

        @Test
        void exclusiveBetweenDouble_startEqualsEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(5.0, 5.0, 5.0, CUSTOM_MESSAGE, 5));
            assertEquals(String.format(CUSTOM_MESSAGE, 5), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenDouble_NaNValues_throwsIAE() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Double.NaN, 10.0, 5.0));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, Double.NaN, 5.0));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, Double.NaN));
        }

        @Test
        void exclusiveBetweenDouble_InfinityValues_normalCase() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0));
        }

        @Test
        void exclusiveBetweenDouble_InfinityValues_edgeCase() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, 10.0, Double.NEGATIVE_INFINITY));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY));
        }


        // long overloads
        @Test
        void exclusiveBetweenLong_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L));
        }

        @Test
        void exclusiveBetweenLong_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L, CUSTOM_MESSAGE, 5L));
        }

        @Test
        void exclusiveBetweenLong_valueEqualsStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 0L));
        }

        @Test
        void exclusiveBetweenLong_valueEqualsStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0L, 10L, 0L, CUSTOM_MESSAGE, 0L));
            assertEquals(String.format(CUSTOM_MESSAGE, 0L), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenLong_valueEqualsEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 10L));
        }

        @Test
        void exclusiveBetweenLong_valueEqualsEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0L, 10L, 10L, CUSTOM_MESSAGE, 10L));
            assertEquals(String.format(CUSTOM_MESSAGE, 10L), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenLong_valueLessThanStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, -1L));
        }

        @Test
        void exclusiveBetweenLong_valueLessThanStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0L, 10L, -1L, CUSTOM_MESSAGE, -1L));
            assertEquals(String.format(CUSTOM_MESSAGE, -1L), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenLong_valueGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 11L));
        }

        @Test
        void exclusiveBetweenLong_valueGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0L, 10L, 11L, CUSTOM_MESSAGE, 11L));
            assertEquals(String.format(CUSTOM_MESSAGE, 11L), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenLong_startGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10L, 0L, 5L));
        }

        @Test
        void exclusiveBetweenLong_startGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(10L, 0L, 5L, CUSTOM_MESSAGE, 5L));
            assertEquals(String.format(CUSTOM_MESSAGE, 5L), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenLong_startEqualsEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 5L));
        }

        @Test
        void exclusiveBetweenLong_startEqualsEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(5L, 5L, 5L, CUSTOM_MESSAGE, 5L));
            assertEquals(String.format(CUSTOM_MESSAGE, 5L), thrown.getMessage());
        }

        // Generic overloads
        @Test
        void exclusiveBetweenGeneric_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0, 10, 5));
            assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "z", "m"));
        }

        @Test
        void exclusiveBetweenGeneric_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.exclusiveBetween(0, 10, 5, CUSTOM_MESSAGE, 5));
            assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "z", "m", CUSTOM_MESSAGE, "m"));
        }

        @Test
        void exclusiveBetweenGeneric_valueEqualsStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0, 10, 0));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "a"));
        }

        @Test
        void exclusiveBetweenGeneric_valueEqualsStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0, 10, 0, CUSTOM_MESSAGE, 0));
            assertEquals(String.format(CUSTOM_MESSAGE, 0), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenGeneric_valueEqualsEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0, 10, 10));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "z"));
        }

        @Test
        void exclusiveBetweenGeneric_valueEqualsEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0, 10, 10, CUSTOM_MESSAGE, 10));
            assertEquals(String.format(CUSTOM_MESSAGE, 10), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenGeneric_valueLessThanStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0, 10, -1));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("b", "z", "a"));
        }

        @Test
        void exclusiveBetweenGeneric_valueLessThanStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0, 10, -1, CUSTOM_MESSAGE, -1));
            assertEquals(String.format(CUSTOM_MESSAGE, -1), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenGeneric_valueGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0, 10, 11));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "y", "z"));
        }

        @Test
        void exclusiveBetweenGeneric_valueGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(0, 10, 11, CUSTOM_MESSAGE, 11));
            assertEquals(String.format(CUSTOM_MESSAGE, 11), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenGeneric_startGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10, 0, 5));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("z", "a", "m"));
        }

        @Test
        void exclusiveBetweenGeneric_startGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(10, 0, 5, CUSTOM_MESSAGE, 5));
            assertEquals(String.format(CUSTOM_MESSAGE, 5), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenGeneric_startEqualsEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5, 5, 5));
            assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "a", "a"));
        }

        @Test
        void exclusiveBetweenGeneric_startEqualsEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.exclusiveBetween(5, 5, 5, CUSTOM_MESSAGE, 5));
            assertEquals(String.format(CUSTOM_MESSAGE, 5), thrown.getMessage());
        }

        @Test
        void exclusiveBetweenGeneric_nullParameters_throwsNPE() {
            assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween(null, 10, 5));
            assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween(0, null, 5));
            assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween(0, 10, null));
        }
    }

    @Nested
    class FiniteTests {

        @Test
        void finite_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.finite(0.0));
            assertDoesNotThrow(() -> Validate.finite(1.0));
            assertDoesNotThrow(() -> Validate.finite(-1.0));
            assertDoesNotThrow(() -> Validate.finite(Double.MAX_VALUE));
            assertDoesNotThrow(() -> Validate.finite(Double.MIN_VALUE));
        }

        @Test
        void finite_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.finite(0.0, CUSTOM_MESSAGE, 0.0));
        }

        @Test
        void finite_NaN_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.NaN));
        }

        @Test
        void finite_NaN_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.finite(Double.NaN, CUSTOM_MESSAGE, "NaN"));
            assertEquals(String.format(CUSTOM_MESSAGE, "NaN"), thrown.getMessage());
        }

        @Test
        void finite_PositiveInfinity_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.POSITIVE_INFINITY));
        }

        @Test
        void finite_PositiveInfinity_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.finite(Double.POSITIVE_INFINITY, CUSTOM_MESSAGE, "Infinity"));
            assertEquals(String.format(CUSTOM_MESSAGE, "Infinity"), thrown.getMessage());
        }

        @Test
        void finite_NegativeInfinity_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.NEGATIVE_INFINITY));
        }

        @Test
        void finite_NegativeInfinity_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.finite(Double.NEGATIVE_INFINITY, CUSTOM_MESSAGE, "-Infinity"));
            assertEquals(String.format(CUSTOM_MESSAGE, "-Infinity"), thrown.getMessage());
        }
    }

    // getMessage is private, so we test it indirectly through other methods that use it.
    // For example, exclusiveBetween, finite, etc. already cover message formatting.

    @Nested
    class InclusiveBetweenTests {

        // double overloads
        @Test
        void inclusiveBetweenDouble_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0));
        }

        @Test
        void inclusiveBetweenDouble_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0, CUSTOM_MESSAGE, 5));
        }

        @Test
        void inclusiveBetweenDouble_valueEqualsStart_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 0.0));
        }

        @Test
        void inclusiveBetweenDouble_valueEqualsStart_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 0.0, CUSTOM_MESSAGE, 0));
        }

        @Test
        void inclusiveBetweenDouble_valueEqualsEnd_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 10.0));
        }

        @Test
        void inclusiveBetweenDouble_valueEqualsEnd_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 10.0, CUSTOM_MESSAGE, 10));
        }

        @Test
        void inclusiveBetweenDouble_valueLessThanStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, -1.0));
        }

        @Test
        void inclusiveBetweenDouble_valueLessThanStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0.0, 10.0, -1.0, CUSTOM_MESSAGE, -1));
            assertEquals(String.format(CUSTOM_MESSAGE, -1), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenDouble_valueGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, 11.0));
        }

        @Test
        void inclusiveBetweenDouble_valueGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0.0, 10.0, 11.0, CUSTOM_MESSAGE, 11));
            assertEquals(String.format(CUSTOM_MESSAGE, 11), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenDouble_startGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10.0, 0.0, 5.0));
        }

        @Test
        void inclusiveBetweenDouble_startGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(10.0, 0.0, 5.0, CUSTOM_MESSAGE, 5));
            assertEquals(String.format(CUSTOM_MESSAGE, 5), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenDouble_startEqualsEnd_valueEquals_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5.0, 5.0, 5.0));
        }

        @Test
        void inclusiveBetweenDouble_startEqualsEnd_valueEquals_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5.0, 5.0, 5.0, CUSTOM_MESSAGE, 5));
        }

        @Test
        void inclusiveBetweenDouble_startEqualsEnd_valueNotEquals_throwsIAE() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5.0, 5.0, 4.0));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5.0, 5.0, 6.0));
        }

        @Test
        void inclusiveBetweenDouble_NaNValues_throwsIAE() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(Double.NaN, 10.0, 5.0));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, Double.NaN, 5.0));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, Double.NaN));
        }

        @Test
        void inclusiveBetweenDouble_InfinityValues_normalCase() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0));
        }

        @Test
        void inclusiveBetweenDouble_InfinityValues_edgeCase() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, 10.0, Double.NEGATIVE_INFINITY));
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY));
        }

        // long overloads
        @Test
        void inclusiveBetweenLong_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L));
        }

        @Test
        void inclusiveBetweenLong_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L, CUSTOM_MESSAGE, 5L));
        }

        @Test
        void inclusiveBetweenLong_valueEqualsStart_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 0L));
        }

        @Test
        void inclusiveBetweenLong_valueEqualsStart_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 0L, CUSTOM_MESSAGE, 0L));
        }

        @Test
        void inclusiveBetweenLong_valueEqualsEnd_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 10L));
        }

        @Test
        void inclusiveBetweenLong_valueEqualsEnd_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 10L, CUSTOM_MESSAGE, 10L));
        }

        @Test
        void inclusiveBetweenLong_valueLessThanStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0L, 10L, -1L));
        }

        @Test
        void inclusiveBetweenLong_valueLessThanStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0L, 10L, -1L, CUSTOM_MESSAGE, -1L));
            assertEquals(String.format(CUSTOM_MESSAGE, -1L), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenLong_valueGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0L, 10L, 11L));
        }

        @Test
        void inclusiveBetweenLong_valueGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0L, 10L, 11L, CUSTOM_MESSAGE, 11L));
            assertEquals(String.format(CUSTOM_MESSAGE, 11L), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenLong_startGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10L, 0L, 5L));
        }

        @Test
        void inclusiveBetweenLong_startGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(10L, 0L, 5L, CUSTOM_MESSAGE, 5L));
            assertEquals(String.format(CUSTOM_MESSAGE, 5L), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenLong_startEqualsEnd_valueEquals_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5L, 5L, 5L));
        }

        @Test
        void inclusiveBetweenLong_startEqualsEnd_valueEquals_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5L, 5L, 5L, CUSTOM_MESSAGE, 5L));
        }

        @Test
        void inclusiveBetweenLong_startEqualsEnd_valueNotEquals_throwsIAE() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5L, 5L, 4L));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5L, 5L, 6L));
        }

        // Generic overloads
        @Test
        void inclusiveBetweenGeneric_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0, 10, 5));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "m"));
        }

        @Test
        void inclusiveBetweenGeneric_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0, 10, 5, CUSTOM_MESSAGE, 5));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "m", CUSTOM_MESSAGE, "m"));
        }

        @Test
        void inclusiveBetweenGeneric_valueEqualsStart_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0, 10, 0));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "a"));
        }

        @Test
        void inclusiveBetweenGeneric_valueEqualsStart_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0, 10, 0, CUSTOM_MESSAGE, 0));
        }

        @Test
        void inclusiveBetweenGeneric_valueEqualsEnd_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0, 10, 10));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "z"));
        }

        @Test
        void inclusiveBetweenGeneric_valueEqualsEnd_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(0, 10, 10, CUSTOM_MESSAGE, 10));
        }

        @Test
        void inclusiveBetweenGeneric_valueLessThanStart_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0, 10, -1));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("b", "z", "a"));
        }

        @Test
        void inclusiveBetweenGeneric_valueLessThanStart_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0, 10, -1, CUSTOM_MESSAGE, -1));
            assertEquals(String.format(CUSTOM_MESSAGE, -1), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenGeneric_valueGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0, 10, 11));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("a", "y", "z"));
        }

        @Test
        void inclusiveBetweenGeneric_valueGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(0, 10, 11, CUSTOM_MESSAGE, 11));
            assertEquals(String.format(CUSTOM_MESSAGE, 11), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenGeneric_startGreaterThanEnd_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10, 0, 5));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("z", "a", "m"));
        }

        @Test
        void inclusiveBetweenGeneric_startGreaterThanEnd_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.inclusiveBetween(10, 0, 5, CUSTOM_MESSAGE, 5));
            assertEquals(String.format(CUSTOM_MESSAGE, 5), thrown.getMessage());
        }

        @Test
        void inclusiveBetweenGeneric_startEqualsEnd_valueEquals_noMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5, 5, 5));
            assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "a", "a"));
        }

        @Test
        void inclusiveBetweenGeneric_startEqualsEnd_valueEquals_withMessage() {
            assertDoesNotThrow(() -> Validate.inclusiveBetween(5, 5, 5, CUSTOM_MESSAGE, 5));
        }

        @Test
        void inclusiveBetweenGeneric_startEqualsEnd_valueNotEquals_throwsIAE() {
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5, 5, 4));
            assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5, 5, 6));
        }

        @Test
        void inclusiveBetweenGeneric_nullParameters_throwsNPE() {
            assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween(null, 10, 5));
            assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween(0, null, 5));
            assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween(0, 10, null));
        }
    }

    @Nested
    class IsAssignableFromTests {

        @Test
        void isAssignableFrom_normalCase_noMessage() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Number.class, Integer.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, String.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(List.class, ArrayList.class));
            assertDoesNotThrow(() -> Validate.isAssignableFrom(int.class, int.class)); // Primitive types
        }

        @Test
        void isAssignableFrom_normalCase_withMessage() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(Number.class, Integer.class, CUSTOM_MESSAGE, "Integer"));
        }

        @Test
        void isAssignableFrom_sameClass_noMessage() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(String.class, String.class));
        }

        @Test
        void isAssignableFrom_sameClass_withMessage() {
            assertDoesNotThrow(() -> Validate.isAssignableFrom(String.class, String.class, CUSTOM_MESSAGE, "String"));
        }

        @Test
        void isAssignableFrom_notAssignable_throwsIAE_noMessage() {
            assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(Integer.class, Number.class));
            assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(String.class, Object.class));
            assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(ArrayList.class, List.class));
        }

        @Test
        void isAssignableFrom_notAssignable_throwsIAE_withMessage() {
            IllegalArgumentException thrown = assertThrows(IllegalArgumentException.class,
                    () -> Validate.isAssignableFrom(Integer.class, Number.class, CUSTOM_MESSAGE, "Number"));
            assertEquals(String.format(CUSTOM_MESSAGE, "Number"), thrown.getMessage());
        }