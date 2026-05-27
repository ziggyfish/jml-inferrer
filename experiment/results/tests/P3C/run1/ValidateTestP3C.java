```java
package org.apache.commons.lang3.p3c;

import org.apache.commons.lang3.Validate;
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
import java.util.regex.PatternSyntaxException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ValidateTestP3CP3C {

    // --- exclusiveBetween (double) ---
    @Test
    void testExclusiveBetweenDouble_NormalValid() {
        assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, 10.0, 5.0));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(-10.0, 0.0, -5.0));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(-10.0, 10.0, 0.0));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(Double.MIN_VALUE, Double.MAX_VALUE, 1.0));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(Double.MIN_VALUE, Double.MAX_VALUE, -1.0));
    }

    @Test
    void testExclusiveBetweenDouble_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 0.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 10.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, -1.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 11.0));
    }

    @Test
    void testExclusiveBetweenDouble_EdgeCases() {
        // Start == End (invalid range)
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 4.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 6.0));

        // NaN values
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Double.NaN, 10.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, Double.NaN, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, Double.NaN));

        // Infinity values
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, 10.0, Double.NEGATIVE_INFINITY));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, 0.0, -100.0));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(0.0, Double.POSITIVE_INFINITY, 100.0));
    }

    @Test
    void testExclusiveBetweenDoubleWithMessage_NormalInvalid() {
        String message = "Value %s is not exclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.exclusiveBetween(0.0, 10.0, 0.0, message, 0.0, 0.0, 10.0));
        assertEquals("Value 0.0 is not exclusively between 0.0 and 10.0", e.getMessage());
    }

    // --- exclusiveBetween (long) ---
    @Test
    void testExclusiveBetweenLong_NormalValid() {
        assertDoesNotThrow(() -> Validate.exclusiveBetween(0L, 10L, 5L));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(-10L, 0L, -5L));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(-10L, 10L, 0L));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, 0L));
    }

    @Test
    void testExclusiveBetweenLong_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 0L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 10L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, -1L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 11L));
    }

    @Test
    void testExclusiveBetweenLong_EdgeCases() {
        // Start == End (invalid range)
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 5L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 4L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 6L));

        // Max/Min values
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MAX_VALUE));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, 0L));
    }

    @Test
    void testExclusiveBetweenLongWithMessage_NormalInvalid() {
        String message = "Value %d is not exclusively between %d and %d";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.exclusiveBetween(0L, 10L, 0L, message, 0L, 0L, 10L));
        assertEquals("Value 0 is not exclusively between 0 and 10", e.getMessage());
    }

    // --- exclusiveBetween (T extends Comparable) ---
    @Test
    void testExclusiveBetweenComparable_NormalValid() {
        assertDoesNotThrow(() -> Validate.exclusiveBetween("a", "z", "m"));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(1, 10, 5));
        assertDoesNotThrow(() -> Validate.exclusiveBetween(new Integer(1), new Integer(10), new Integer(5)));
    }

    @Test
    void testExclusiveBetweenComparable_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "a"));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "z"));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "0")); // Before 'a'
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "{")); // After 'z'
    }

    @Test
    void testExclusiveBetweenComparable_EdgeCases() {
        // Start == End (invalid range)
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "a", "a"));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "a", "b"));

        // Null values
        assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween(null, "z", "m"));
        assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween("a", null, "m"));
        assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween("a", "z", null));
    }

    @Test
    void testExclusiveBetweenComparableWithMessage_NormalInvalid() {
        String message = "Value %s is not exclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.exclusiveBetween("a", "z", "a", message, "a", "a", "z"));
        assertEquals("Value a is not exclusively between a and z", e.getMessage());
    }

    // --- finite (double) ---
    @Test
    void testFiniteDouble_NormalValid() {
        assertDoesNotThrow(() -> Validate.finite(0.0));
        assertDoesNotThrow(() -> Validate.finite(1.0));
        assertDoesNotThrow(() -> Validate.finite(-1.0));
        assertDoesNotThrow(() -> Validate.finite(Double.MAX_VALUE));
        assertDoesNotThrow(() -> Validate.finite(Double.MIN_VALUE));
    }

    @Test
    void testFiniteDouble_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.NaN));
        assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.POSITIVE_INFINITY));
        assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.NEGATIVE_INFINITY));
    }

    @Test
    void testFiniteDoubleWithMessage_NormalInvalid() {
        String message = "Value %s is not finite";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.finite(Double.NaN, message, Double.NaN));
        assertEquals("Value NaN is not finite", e.getMessage());
    }

    // --- getMessage (private, but indirectly testable) ---
    // This method is private, so we can only test its behavior indirectly through public methods that use it.
    // The tests for methods with messages already cover this.

    // --- inclusiveBetween (double) ---
    @Test
    void testInclusiveBetweenDouble_NormalValid() {
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 5.0));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 0.0));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, 10.0, 10.0));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(-10.0, 0.0, -5.0));
    }

    @Test
    void testInclusiveBetweenDouble_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, -1.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, 11.0));
    }

    @Test
    void testInclusiveBetweenDouble_EdgeCases() {
        // Start == End (valid)
        assertDoesNotThrow(() -> Validate.inclusiveBetween(5.0, 5.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5.0, 5.0, 4.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5.0, 5.0, 6.0));

        // NaN values
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(Double.NaN, 10.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, Double.NaN, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, Double.NaN));

        // Infinity values
        assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, 10.0, Double.NEGATIVE_INFINITY));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0.0, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0));
    }

    @Test
    void testInclusiveBetweenDoubleWithMessage_NormalInvalid() {
        String message = "Value %s is not inclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.inclusiveBetween(0.0, 10.0, -1.0, message, -1.0, 0.0, 10.0));
        assertEquals("Value -1.0 is not inclusively between 0.0 and 10.0", e.getMessage());
    }

    // --- inclusiveBetween (long) ---
    @Test
    void testInclusiveBetweenLong_NormalValid() {
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 5L));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 0L));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(0L, 10L, 10L));
    }

    @Test
    void testInclusiveBetweenLong_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0L, 10L, -1L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0L, 10L, 11L));
    }

    @Test
    void testInclusiveBetweenLong_EdgeCases() {
        // Start == End (valid)
        assertDoesNotThrow(() -> Validate.inclusiveBetween(5L, 5L, 5L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5L, 5L, 4L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5L, 5L, 6L));

        // Max/Min values
        assertDoesNotThrow(() -> Validate.inclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, Long.MAX_VALUE));
        assertDoesNotThrow(() -> Validate.inclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, 0L));
    }

    @Test
    void testInclusiveBetweenLongWithMessage_NormalInvalid() {
        String message = "Value %d is not inclusively between %d and %d";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.inclusiveBetween(0L, 10L, -1L, message, -1L, 0L, 10L));
        assertEquals("Value -1 is not inclusively between 0 and 10", e.getMessage());
    }

    // --- inclusiveBetween (T extends Comparable) ---
    @Test
    void testInclusiveBetweenComparable_NormalValid() {
        assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "m"));
        assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "a"));
        assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "z", "z"));
    }

    @Test
    void testInclusiveBetweenComparable_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("a", "z", "0")); // Before 'a'
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("a", "z", "{")); // After 'z'
    }

    @Test
    void testInclusiveBetweenComparable_EdgeCases() {
        // Start == End (valid)
        assertDoesNotThrow(() -> Validate.inclusiveBetween("a", "a", "a"));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("a", "a", "b"));

        // Null values
        assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween(null, "z", "m"));
        assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween("a", null, "m"));
        assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween("a", "z", null));
    }

    @Test
    void testInclusiveBetweenComparableWithMessage_NormalInvalid() {
        String message = "Value %s is not inclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.inclusiveBetween("a", "z", "0", message, "0", "a", "z"));
        assertEquals("Value 0 is not inclusively between a and z", e.getMessage());
    }

    // --- isAssignableFrom ---
    @Test
    void testIsAssignableFrom_NormalValid() {
        assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, String.class));
        assertDoesNotThrow(() -> Validate.isAssignableFrom(List.class, ArrayList.class));
        assertDoesNotThrow(() -> Validate.isAssignableFrom(Number.class, Integer.class));
        assertDoesNotThrow(() -> Validate.isAssignableFrom(Object.class, Object.class));
        assertDoesNotThrow(() -> Validate.isAssignableFrom(String.class, String.class));
    }

    @Test
    void testIsAssignableFrom_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(String.class, Object.class));
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(ArrayList.class, List.class));
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(Integer.class, Number.class));
    }

    @Test
    void testIsAssignableFrom_EdgeCases() {
        // Null values
        assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(null, String.class));
        assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(Object.class, null));
        assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(null, null));

        // Primitive types vs Wrapper types
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(int.class, Integer.class));
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(Integer.class, int.class));
        assertDoesNotThrow(() -> Validate.isAssignableFrom(int.class, int.class));
        assertDoesNotThrow(() -> Validate.isAssignableFrom(Integer.class, Integer.class));
    }

    @Test
    void testIsAssignableFromWithMessage_NormalInvalid() {
        String message = "%s is not assignable from %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isAssignableFrom(String.class, Object.class, message, String.class, Object.class));
        assertEquals("class java.lang.String is not assignable from class java.lang.Object", e.getMessage());
    }

    // --- isInstanceOf ---
    @Test
    void testIsInstanceOf_NormalValid() {
        assertDoesNotThrow(() -> Validate.isInstanceOf(String.class, "hello"));
        assertDoesNotThrow(() -> Validate.isInstanceOf(Object.class, "hello"));
        assertDoesNotThrow(() -> Validate.isInstanceOf(List.class, new ArrayList<>()));
        assertDoesNotThrow(() -> Validate.isInstanceOf(Integer.class, 10));
    }

    @Test
    void testIsInstanceOf_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(Integer.class, "hello"));
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(String.class, 10));
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(ArrayList.class, new HashSet<>()));
    }

    @Test
    void testIsInstanceOf_EdgeCases() {
        // Null values
        assertThrows(NullPointerException.class, () -> Validate.isInstanceOf(null, "hello"));
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(String.class, null)); // null is not an instance of String
        assertThrows(NullPointerException.class, () -> Validate.isInstanceOf(null, null));

        // Primitive types vs Wrapper types
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(int.class, 10)); // int.class is not assignable from Integer
        assertDoesNotThrow(() -> Validate.isInstanceOf(Integer.class, 10));
    }

    @Test
    void testIsInstanceOfWithMessage_NormalInvalid() {
        String message = "%s is not an instance of %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isInstanceOf(Integer.class, "hello", message, "hello", Integer.class));
        assertEquals("hello is not an instance of class java.lang.Integer", e.getMessage());
    }

    // --- isTrue (boolean) ---
    @Test
    void testIsTrueBoolean_NormalValid() {
        assertDoesNotThrow(() -> Validate.isTrue(true));
    }

    @Test
    void testIsTrueBoolean_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isTrue(false));
    }

    @Test
    void testIsTrueBooleanWithMessageDouble_NormalInvalid() {
        String message = "Expression is false, value: %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, message, 123.45));
        assertEquals("Expression is false, value: 123.45", e.getMessage());
    }

    @Test
    void testIsTrueBooleanWithMessageLong_NormalInvalid() {
        String message = "Expression is false, value: %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, message, 123L));
        assertEquals("Expression is false, value: 123", e.getMessage());
    }

    @Test
    void testIsTrueBooleanWithMessageObject_NormalInvalid() {
        String message = "Expression is false, values: %s, %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, message, "a", 1));
        assertEquals("Expression is false, values: a, 1", e.getMessage());
    }

    @Test
    void testIsTrueBooleanWithMessageSupplier_NormalInvalid() {
        Supplier<String> messageSupplier = () -> "Supplier message";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, messageSupplier));
        assertEquals("Supplier message", e.getMessage());
    }

    @Test
    void testIsTrueBooleanWithMessageSupplier_SupplierNotCalledOnValid() {
        final boolean[] supplierCalled = {false};
        Supplier<String> messageSupplier = () -> {
            supplierCalled[0] = true;
            return "Supplier message";
        };
        assertDoesNotThrow(() -> Validate.isTrue(true, messageSupplier));
        assertTrue(!supplierCalled[0], "Supplier should not be called if expression is true");
    }

    // --- matchesPattern ---
    @Test
    void testMatchesPattern_NormalValid() {
        assertDoesNotThrow(() -> Validate.matchesPattern("hello", "h.*o"));
        assertDoesNotThrow(() -> Validate.matchesPattern("12345", "\\d+"));
        assertDoesNotThrow(() -> Validate.matchesPattern("abc", "[a-c]{3}"));
        assertDoesNotThrow(() -> Validate.matchesPattern("", ".*"));
    }

    @Test
    void testMatchesPattern_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("hello", "xyz"));
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("123", "[a-z]+"));
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("abc", "[a-c]{2}"));
    }

    @Test
    void testMatchesPattern_EdgeCases() {
        // Null values
        assertThrows(NullPointerException.class, () -> Validate.matchesPattern(null, ".*"));
        assertThrows(NullPointerException.class, () -> Validate.matchesPattern("hello", null));
        assertThrows(NullPointerException.class, () -> Validate.matchesPattern(null, null));

        // Invalid regex pattern
        assertThrows(PatternSyntaxException.class, () -> Validate.matchesPattern("hello", "["));
        assertThrows(PatternSyntaxException.class, () -> Validate.matchesPattern("hello", "*"));
    }

    @Test
    void testMatchesPatternWithMessage_NormalInvalid() {
        String message = "Input '%s' does not match pattern '%s'";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.matchesPattern("hello", "xyz", message, "hello", "xyz"));
        assertEquals("Input 'hello' does not match pattern 'xyz'", e.getMessage());
    }

    // --- noNullElements (Iterable) ---
    @Test
    void testNoNullElementsIterable_NormalValid() {
        List<String> list = Arrays.asList("a", "b", "c");
        assertDoesNotThrow(() -> Validate.noNullElements(list));
        assertEquals(list, Validate.noNullElements(list));

        Set<Integer> set = new HashSet<>(Arrays.asList(1, 2, 3));
        assertDoesNotThrow(() -> Validate.noNullElements(set));
        assertEquals(set, Validate.noNullElements(set));

        List<String> emptyList = Collections.emptyList();
        assertDoesNotThrow(() -> Validate.noNullElements(emptyList));
        assertEquals(emptyList, Validate.noNullElements(emptyList));
    }

    @Test
    void testNoNullElementsIterable_NormalInvalid() {
        List<String> listWithNull = new ArrayList<>(Arrays.asList("a", null, "c"));
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(listWithNull));

        Set<Integer> setWithNull = new HashSet<>();
        setWithNull.add(1);
        setWithNull.add(null);
        setWithNull.add(3);
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(setWithNull));
    }

    @Test
    void testNoNullElementsIterable_EdgeCases() {
        // Null iterable
        assertThrows(NullPointerException.class, () -> Validate.noNullElements((Iterable<?>) null));
    }

    @Test
    void testNoNullElementsIterableWithMessage_NormalInvalid() {
        String message = "Iterable contains null at index %s";
        List<String> listWithNull = new ArrayList<>(Arrays.asList("a", null, "c"));
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.noNullElements(listWithNull, message, 1));
        assertEquals("Iterable contains null at index 1", e.getMessage());
    }

    // --- noNullElements (Array) ---
    @Test
    void testNoNullElementsArray_NormalValid() {
        String[] array = {"a", "b", "c"};
        assertDoesNotThrow(() -> Validate.noNullElements(array));
        assertEquals(array, Validate.noNullElements(array));

        Integer[] emptyArray = {};
        assertDoesNotThrow(() -> Validate.noNullElements(emptyArray));
        assertEquals(emptyArray, Validate.noNullElements(emptyArray));
    }

    @Test
    void testNoNullElementsArray_NormalInvalid() {
        String[] arrayWithNull = {"a", null, "c"};
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(arrayWithNull));

        Object[] arrayWithNullAtStart = {null, "b", "c"};
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(arrayWithNullAtStart));

        Object[] arrayWithNullAtEnd = {"a", "b", null};
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(arrayWithNullAtEnd));
    }

    @Test
    void testNoNullElementsArray_EdgeCases() {
        // Null array
        assertThrows(NullPointerException.class, () -> Validate.noNullElements((Object[]) null));
    }

    @Test
    void testNoNullElementsArrayWithMessage_NormalInvalid() {
        String message = "Array contains null at index %s";
        String[] arrayWithNull = {"a", null, "c"};
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.noNullElements(arrayWithNull, message, 1));
        assertEquals("Array contains null at index 1", e.getMessage());
    }

    // --- notBlank (CharSequence) ---
    @Test
    void testNotBlankCharSequence_NormalValid() {
        assertEquals("hello", Validate.notBlank("hello"));
        assertEquals(" a ", Validate.notBlank(" a "));
    }

    @Test
    void testNotBlankCharSequence_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notBlank(""));
        assertThrows(IllegalArgumentException.class, () -> Validate.notBlank(" "));
        assertThrows(IllegalArgumentException.class, () -> Validate.notBlank("\t\n"));
    }

    @Test
    void testNotBlankCharSequence_EdgeCases() {
        // Null CharSequence
        assertThrows(NullPointerException.class, () -> Validate.notBlank((CharSequence) null));
    }

    @Test
    void testNotBlankCharSequenceWithMessage_NormalInvalid() {
        String message = "Input '%s' cannot be blank";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notBlank(" ", message, " "));
        assertEquals("Input ' ' cannot be blank", e.getMessage());
    }

    // --- notEmpty (Collection) ---
    @Test
    void testNotEmptyCollection_NormalValid() {
        List<String> list = Arrays.asList("a", "b");
        assertEquals(list, Validate.notEmpty(list));
        Set<Integer> set = Collections.singleton(1);
        assertEquals(set, Validate.notEmpty(set));
    }

    @Test
    void testNotEmptyCollection_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(new ArrayList<>()));
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(new HashSet<>()));
    }

    @Test
    void testNotEmptyCollection_EdgeCases() {
        // Null collection
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((Collection<?>) null));
    }

    @Test
    void testNotEmptyCollectionWithMessage_NormalInvalid() {
        String message = "Collection cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty(new ArrayList<>(), message));
        assertEquals("Collection cannot be empty", e.getMessage());
    }

    // --- notEmpty (Map) ---
    @Test
    void testNotEmptyMap_NormalValid() {
        Map<String, String> map = Collections.singletonMap("key", "value");
        assertEquals(map, Validate.notEmpty(map));
    }

    @Test
    void testNotEmptyMap_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(new HashMap<>()));
    }

    @Test
    void testNotEmptyMap_EdgeCases() {
        // Null map
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((Map<?, ?>) null));
    }

    @Test
    void testNotEmptyMapWithMessage_NormalInvalid() {
        String message = "Map cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty(new HashMap<>(), message));
        assertEquals("Map cannot be empty", e.getMessage());
    }

    // --- notEmpty (CharSequence) ---
    @Test
    void testNotEmptyCharSequence_NormalValid() {
        assertEquals("hello", Validate.notEmpty("hello"));
        assertEquals(" ", Validate.notEmpty(" "));
    }

    @Test
    void testNotEmptyCharSequence_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(""));
    }

    @Test
    void testNotEmptyCharSequence_EdgeCases() {
        // Null CharSequence
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((CharSequence) null));
    }

    @Test
    void testNotEmptyCharSequenceWithMessage_NormalInvalid() {
        String message = "CharSequence cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty("", message));
        assertEquals("CharSequence cannot be empty", e.getMessage());
    }

    // --- notEmpty (Array) ---
    @Test
    void testNotEmptyArray_NormalValid() {
        String[] array = {"a", "b"};
        assertEquals(array, Validate.notEmpty(array));
    }

    @Test
    void testNotEmptyArray_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(new String[]{}));
    }

    @Test
    void testNotEmptyArray_EdgeCases() {
        // Null array
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((Object[]) null));
    }

    @Test
    void testNotEmptyArrayWithMessage_NormalInvalid() {
        String message = "Array cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty(new String[]{}, message));
        assertEquals("Array cannot be empty", e.getMessage());
    }

    // --- notNaN (double) ---
    @Test
    void testNotNaNDouble_NormalValid() {
        assertDoesNotThrow(() -> Validate.notNaN(0.0));
        assertDoesNotThrow(() -> Validate.notNaN(1.0));
        assertDoesNotThrow(() -> Validate.notNaN(-1.0));
        assertDoesNotThrow(() -> Validate.notNaN(Double.MAX_VALUE));
        assertDoesNotThrow(() -> Validate.notNaN(Double.MIN_VALUE));
        assertDoesNotThrow(() -> Validate.notNaN(Double.POSITIVE_INFINITY));
        assertDoesNotThrow(() -> Validate.notNaN(Double.NEGATIVE_INFINITY));
    }

    @Test
    void testNotNaNDouble_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notNaN(Double.NaN));
    }

    @