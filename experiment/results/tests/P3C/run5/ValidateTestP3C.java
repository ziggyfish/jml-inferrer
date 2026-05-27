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
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.*;

public class ValidateTestP3CP3C {

    // --- exclusiveBetween (double) ---

    @Test
    void testExclusiveBetweenDouble_NormalValid() {
        Validate.exclusiveBetween(0.0, 10.0, 5.0);
        Validate.exclusiveBetween(-10.0, 0.0, -5.0);
        Validate.exclusiveBetween(Double.MIN_VALUE, Double.MAX_VALUE, 1.0);
    }

    @Test
    void testExclusiveBetweenDouble_NormalInvalid_LowerBound() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 0.0));
    }

    @Test
    void testExclusiveBetweenDouble_NormalInvalid_UpperBound() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 10.0));
    }

    @Test
    void testExclusiveBetweenDouble_NormalInvalid_OutsideRange() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, -1.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, 11.0));
    }

    @Test
    void testExclusiveBetweenDouble_EdgeCase_StartEqualsEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 4.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5.0, 5.0, 6.0));
    }

    @Test
    void testExclusiveBetweenDouble_EdgeCase_StartGreaterThanEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10.0, 0.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10.0, 0.0, 10.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10.0, 0.0, 0.0));
    }

    @Test
    void testExclusiveBetweenDouble_NaN_Start() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Double.NaN, 10.0, 5.0));
    }

    @Test
    void testExclusiveBetweenDouble_NaN_End() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, Double.NaN, 5.0));
    }

    @Test
    void testExclusiveBetweenDouble_NaN_Value() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, 10.0, Double.NaN));
    }

    @Test
    void testExclusiveBetweenDouble_Infinity_Valid() {
        Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0);
        Validate.exclusiveBetween(0.0, Double.POSITIVE_INFINITY, 100.0);
        Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, 0.0, -100.0);
    }

    @Test
    void testExclusiveBetweenDouble_Infinity_Invalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0.0, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(Double.NEGATIVE_INFINITY, 0.0, Double.NEGATIVE_INFINITY));
    }

    @Test
    void testExclusiveBetweenDouble_WithMessage_NormalInvalid() {
        String message = "Value %s is not exclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.exclusiveBetween(0.0, 10.0, 0.0, message, 0.0, 0.0, 10.0));
        assertEquals("Value 0.0 is not exclusively between 0.0 and 10.0", e.getMessage());
    }

    // --- exclusiveBetween (long) ---

    @Test
    void testExclusiveBetweenLong_NormalValid() {
        Validate.exclusiveBetween(0L, 10L, 5L);
        Validate.exclusiveBetween(-10L, 0L, -5L);
        Validate.exclusiveBetween(Long.MIN_VALUE, Long.MAX_VALUE, 0L);
    }

    @Test
    void testExclusiveBetweenLong_NormalInvalid_LowerBound() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 0L));
    }

    @Test
    void testExclusiveBetweenLong_NormalInvalid_UpperBound() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 10L));
    }

    @Test
    void testExclusiveBetweenLong_NormalInvalid_OutsideRange() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, -1L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(0L, 10L, 11L));
    }

    @Test
    void testExclusiveBetweenLong_EdgeCase_StartEqualsEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 5L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 4L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(5L, 5L, 6L));
    }

    @Test
    void testExclusiveBetweenLong_EdgeCase_StartGreaterThanEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10L, 0L, 5L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10L, 0L, 10L));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween(10L, 0L, 0L));
    }

    @Test
    void testExclusiveBetweenLong_WithMessage_NormalInvalid() {
        String message = "Value %s is not exclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.exclusiveBetween(0L, 10L, 0L, message, 0L, 0L, 10L));
        assertEquals("Value 0 is not exclusively between 0 and 10", e.getMessage());
    }

    // --- exclusiveBetween (Comparable) ---

    @Test
    void testExclusiveBetweenComparable_NormalValid() {
        Validate.exclusiveBetween("a", "z", "m");
        Validate.exclusiveBetween(Integer.valueOf(0), Integer.valueOf(10), Integer.valueOf(5));
    }

    @Test
    void testExclusiveBetweenComparable_NormalInvalid_LowerBound() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "a"));
    }

    @Test
    void testExclusiveBetweenComparable_NormalInvalid_UpperBound() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", "z"));
    }

    @Test
    void testExclusiveBetweenComparable_NormalInvalid_OutsideRange() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("b", "y", "a"));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("b", "y", "z"));
    }

    @Test
    void testExclusiveBetweenComparable_EdgeCase_StartEqualsEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "a", "a"));
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "a", "b"));
    }

    @Test
    void testExclusiveBetweenComparable_EdgeCase_StartGreaterThanEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("z", "a", "m"));
    }

    @Test
    void testExclusiveBetweenComparable_Null_Start() {
        assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween(null, "z", "m"));
    }

    @Test
    void testExclusiveBetweenComparable_Null_End() {
        assertThrows(NullPointerException.class, () -> Validate.exclusiveBetween("a", null, "m"));
    }

    @Test
    void testExclusiveBetweenComparable_Null_Value() {
        assertThrows(IllegalArgumentException.class, () -> Validate.exclusiveBetween("a", "z", null));
    }

    @Test
    void testExclusiveBetweenComparable_WithMessage_NormalInvalid() {
        String message = "Value %s is not exclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.exclusiveBetween("a", "z", "a", message, "a", "a", "z"));
        assertEquals("Value a is not exclusively between a and z", e.getMessage());
    }

    // --- finite (double) ---

    @Test
    void testFiniteDouble_NormalValid() {
        Validate.finite(0.0);
        Validate.finite(1.0);
        Validate.finite(-1.0);
        Validate.finite(Double.MAX_VALUE);
        Validate.finite(Double.MIN_VALUE);
    }

    @Test
    void testFiniteDouble_Invalid_NaN() {
        assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.NaN));
    }

    @Test
    void testFiniteDouble_Invalid_PositiveInfinity() {
        assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.POSITIVE_INFINITY));
    }

    @Test
    void testFiniteDouble_Invalid_NegativeInfinity() {
        assertThrows(IllegalArgumentException.class, () -> Validate.finite(Double.NEGATIVE_INFINITY));
    }

    @Test
    void testFiniteDouble_WithMessage_Invalid() {
        String message = "Value %s is not finite";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.finite(Double.POSITIVE_INFINITY, message, Double.POSITIVE_INFINITY));
        assertEquals("Value Infinity is not finite", e.getMessage());
    }

    // --- getMessage (private, not directly testable, but its effect is seen in other tests) ---

    // --- inclusiveBetween (double) ---

    @Test
    void testInclusiveBetweenDouble_NormalValid() {
        Validate.inclusiveBetween(0.0, 10.0, 5.0);
        Validate.inclusiveBetween(0.0, 10.0, 0.0); // Lower bound
        Validate.inclusiveBetween(0.0, 10.0, 10.0); // Upper bound
        Validate.inclusiveBetween(-10.0, 0.0, -5.0);
    }

    @Test
    void testInclusiveBetweenDouble_NormalInvalid_OutsideRange() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, -1.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, 11.0));
    }

    @Test
    void testInclusiveBetweenDouble_EdgeCase_StartEqualsEnd_Valid() {
        Validate.inclusiveBetween(5.0, 5.0, 5.0);
    }

    @Test
    void testInclusiveBetweenDouble_EdgeCase_StartEqualsEnd_Invalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5.0, 5.0, 4.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5.0, 5.0, 6.0));
    }

    @Test
    void testInclusiveBetweenDouble_EdgeCase_StartGreaterThanEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10.0, 0.0, 5.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10.0, 0.0, 10.0));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10.0, 0.0, 0.0));
    }

    @Test
    void testInclusiveBetweenDouble_NaN_Start() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(Double.NaN, 10.0, 5.0));
    }

    @Test
    void testInclusiveBetweenDouble_NaN_End() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, Double.NaN, 5.0));
    }

    @Test
    void testInclusiveBetweenDouble_NaN_Value() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, Double.NaN));
    }

    @Test
    void testInclusiveBetweenDouble_Infinity_Valid() {
        Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 0.0);
        Validate.inclusiveBetween(0.0, Double.POSITIVE_INFINITY, 100.0);
        Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, 0.0, -100.0);
        Validate.inclusiveBetween(0.0, Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
        Validate.inclusiveBetween(Double.NEGATIVE_INFINITY, 0.0, Double.NEGATIVE_INFINITY);
    }

    @Test
    void testInclusiveBetweenDouble_Infinity_Invalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, Double.POSITIVE_INFINITY));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0.0, 10.0, Double.NEGATIVE_INFINITY));
    }

    @Test
    void testInclusiveBetweenDouble_WithMessage_NormalInvalid() {
        String message = "Value %s is not inclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.inclusiveBetween(0.0, 10.0, -1.0, message, -1.0, 0.0, 10.0));
        assertEquals("Value -1.0 is not inclusively between 0.0 and 10.0", e.getMessage());
    }

    // --- inclusiveBetween (long) ---

    @Test
    void testInclusiveBetweenLong_NormalValid() {
        Validate.inclusiveBetween(0L, 10L, 5L);
        Validate.inclusiveBetween(0L, 10L, 0L);
        Validate.inclusiveBetween(0L, 10L, 10L);
        Validate.inclusiveBetween(-10L, 0L, -5L);
    }

    @Test
    void testInclusiveBetweenLong_NormalInvalid_OutsideRange() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0L, 10L, -1L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(0L, 10L, 11L));
    }

    @Test
    void testInclusiveBetweenLong_EdgeCase_StartEqualsEnd_Valid() {
        Validate.inclusiveBetween(5L, 5L, 5L);
    }

    @Test
    void testInclusiveBetweenLong_EdgeCase_StartEqualsEnd_Invalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5L, 5L, 4L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(5L, 5L, 6L));
    }

    @Test
    void testInclusiveBetweenLong_EdgeCase_StartGreaterThanEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10L, 0L, 5L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10L, 0L, 10L));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween(10L, 0L, 0L));
    }

    @Test
    void testInclusiveBetweenLong_WithMessage_NormalInvalid() {
        String message = "Value %s is not inclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.inclusiveBetween(0L, 10L, -1L, message, -1L, 0L, 10L));
        assertEquals("Value -1 is not inclusively between 0 and 10", e.getMessage());
    }

    // --- inclusiveBetween (Comparable) ---

    @Test
    void testInclusiveBetweenComparable_NormalValid() {
        Validate.inclusiveBetween("a", "z", "m");
        Validate.inclusiveBetween("a", "z", "a");
        Validate.inclusiveBetween("a", "z", "z");
        Validate.inclusiveBetween(Integer.valueOf(0), Integer.valueOf(10), Integer.valueOf(5));
    }

    @Test
    void testInclusiveBetweenComparable_NormalInvalid_OutsideRange() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("b", "y", "a"));
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("b", "y", "z"));
    }

    @Test
    void testInclusiveBetweenComparable_EdgeCase_StartEqualsEnd_Valid() {
        Validate.inclusiveBetween("a", "a", "a");
    }

    @Test
    void testInclusiveBetweenComparable_EdgeCase_StartEqualsEnd_Invalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("a", "a", "b"));
    }

    @Test
    void testInclusiveBetweenComparable_EdgeCase_StartGreaterThanEnd() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("z", "a", "m"));
    }

    @Test
    void testInclusiveBetweenComparable_Null_Start() {
        assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween(null, "z", "m"));
    }

    @Test
    void testInclusiveBetweenComparable_Null_End() {
        assertThrows(NullPointerException.class, () -> Validate.inclusiveBetween("a", null, "m"));
    }

    @Test
    void testInclusiveBetweenComparable_Null_Value() {
        assertThrows(IllegalArgumentException.class, () -> Validate.inclusiveBetween("a", "z", null));
    }

    @Test
    void testInclusiveBetweenComparable_WithMessage_NormalInvalid() {
        String message = "Value %s is not inclusively between %s and %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.inclusiveBetween("a", "z", "0", message, "0", "a", "z"));
        assertEquals("Value 0 is not inclusively between a and z", e.getMessage());
    }

    // --- isAssignableFrom ---

    @Test
    void testIsAssignableFrom_NormalValid() {
        Validate.isAssignableFrom(Object.class, String.class);
        Validate.isAssignableFrom(List.class, ArrayList.class);
        Validate.isAssignableFrom(Number.class, Integer.class);
        Validate.isAssignableFrom(Object.class, Object.class); // Same class
    }

    @Test
    void testIsAssignableFrom_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(String.class, Object.class));
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(ArrayList.class, List.class));
        assertThrows(IllegalArgumentException.class, () -> Validate.isAssignableFrom(Integer.class, Number.class));
    }

    @Test
    void testIsAssignableFrom_Null_SuperType() {
        assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(null, String.class));
    }

    @Test
    void testIsAssignableFrom_Null_Type() {
        assertThrows(NullPointerException.class, () -> Validate.isAssignableFrom(Object.class, null));
    }

    @Test
    void testIsAssignableFrom_WithMessage_NormalInvalid() {
        String message = "%s is not assignable from %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isAssignableFrom(String.class, Object.class, message, String.class.getName(), Object.class.getName()));
        assertEquals("java.lang.String is not assignable from java.lang.Object", e.getMessage());
    }

    // --- isInstanceOf ---

    @Test
    void testIsInstanceOf_NormalValid() {
        Validate.isInstanceOf(String.class, "hello");
        Validate.isInstanceOf(Object.class, 123);
        Validate.isInstanceOf(List.class, new ArrayList<>());
        Validate.isInstanceOf(Integer.class, Integer.valueOf(10));
    }

    @Test
    void testIsInstanceOf_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(String.class, 123));
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(Integer.class, "hello"));
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(ArrayList.class, new HashSet<>()));
    }

    @Test
    void testIsInstanceOf_Null_Type() {
        assertThrows(NullPointerException.class, () -> Validate.isInstanceOf(null, "hello"));
    }

    @Test
    void testIsInstanceOf_Null_Object() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isInstanceOf(String.class, null));
    }

    @Test
    void testIsInstanceOf_WithMessage_NormalInvalid() {
        String message = "%s is not an instance of %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isInstanceOf(String.class, 123, message, 123, String.class.getName()));
        assertEquals("123 is not an instance of java.lang.String", e.getMessage());
    }

    // --- isTrue (boolean) ---

    @Test
    void testIsTrueBoolean_NormalValid() {
        Validate.isTrue(true);
    }

    @Test
    void testIsTrueBoolean_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.isTrue(false));
    }

    @Test
    void testIsTrueBoolean_WithMessage_Double_NormalInvalid() {
        String message = "Expression is false: %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, message, 1.23));
        assertEquals("Expression is false: 1.23", e.getMessage());
    }

    @Test
    void testIsTrueBoolean_WithMessage_Long_NormalInvalid() {
        String message = "Expression is false: %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, message, 123L));
        assertEquals("Expression is false: 123", e.getMessage());
    }

    @Test
    void testIsTrueBoolean_WithMessage_Object_NormalInvalid() {
        String message = "Expression is false: %s, %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, message, "error", 42));
        assertEquals("Expression is false: error, 42", e.getMessage());
    }

    @Test
    void testIsTrueBoolean_WithMessageSupplier_NormalInvalid() {
        Supplier<String> messageSupplier = () -> "Supplier message";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.isTrue(false, messageSupplier));
        assertEquals("Supplier message", e.getMessage());
    }

    @Test
    void testIsTrueBoolean_WithMessageSupplier_Valid() {
        Validate.isTrue(true, () -> "This message should not be evaluated");
    }

    @Test
    void testIsTrueBoolean_WithMessageSupplier_NullSupplier() {
        assertThrows(NullPointerException.class, () -> Validate.isTrue(false, (Supplier<String>) null));
    }

    // --- matchesPattern ---

    @Test
    void testMatchesPattern_NormalValid() {
        Validate.matchesPattern("hello", "h.*o");
        Validate.matchesPattern("12345", "\\d+");
        Validate.matchesPattern("abc", "[a-c]{3}");
    }

    @Test
    void testMatchesPattern_NormalInvalid() {
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("hello", "xyz"));
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("abc", "\\d+"));
    }

    @Test
    void testMatchesPattern_Null_Input() {
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern(null, "\\d+"));
    }

    @Test
    void testMatchesPattern_Null_Pattern() {
        assertThrows(NullPointerException.class, () -> Validate.matchesPattern("hello", null));
    }

    @Test
    void testMatchesPattern_Empty_Input() {
        Validate.matchesPattern("", ".*");
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("", "a+"));
    }

    @Test
    void testMatchesPattern_Empty_Pattern() {
        Validate.matchesPattern("abc", ""); // Empty pattern matches any string
        Validate.matchesPattern("", "");
    }

    @Test
    void testMatchesPattern_InvalidRegexSyntax() {
        assertThrows(IllegalArgumentException.class, () -> Validate.matchesPattern("hello", "[")); // Malformed regex
    }

    @Test
    void testMatchesPattern_WithMessage_NormalInvalid() {
        String message = "Input '%s' does not match pattern '%s'";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.matchesPattern("hello", "xyz", message, "hello", "xyz"));
        assertEquals("Input 'hello' does not match pattern 'xyz'", e.getMessage());
    }

    // --- noNullElements (Iterable) ---

    @Test
    void testNoNullElementsIterable_NormalValid() {
        List<String> list = Arrays.asList("a", "b", "c");
        assertSame(list, Validate.noNullElements(list));

        Set<Integer> set = new HashSet<>(Arrays.asList(1, 2, 3));
        assertSame(set, Validate.noNullElements(set));

        Collection<Object> empty = Collections.emptyList();
        assertSame(empty, Validate.noNullElements(empty));
    }

    @Test
    void testNoNullElementsIterable_NormalInvalid() {
        List<String> listWithNull = new ArrayList<>(Arrays.asList("a", null, "c"));
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(listWithNull));
    }

    @Test
    void testNoNullElementsIterable_Null_Iterable() {
        assertThrows(NullPointerException.class, () -> Validate.noNullElements((Iterable<?>) null));
    }

    @Test
    void testNoNullElementsIterable_WithMessage_NormalInvalid() {
        List<String> listWithNull = new ArrayList<>(Arrays.asList("a", null, "c"));
        String message = "Iterable contains null element at index %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.noNullElements(listWithNull, message, 1));
        assertEquals("Iterable contains null element at index 1", e.getMessage());
    }

    // --- noNullElements (Array) ---

    @Test
    void testNoNullElementsArray_NormalValid() {
        String[] array = {"a", "b", "c"};
        assertSame(array, Validate.noNullElements(array));

        Integer[] emptyArray = {};
        assertSame(emptyArray, Validate.noNullElements(emptyArray));
    }

    @Test
    void testNoNullElementsArray_NormalInvalid() {
        String[] arrayWithNull = {"a", null, "c"};
        assertThrows(IllegalArgumentException.class, () -> Validate.noNullElements(arrayWithNull));
    }

    @Test
    void testNoNullElementsArray_Null_Array() {
        assertThrows(NullPointerException.class, () -> Validate.noNullElements((Object[]) null));
    }

    @Test
    void testNoNullElementsArray_WithMessage_NormalInvalid() {
        String[] arrayWithNull = {"a", null, "c"};
        String message = "Array contains null element at index %s";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.noNullElements(arrayWithNull, message, 1));
        assertEquals("Array contains null element at index 1", e.getMessage());
    }

    // --- notBlank (CharSequence) ---

    @Test
    void testNotBlankCharSequence_NormalValid() {
        assertEquals("hello", Validate.notBlank("hello"));
        assertEquals("  a  ", Validate.notBlank("  a  "));
    }

    @Test
    void testNotBlankCharSequence_NormalInvalid_Empty() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notBlank(""));
    }

    @Test
    void testNotBlankCharSequence_NormalInvalid_Blank() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notBlank(" "));
        assertThrows(IllegalArgumentException.class, () -> Validate.notBlank("\t\n"));
    }

    @Test
    void testNotBlankCharSequence_Null_CharSequence() {
        assertThrows(NullPointerException.class, () -> Validate.notBlank((String) null));
    }

    @Test
    void testNotBlankCharSequence_WithMessage_NormalInvalid() {
        String message = "Input '%s' cannot be blank";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notBlank(" ", message, " "));
        assertEquals("Input ' ' cannot be blank", e.getMessage());
    }

    // --- notEmpty (Collection) ---

    @Test
    void testNotEmptyCollection_NormalValid() {
        List<String> list = Arrays.asList("a", "b");
        assertSame(list, Validate.notEmpty(list));
    }

    @Test
    void testNotEmptyCollection_NormalInvalid_Empty() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(Collections.emptyList()));
    }

    @Test
    void testNotEmptyCollection_Null_Collection() {
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((Collection<?>) null));
    }

    @Test
    void testNotEmptyCollection_WithMessage_NormalInvalid() {
        String message = "Collection cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty(Collections.emptySet(), message));
        assertEquals("Collection cannot be empty", e.getMessage());
    }

    // --- notEmpty (Map) ---

    @Test
    void testNotEmptyMap_NormalValid() {
        Map<String, String> map = new HashMap<>();
        map.put("key", "value");
        assertSame(map, Validate.notEmpty(map));
    }

    @Test
    void testNotEmptyMap_NormalInvalid_Empty() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(Collections.emptyMap()));
    }

    @Test
    void testNotEmptyMap_Null_Map() {
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((Map<?, ?>) null));
    }

    @Test
    void testNotEmptyMap_WithMessage_NormalInvalid() {
        String message = "Map cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty(Collections.emptyMap(), message));
        assertEquals("Map cannot be empty", e.getMessage());
    }

    // --- notEmpty (CharSequence) ---

    @Test
    void testNotEmptyCharSequence_NormalValid() {
        assertEquals("hello", Validate.notEmpty("hello"));
        assertEquals(" ", Validate.notEmpty(" ")); // Blank is not empty
    }

    @Test
    void testNotEmptyCharSequence_NormalInvalid_Empty() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(""));
    }

    @Test
    void testNotEmptyCharSequence_Null_CharSequence() {
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((String) null));
    }

    @Test
    void testNotEmptyCharSequence_WithMessage_NormalInvalid() {
        String message = "Input cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty("", message));
        assertEquals("Input cannot be empty", e.getMessage());
    }

    // --- notEmpty (Array) ---

    @Test
    void testNotEmptyArray_NormalValid() {
        String[] array = {"a", "b"};
        assertSame(array, Validate.notEmpty(array));
    }

    @Test
    void testNotEmptyArray_NormalInvalid_Empty() {
        assertThrows(IllegalArgumentException.class, () -> Validate.notEmpty(new String[]{}));
    }

    @Test
    void testNotEmptyArray_Null_Array() {
        assertThrows(NullPointerException.class, () -> Validate.notEmpty((Object[]) null));
    }

    @Test
    void testNotEmptyArray_WithMessage_NormalInvalid() {
        String message = "Array cannot be empty";
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> Validate.notEmpty(new Integer[]{}, message));
        assertEquals("Array cannot be empty", e.getMessage());
    }

    // --- notNaN (double) ---

    @Test
    void testNotNaNDouble_NormalValid() {
        Validate.notNaN(0.0);
        Validate.notNaN(1.0);
        Validate.notNaN(-1