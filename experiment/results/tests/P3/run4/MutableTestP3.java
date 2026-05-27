package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.Mutable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive unit tests for the Mutable interface.
 * This class tests the default method 'get()' and the abstract methods
 * 'getValue()' and 'setValue(T value)' through concrete implementations.
 */
class MutableTestP3P3 {

    // A concrete implementation of Mutable for testing purposes
    private static class TestMutable<T> implements Mutable<T> {
        private T value;

        public TestMutable(T initialValue) {
            this.value = initialValue;
        }

        @Override
        public T getValue() {
            return value;
        }

        @Override
        public void setValue(T value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null || getClass() != obj.getClass()) return false;
            TestMutable<?> that = (TestMutable<?>) obj;
            return java.util.Objects.equals(value, that.value);
        }

        @Override
        public int hashCode() {
            return java.util.Objects.hash(value);
        }
    }

    private TestMutable<String> mutableString;
    private TestMutable<Integer> mutableInteger;
    private TestMutable<Object> mutableObject;

    @BeforeEach
    void setUp() {
        mutableString = new TestMutable<>("initial");
        mutableInteger = new TestMutable<>(123);
        mutableObject = new TestMutable<>(new Object());
    }

    @Nested
    @DisplayName("Tests for get() method")
    class GetMethodTests {

        @Test
        @DisplayName("get() should return the current value for String type")
        void get_shouldReturnCurrentValue_String() {
            assertEquals("initial", mutableString.get());
        }

        @Test
        @DisplayName("get() should return the current value for Integer type")
        void get_shouldReturnCurrentValue_Integer() {
            assertEquals(123, mutableInteger.get());
        }

        @Test
        @DisplayName("get() should return the current value for Object type")
        void get_shouldReturnCurrentValue_Object() {
            Object obj = mutableObject.getValue(); // Get the initial object reference
            assertSame(obj, mutableObject.get());
        }

        @Test
        @DisplayName("get() should return null if value is null")
        void get_shouldReturnNull_whenValueIsNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.get());
        }

        @Test
        @DisplayName("get() should return the updated value after setValue")
        void get_shouldReturnUpdatedValue_afterSetValue() {
            mutableString.setValue("updated");
            assertEquals("updated", mutableString.get());
        }
    }

    @Nested
    @DisplayName("Tests for getValue() method")
    class GetValueMethodTests {

        @Test
        @DisplayName("getValue() should return the initial value for String type")
        void getValue_shouldReturnInitialValue_String() {
            assertEquals("initial", mutableString.getValue());
        }

        @Test
        @DisplayName("getValue() should return the initial value for Integer type")
        void getValue_shouldReturnInitialValue_Integer() {
            assertEquals(123, mutableInteger.getValue());
        }

        @Test
        @DisplayName("getValue() should return the initial value for Object type")
        void getValue_shouldReturnInitialValue_Object() {
            Object obj = mutableObject.getValue(); // Get the initial object reference
            assertSame(obj, mutableObject.getValue());
        }

        @Test
        @DisplayName("getValue() should return null if initial value is null")
        void getValue_shouldReturnNull_whenInitialValueIsNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.getValue());
        }

        @Test
        @DisplayName("getValue() should return the updated value after setValue")
        void getValue_shouldReturnUpdatedValue_afterSetValue() {
            mutableInteger.setValue(456);
            assertEquals(456, mutableInteger.getValue());
        }

        @Test
        @DisplayName("getValue() should return the same object reference for mutable objects")
        void getValue_shouldReturnSameObjectReference() {
            StringBuilder sb = new StringBuilder("hello");
            TestMutable<StringBuilder> mutableSb = new TestMutable<>(sb);
            assertSame(sb, mutableSb.getValue());

            // Ensure it's not a copy
            mutableSb.getValue().append(" world");
            assertEquals("hello world", sb.toString());
        }
    }

    @Nested
    @DisplayName("Tests for setValue(T value) method")
    class SetValueMethodTests {

        @ParameterizedTest
        @ValueSource(strings = {"new value", "", "another value with spaces"})
        @DisplayName("setValue() should update the value for String type")
        void setValue_shouldUpdateValue_String(String newValue) {
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.getValue());
            assertEquals(newValue, mutableString.get()); // Also check get()
        }

        @ParameterizedTest
        @NullSource
        @DisplayName("setValue() should allow setting null for String type")
        void setValue_shouldAllowSettingNull_String(String nullValue) {
            mutableString.setValue(nullValue);
            assertNull(mutableString.getValue());
            assertNull(mutableString.get());
        }

        @ParameterizedTest
        @ValueSource(ints = {0, 1, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
        @DisplayName("setValue() should update the value for Integer type")
        void setValue_shouldUpdateValue_Integer(int newValue) {
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.getValue());
            assertEquals(newValue, mutableInteger.get());
        }

        @ParameterizedTest
        @NullSource
        @DisplayName("setValue() should allow setting null for Integer type")
        void setValue_shouldAllowSettingNull_Integer(Integer nullValue) {
            mutableInteger.setValue(nullValue);
            assertNull(mutableInteger.getValue());
            assertNull(mutableInteger.get());
        }

        @Test
        @DisplayName("setValue() should update the value for Object type")
        void setValue_shouldUpdateValue_Object() {
            Object newObj = new Object();
            mutableObject.setValue(newObj);
            assertSame(newObj, mutableObject.getValue());
            assertSame(newObj, mutableObject.get());
        }

        @Test
        @DisplayName("setValue() should allow setting null for Object type")
        void setValue_shouldAllowSettingNull_Object() {
            mutableObject.setValue(null);
            assertNull(mutableObject.getValue());
            assertNull(mutableObject.get());
        }

        @Test
        @DisplayName("setValue() with the same value should not change the value")
        void setValue_sameValue_shouldNotChangeValue() {
            String initial = mutableString.getValue();
            mutableString.setValue(initial);
            assertEquals(initial, mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with a new object reference should update the reference")
        void setValue_newObjectReference_shouldUpdateReference() {
            StringBuilder sb1 = new StringBuilder("one");
            StringBuilder sb2 = new StringBuilder("two");
            TestMutable<StringBuilder> mutableSb = new TestMutable<>(sb1);

            assertSame(sb1, mutableSb.getValue());
            mutableSb.setValue(sb2);
            assertSame(sb2, mutableSb.getValue());
            assertNotSame(sb1, mutableSb.getValue());
        }
    }

    @Nested
    @DisplayName("Interaction Tests")
    class InteractionTests {

        @Test
        @DisplayName("setValue followed by getValue should return the last set value")
        void setValue_then_getValue_returnsLastSet() {
            mutableString.setValue("first");
            assertEquals("first", mutableString.getValue());
            mutableString.setValue("second");
            assertEquals("second", mutableString.getValue());
            mutableString.setValue(null);
            assertNull(mutableString.getValue());
            mutableString.setValue("final");
            assertEquals("final", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue followed by get should return the last set value")
        void setValue_then_get_returnsLastSet() {
            mutableInteger.setValue(10);
            assertEquals(10, mutableInteger.get());
            mutableInteger.setValue(20);
            assertEquals(20, mutableInteger.get());
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
            mutableInteger.setValue(30);
            assertEquals(30, mutableInteger.get());
        }

        @Test
        @DisplayName("Multiple set and get operations should maintain consistency")
        void multipleSetGetOperations_maintainConsistency() {
            mutableString.setValue("A");
            assertEquals("A", mutableString.getValue());
            assertEquals("A", mutableString.get());

            mutableString.setValue("B");
            assertEquals("B", mutableString.getValue());
            assertEquals("B", mutableString.get());

            mutableString.setValue(null);
            assertNull(mutableString.getValue());
            assertNull(mutableString.get());

            mutableString.setValue("C");
            assertEquals("C", mutableString.getValue());
            assertEquals("C", mutableString.get());
        }
    }

    @Nested
    @DisplayName("Type Safety Tests")
    class TypeSafetyTests {

        @Test
        @DisplayName("Mutable<String> should only accept String values")
        void stringMutable_onlyAcceptsStrings() {
            TestMutable<String> stringMutable = new TestMutable<>("hello");
            stringMutable.setValue("world");
            assertEquals("world", stringMutable.getValue());

            // The following line would cause a compile-time error, demonstrating type safety
            // stringMutable.setValue(123); // This won't compile
        }

        @Test
        @DisplayName("Mutable<Integer> should only accept Integer values")
        void integerMutable_onlyAcceptsIntegers() {
            TestMutable<Integer> integerMutable = new TestMutable<>(10);
            integerMutable.setValue(20);
            assertEquals(20, integerMutable.getValue());

            // The following line would cause a compile-time error, demonstrating type safety
            // integerMutable.setValue("abc"); // This won't compile
        }

        @Test
        @DisplayName("Mutable<Object> should accept any object type")
        void objectMutable_acceptsAnyObject() {
            TestMutable<Object> objectMutable = new TestMutable<>(new String("string"));
            assertEquals("string", objectMutable.getValue());

            objectMutable.setValue(123);
            assertEquals(123, objectMutable.getValue());

            objectMutable.setValue(true);
            assertEquals(true, objectMutable.getValue());

            objectMutable.setValue(new StringBuilder("builder"));
            assertEquals(new StringBuilder("builder").toString(), objectMutable.getValue().toString());
        }
    }

    @Nested
    @DisplayName("Edge Cases for Initial State")
    class InitialStateEdgeCases {

        @Test
        @DisplayName("Mutable initialized with null should return null for get and getValue")
        void initializedWithNull_returnsNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.get());
            assertNull(nullMutable.getValue());
        }

        @Test
        @DisplayName("Mutable initialized with empty string should return empty string")
        void initializedWithEmptyString_returnsEmptyString() {
            TestMutable<String> emptyStringMutable = new TestMutable<>("");
            assertEquals("", emptyStringMutable.get());
            assertEquals("", emptyStringMutable.getValue());
        }

        @Test
        @DisplayName("Mutable initialized with zero should return zero")
        void initializedWithZero_returnsZero() {
            TestMutable<Integer> zeroMutable = new TestMutable<>(0);
            assertEquals(0, zeroMutable.get());
            assertEquals(0, zeroMutable.getValue());
        }
    }

    @Nested
    @DisplayName("toString, equals, hashCode Tests (for concrete implementation)")
    class UtilityMethodTests {

        @Test
        @DisplayName("toString() should return string representation of value")
        void toString_shouldReturnValueString() {
            assertEquals("initial", mutableString.toString());
            mutableString.setValue("new");
            assertEquals("new", mutableString.toString());
            mutableString.setValue(null);
            assertEquals("null", mutableString.toString());
        }

        @Test
        @DisplayName("equals() should compare based on value")
        void equals_shouldCompareBasedOnValue() {
            TestMutable<String> otherMutable = new TestMutable<>("initial");
            TestMutable<String> differentMutable = new TestMutable<>("different");
            TestMutable<String> nullMutable1 = new TestMutable<>(null);
            TestMutable<String> nullMutable2 = new TestMutable<>(null);

            assertTrue(mutableString.equals(otherMutable));
            assertFalse(mutableString.equals(differentMutable));
            assertFalse(mutableString.equals(null));
            assertFalse(mutableString.equals("initial")); // Different type

            assertTrue(nullMutable1.equals(nullMutable2));
            assertFalse(nullMutable1.equals(mutableString));
        }

        @Test
        @DisplayName("hashCode() should be consistent with equals()")
        void hashCode_shouldBeConsistentWithEquals() {
            TestMutable<String> otherMutable = new TestMutable<>("initial");
            TestMutable<String> differentMutable = new TestMutable<>("different");
            TestMutable<String> nullMutable1 = new TestMutable<>(null);
            TestMutable<String> nullMutable2 = new TestMutable<>(null);

            assertEquals(mutableString.hashCode(), otherMutable.hashCode());
            assertNotEquals(mutableString.hashCode(), differentMutable.hashCode());
            assertEquals(nullMutable1.hashCode(), nullMutable2.hashCode());
        }
    }
}