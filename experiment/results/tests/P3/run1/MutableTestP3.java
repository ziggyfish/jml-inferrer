package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.Mutable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the Mutable abstract class.
 * This class tests the contract defined by the JML specifications for the get, getValue, and setValue methods.
 * Since Mutable is abstract, we will test it using a concrete anonymous subclass.
 */
class MutableTestP3P3 {

    // A concrete implementation of Mutable for testing purposes
    private static class TestMutable<T> extends Mutable<T> {
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
    }

    private TestMutable<String> mutableString;
    private TestMutable<Integer> mutableInteger;
    private TestMutable<Object> mutableObject;

    @BeforeEach
    void setUp() {
        mutableString = new TestMutable<>("initial");
        mutableInteger = new TestMutable<>(100);
        mutableObject = new TestMutable<>(new Object());
    }

    @Nested
    @DisplayName("get() method tests")
    class GetMethodTests {

        /**
         * T get();
         * @ensures \result == getValue();
         */

        @Test
        @DisplayName("get() should return the current value for String")
        void get_shouldReturnCurrentValueForString() {
            String expected = "initial";
            assertEquals(expected, mutableString.get(), "get() should return the initial string value.");
            assertEquals(mutableString.getValue(), mutableString.get(), "get() should match getValue() for string.");
        }

        @Test
        @DisplayName("get() should return the current value for Integer")
        void get_shouldReturnCurrentValueForInteger() {
            Integer expected = 100;
            assertEquals(expected, mutableInteger.get(), "get() should return the initial integer value.");
            assertEquals(mutableInteger.getValue(), mutableInteger.get(), "get() should match getValue() for integer.");
        }

        @Test
        @DisplayName("get() should return the current value for Object")
        void get_shouldReturnCurrentValueForObject() {
            Object expected = mutableObject.getValue(); // Get the initial object reference
            assertEquals(expected, mutableObject.get(), "get() should return the initial object reference.");
            assertEquals(mutableObject.getValue(), mutableObject.get(), "get() should match getValue() for object.");
            assertSame(expected, mutableObject.get(), "get() should return the same object reference.");
        }

        @Test
        @DisplayName("get() should return null if value is null")
        void get_shouldReturnNullIfValueIsNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.get(), "get() should return null when the value is null.");
            assertNull(nullMutable.getValue(), "getValue() should return null when the value is null.");
            assertEquals(nullMutable.getValue(), nullMutable.get(), "get() should match getValue() for null.");
        }

        @Test
        @DisplayName("get() should return updated value after setValue()")
        void get_shouldReturnUpdatedValueAfterSetValue() {
            String newValue = "updated";
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.get(), "get() should return the updated string value.");
            assertEquals(mutableString.getValue(), mutableString.get(), "get() should match getValue() after update.");
        }
    }

    @Nested
    @DisplayName("getValue() method tests")
    class GetValueMethodTests {

        /**
         * abstract T getValue();
         * (No JML postcondition provided for getValue() itself, but it's implied to return the current state.)
         */

        @Test
        @DisplayName("getValue() should return the initial value for String")
        void getValue_shouldReturnInitialValueForString() {
            assertEquals("initial", mutableString.getValue(), "getValue() should return the initial string value.");
        }

        @Test
        @DisplayName("getValue() should return the initial value for Integer")
        void getValue_shouldReturnInitialValueForInteger() {
            assertEquals(100, mutableInteger.getValue(), "getValue() should return the initial integer value.");
        }

        @Test
        @DisplayName("getValue() should return the initial value for Object")
        void getValue_shouldReturnInitialValueForObject() {
            Object initialObject = mutableObject.getValue(); // Store the initial object reference
            assertNotNull(initialObject, "getValue() should return a non-null object initially.");
            // We can't assert equality without knowing the object's equals method, but we can assert reference equality
            // if we capture the initial object.
            // For this test, we just ensure it's not null and is the same instance as initially set.
            TestMutable<Object> tempMutable = new TestMutable<>(initialObject);
            assertSame(initialObject, tempMutable.getValue(), "getValue() should return the same object reference.");
        }

        @Test
        @DisplayName("getValue() should return null if initial value is null")
        void getValue_shouldReturnNullIfInitialValueIsNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.getValue(), "getValue() should return null when initialized with null.");
        }

        @Test
        @DisplayName("getValue() should return updated value after setValue()")
        void getValue_shouldReturnUpdatedValueAfterSetValue() {
            String newValue = "new value";
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.getValue(), "getValue() should return the updated string value.");

            Integer newInt = 200;
            mutableInteger.setValue(newInt);
            assertEquals(newInt, mutableInteger.getValue(), "getValue() should return the updated integer value.");

            Object newObject = new Object();
            mutableObject.setValue(newObject);
            assertSame(newObject, mutableObject.getValue(), "getValue() should return the updated object reference.");
        }
    }

    @Nested
    @DisplayName("setValue(T value) method tests")
    class SetValueMethodTests {

        /**
         * abstract void setValue(T value);
         * @ensures getValue() == value;
         */

        @Test
        @DisplayName("setValue() should update the value for String")
        void setValue_shouldUpdateValueForString() {
            String newValue = "hello";
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.getValue(), "setValue() should update the string value.");
            assertEquals(newValue, mutableString.get(), "get() should reflect the updated string value.");
        }

        @Test
        @DisplayName("setValue() should update the value for Integer")
        void setValue_shouldUpdateValueForInteger() {
            Integer newValue = 500;
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.getValue(), "setValue() should update the integer value.");
            assertEquals(newValue, mutableInteger.get(), "get() should reflect the updated integer value.");
        }

        @Test
        @DisplayName("setValue() should update the value for Object")
        void setValue_shouldUpdateValueForObject() {
            Object newValue = new Object();
            mutableObject.setValue(newValue);
            assertSame(newValue, mutableObject.getValue(), "setValue() should update the object reference.");
            assertSame(newValue, mutableObject.get(), "get() should reflect the updated object reference.");
        }

        @Test
        @DisplayName("setValue() should allow setting null for String")
        void setValue_shouldAllowSettingNullForString() {
            mutableString.setValue(null);
            assertNull(mutableString.getValue(), "setValue() should allow setting null for string.");
            assertNull(mutableString.get(), "get() should reflect null after setting null.");
        }

        @Test
        @DisplayName("setValue() should allow setting null for Integer")
        void setValue_shouldAllowSettingNullForInteger() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.getValue(), "setValue() should allow setting null for integer.");
            assertNull(mutableInteger.get(), "get() should reflect null after setting null.");
        }

        @Test
        @DisplayName("setValue() should allow setting null for Object")
        void setValue_shouldAllowSettingNullForObject() {
            mutableObject.setValue(null);
            assertNull(mutableObject.getValue(), "setValue() should allow setting null for object.");
            assertNull(mutableObject.get(), "get() should reflect null after setting null.");
        }

        @Test
        @DisplayName("setValue() should allow setting the same value for String")
        void setValue_shouldAllowSettingSameValueForString() {
            String initialValue = mutableString.getValue();
            mutableString.setValue(initialValue);
            assertEquals(initialValue, mutableString.getValue(), "setValue() should allow setting the same string value.");
        }

        @Test
        @DisplayName("setValue() should allow setting the same value for Object")
        void setValue_shouldAllowSettingSameValueForObject() {
            Object initialValue = mutableObject.getValue();
            mutableObject.setValue(initialValue);
            assertSame(initialValue, mutableObject.getValue(), "setValue() should allow setting the same object reference.");
        }

        @Test
        @DisplayName("setValue() should handle multiple updates correctly")
        void setValue_shouldHandleMultipleUpdatesCorrectly() {
            mutableString.setValue("first");
            assertEquals("first", mutableString.getValue());
            mutableString.setValue("second");
            assertEquals("second", mutableString.getValue());
            mutableString.setValue(null);
            assertNull(mutableString.getValue());
            mutableString.setValue("final");
            assertEquals("final", mutableString.getValue());
        }
    }
}