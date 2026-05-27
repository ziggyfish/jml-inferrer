package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.Mutable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive unit tests for the {@link Mutable} abstract class.
 * These tests cover normal behavior, edge cases, and potential failure scenarios
 * for the specified methods: get(), getValue(), and setValue(T value).
 *
 * Since Mutable is an abstract class, we will test it using a concrete anonymous
 * subclass for instantiation.
 */
class MutableTestP3CP3C {

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
        mutableInteger = new TestMutable<>(123);
        mutableObject = new TestMutable<>(new Object());
    }

    @Nested
    @DisplayName("get() method tests")
    class GetMethodTests {

        @Test
        @DisplayName("get() returns the initial value for String")
        void testGetStringInitialValue() {
            assertEquals("initial", mutableString.get(), "get() should return the initial String value.");
        }

        @Test
        @DisplayName("get() returns the initial value for Integer")
        void testGetIntegerInitialValue() {
            assertEquals(123, mutableInteger.get(), "get() should return the initial Integer value.");
        }

        @Test
        @DisplayName("get() returns the initial value for Object")
        void testGetObjectInitialValue() {
            assertNotNull(mutableObject.get(), "get() should return a non-null initial Object value.");
            // We can't assert equality for a new Object without overriding equals/hashCode,
            // but we can check if it's the same instance after setting.
        }

        @Test
        @DisplayName("get() returns null if initialized with null")
        void testGetNullInitialValue() {
            TestMutable<String> mutableNull = new TestMutable<>(null);
            assertNull(mutableNull.get(), "get() should return null if initialized with null.");
        }

        @Test
        @DisplayName("get() returns the updated value after setValue for String")
        void testGetStringAfterSetValue() {
            mutableString.setValue("updated");
            assertEquals("updated", mutableString.get(), "get() should return the updated String value.");
        }

        @Test
        @DisplayName("get() returns the updated value after setValue for Integer")
        void testGetIntegerAfterSetValue() {
            mutableInteger.setValue(456);
            assertEquals(456, mutableInteger.get(), "get() should return the updated Integer value.");
        }

        @Test
        @DisplayName("get() returns null after setting to null")
        void testGetAfterSettingToNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get(), "get() should return null after setting value to null.");
        }
    }

    @Nested
    @DisplayName("getValue() method tests")
    class GetValueMethodTests {

        @Test
        @DisplayName("getValue() returns the initial value for String")
        void testGetValueStringInitialValue() {
            assertEquals("initial", mutableString.getValue(), "getValue() should return the initial String value.");
        }

        @Test
        @DisplayName("getValue() returns the initial value for Integer")
        void testGetValueIntegerInitialValue() {
            assertEquals(123, mutableInteger.getValue(), "getValue() should return the initial Integer value.");
        }

        @Test
        @DisplayName("getValue() returns the initial value for Object")
        void testGetValueObjectInitialValue() {
            assertNotNull(mutableObject.getValue(), "getValue() should return a non-null initial Object value.");
        }

        @Test
        @DisplayName("getValue() returns null if initialized with null")
        void testGetValueNullInitialValue() {
            TestMutable<String> mutableNull = new TestMutable<>(null);
            assertNull(mutableNull.getValue(), "getValue() should return null if initialized with null.");
        }

        @Test
        @DisplayName("getValue() returns the updated value after setValue for String")
        void testGetValueStringAfterSetValue() {
            mutableString.setValue("new value");
            assertEquals("new value", mutableString.getValue(), "getValue() should return the updated String value.");
        }

        @Test
        @DisplayName("getValue() returns the updated value after setValue for Integer")
        void testGetValueIntegerAfterSetValue() {
            mutableInteger.setValue(789);
            assertEquals(789, mutableInteger.getValue(), "getValue() should return the updated Integer value.");
        }

        @Test
        @DisplayName("getValue() returns null after setting to null")
        void testGetValueAfterSettingToNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.getValue(), "getValue() should return null after setting value to null.");
        }

        @Test
        @DisplayName("getValue() returns the same instance for objects")
        void testGetValueObjectInstance() {
            Object obj = new Object();
            mutableObject.setValue(obj);
            assertSame(obj, mutableObject.getValue(), "getValue() should return the same object instance.");
        }
    }

    @Nested
    @DisplayName("setValue(T value) method tests")
    class SetValueMethodTests {

        @Test
        @DisplayName("setValue() updates the value for String")
        void testSetValueString() {
            String newValue = "hello world";
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.getValue(), "setValue() should update the String value.");
            assertEquals(newValue, mutableString.get(), "get() should reflect the updated String value.");
        }

        @Test
        @DisplayName("setValue() updates the value for Integer")
        void testSetValueInteger() {
            Integer newValue = 999;
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.getValue(), "setValue() should update the Integer value.");
            assertEquals(newValue, mutableInteger.get(), "get() should reflect the updated Integer value.");
        }

        @Test
        @DisplayName("setValue() updates the value for Object")
        void testSetValueObject() {
            Object newObj = new Object();
            mutableObject.setValue(newObj);
            assertSame(newObj, mutableObject.getValue(), "setValue() should update the Object reference.");
            assertSame(newObj, mutableObject.get(), "get() should reflect the updated Object reference.");
        }

        @Test
        @DisplayName("setValue() allows setting value to null for String")
        void testSetValueStringToNull() {
            mutableString.setValue(null);
            assertNull(mutableString.getValue(), "setValue() should allow setting String value to null.");
            assertNull(mutableString.get(), "get() should reflect null after setting String value to null.");
        }

        @Test
        @DisplayName("setValue() allows setting value to null for Integer")
        void testSetValueIntegerToNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.getValue(), "setValue() should allow setting Integer value to null.");
            assertNull(mutableInteger.get(), "get() should reflect null after setting Integer value to null.");
        }

        @Test
        @DisplayName("setValue() allows setting value to null for Object")
        void testSetValueObjectToNull() {
            mutableObject.setValue(null);
            assertNull(mutableObject.getValue(), "setValue() should allow setting Object value to null.");
            assertNull(mutableObject.get(), "get() should reflect null after setting Object value to null.");
        }

        @Test
        @DisplayName("setValue() allows setting value multiple times")
        void testSetValueMultipleTimes() {
            mutableString.setValue("first");
            assertEquals("first", mutableString.getValue());
            mutableString.setValue("second");
            assertEquals("second", mutableString.getValue());
            mutableString.setValue("third");
            assertEquals("third", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with the same value should not change the value (identity check for objects)")
        void testSetValueWithSameObject() {
            Object initialObj = mutableObject.getValue();
            mutableObject.setValue(initialObj);
            assertSame(initialObj, mutableObject.getValue(), "Setting the same object should maintain the reference.");
        }

        @Test
        @DisplayName("setValue() with the same value should not change the value (equality check for primitives/strings)")
        void testSetValueWithSameString() {
            String initialString = mutableString.getValue();
            mutableString.setValue(initialString);
            assertEquals(initialString, mutableString.getValue(), "Setting the same string should maintain the value.");
        }
    }

    @Nested
    @DisplayName("Combined Operations Tests")
    class CombinedOperationsTests {

        @Test
        @DisplayName("Set and Get multiple times with different types")
        void testSetAndGetMixedTypes() {
            TestMutable<Number> mutableNumber = new TestMutable<>(10);
            assertEquals(10, mutableNumber.get());
            assertEquals(10, mutableNumber.getValue());

            mutableNumber.setValue(3.14);
            assertEquals(3.14, mutableNumber.get());
            assertEquals(3.14, mutableNumber.getValue());

            mutableNumber.setValue(null);
            assertNull(mutableNumber.get());
            assertNull(mutableNumber.getValue());

            mutableNumber.setValue(100L);
            assertEquals(100L, mutableNumber.get());
            assertEquals(100L, mutableNumber.getValue());
        }

        @Test
        @DisplayName("Verify get() and getValue() return the same instance for objects")
        void testGetAndGetValueSameInstance() {
            Object obj = new Object();
            mutableObject.setValue(obj);
            assertSame(mutableObject.get(), mutableObject.getValue(), "get() and getValue() should return the same object instance.");
        }

        @Test
        @DisplayName("Verify get() and getValue() return the same value for primitives/strings")
        void testGetAndGetValueSameValue() {
            mutableString.setValue("test");
            assertEquals(mutableString.get(), mutableString.getValue(), "get() and getValue() should return the same string value.");

            mutableInteger.setValue(500);
            assertEquals(mutableInteger.get(), mutableInteger.getValue(), "get() and getValue() should return the same integer value.");
        }
    }
}