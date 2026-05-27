package org.apache.commons.lang3.mutable.p3c;

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
 * Comprehensive unit tests for the {@link Mutable} abstract class.
 * This test class covers normal behavior, edge cases, and potential failure scenarios
 * for the {@code get()}, {@code getValue()}, and {@code setValue()} methods.
 *
 * Since {@link Mutable} is an abstract class, we will test it using a concrete
 * anonymous inner class implementation for various types.
 */
class MutableTestP3CP3C {

    // Helper class to create a concrete Mutable<T> instance for testing
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

    @Nested
    @DisplayName("Tests for Mutable<Integer>")
    class IntegerMutableTests {
        private TestMutable<Integer> mutableInteger;

        @BeforeEach
        void setUp() {
            mutableInteger = new TestMutable<>(0);
        }

        @Test
        @DisplayName("get(): Should return the initial integer value")
        void testGetInitialInteger() {
            assertEquals(0, mutableInteger.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial integer value")
        void testGetValueInitialInteger() {
            assertEquals(0, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() and get(): Should update and return the new integer value")
        void testSetValueAndGetInteger() {
            mutableInteger.setValue(10);
            assertEquals(10, mutableInteger.get());
        }

        @Test
        @DisplayName("setValue() and getValue(): Should update and return the new integer value")
        void testSetValueAndGetValueInteger() {
            mutableInteger.setValue(25);
            assertEquals(25, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null integer value")
        void testSetNullInteger() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
            assertNull(mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting negative integer value")
        void testSetNegativeInteger() {
            mutableInteger.setValue(-5);
            assertEquals(-5, mutableInteger.get());
        }

        @Test
        @DisplayName("setValue(): Should allow setting large integer value")
        void testSetLargeInteger() {
            mutableInteger.setValue(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, mutableInteger.get());
        }

        @Test
        @DisplayName("setValue(): Should allow setting small integer value")
        void testSetSmallInteger() {
            mutableInteger.setValue(Integer.MIN_VALUE);
            assertEquals(Integer.MIN_VALUE, mutableInteger.get());
        }

        @Test
        @DisplayName("setValue(): Should allow setting zero integer value")
        void testSetZeroInteger() {
            mutableInteger.setValue(0);
            assertEquals(0, mutableInteger.get());
        }

        @Test
        @DisplayName("Multiple setValue() calls: Should always reflect the last set value")
        void testMultipleSetInteger() {
            mutableInteger.setValue(1);
            assertEquals(1, mutableInteger.get());
            mutableInteger.setValue(2);
            assertEquals(2, mutableInteger.get());
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
            mutableInteger.setValue(100);
            assertEquals(100, mutableInteger.get());
        }
    }

    @Nested
    @DisplayName("Tests for Mutable<String>")
    class StringMutableTests {
        private TestMutable<String> mutableString;

        @BeforeEach
        void setUp() {
            mutableString = new TestMutable<>("initial");
        }

        @Test
        @DisplayName("get(): Should return the initial string value")
        void testGetInitialString() {
            assertEquals("initial", mutableString.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial string value")
        void testGetValueInitialString() {
            assertEquals("initial", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() and get(): Should update and return the new string value")
        void testSetValueAndGetString() {
            mutableString.setValue("new value");
            assertEquals("new value", mutableString.get());
        }

        @Test
        @DisplayName("setValue() and getValue(): Should update and return the new string value")
        void testSetValueAndGetValueString() {
            mutableString.setValue("another value");
            assertEquals("another value", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null string value")
        void testSetNullString() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting empty string value")
        void testSetEmptyString() {
            mutableString.setValue("");
            assertEquals("", mutableString.get());
        }

        @Test
        @DisplayName("setValue(): Should allow setting string with special characters")
        void testSetSpecialCharString() {
            String specialString = "!@#$%^&*()_+{}[]|\\:;\"'<>,.?/~`";
            mutableString.setValue(specialString);
            assertEquals(specialString, mutableString.get());
        }

        @Test
        @DisplayName("setValue(): Should allow setting long string value")
        void testSetLongString() {
            String longString = "a".repeat(1000);
            mutableString.setValue(longString);
            assertEquals(longString, mutableString.get());
        }

        @Test
        @DisplayName("Multiple setValue() calls: Should always reflect the last set string value")
        void testMultipleSetString() {
            mutableString.setValue("first");
            assertEquals("first", mutableString.get());
            mutableString.setValue("second");
            assertEquals("second", mutableString.get());
            mutableString.setValue(null);
            assertNull(mutableString.get());
            mutableString.setValue("final");
            assertEquals("final", mutableString.get());
        }
    }

    @Nested
    @DisplayName("Tests for Mutable<Object>")
    class ObjectMutableTests {
        private TestMutable<Object> mutableObject;
        private Object obj1 = new Object();
        private Object obj2 = new Object();

        @BeforeEach
        void setUp() {
            mutableObject = new TestMutable<>(obj1);
        }

        @Test
        @DisplayName("get(): Should return the initial object value")
        void testGetInitialObject() {
            assertSame(obj1, mutableObject.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial object value")
        void testGetValueInitialObject() {
            assertSame(obj1, mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue() and get(): Should update and return the new object value")
        void testSetValueAndGetObject() {
            mutableObject.setValue(obj2);
            assertSame(obj2, mutableObject.get());
        }

        @Test
        @DisplayName("setValue() and getValue(): Should update and return the new object value")
        void testSetValueAndGetValueObject() {
            mutableObject.setValue(obj2);
            assertSame(obj2, mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null object value")
        void testSetNullObject() {
            mutableObject.setValue(null);
            assertNull(mutableObject.get());
            assertNull(mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting different object types")
        void testSetDifferentObjectType() {
            mutableObject.setValue(123); // Integer
            assertEquals(123, mutableObject.get());
            mutableObject.setValue("hello"); // String
            assertEquals("hello", mutableObject.get());
            mutableObject.setValue(true); // Boolean
            assertEquals(true, mutableObject.get());
        }
    }

    @Nested
    @DisplayName("Parameterized Tests for Mutable<Integer>")
    class ParameterizedIntegerMutableTests {

        @ParameterizedTest(name = "setValue({0}) and get() should return {0}")
        @ValueSource(ints = {0, 1, -1, 100, -100, Integer.MAX_VALUE, Integer.MIN_VALUE})
        @DisplayName("setValue() and get() with various integer values")
        void testSetValueAndGetWithVariousIntegers(int value) {
            TestMutable<Integer> mutableInteger = new TestMutable<>(0);
            mutableInteger.setValue(value);
            assertEquals(value, mutableInteger.get());
            assertEquals(value, mutableInteger.getValue());
        }

        @ParameterizedTest(name = "setValue({0}) and get() should return {0}")
        @NullSource
        @DisplayName("setValue() and get() with null integer value")
        void testSetValueAndGetWithNullInteger(Integer value) {
            TestMutable<Integer> mutableInteger = new TestMutable<>(10);
            mutableInteger.setValue(value);
            assertNull(mutableInteger.get());
            assertNull(mutableInteger.getValue());
        }
    }

    @Nested
    @DisplayName("Parameterized Tests for Mutable<String>")
    class ParameterizedStringMutableTests {

        @ParameterizedTest(name = "setValue(\"{0}\") and get() should return \"{0}\"")
        @ValueSource(strings = {"", "hello", "world", "12345", "!@#$%", "long string ".repeat(10)})
        @DisplayName("setValue() and get() with various string values")
        void testSetValueAndGetWithVariousStrings(String value) {
            TestMutable<String> mutableString = new TestMutable<>("initial");
            mutableString.setValue(value);
            assertEquals(value, mutableString.get());
            assertEquals(value, mutableString.getValue());
        }

        @ParameterizedTest(name = "setValue({0}) and get() should return {0}")
        @NullSource
        @DisplayName("setValue() and get() with null string value")
        void testSetValueAndGetWithNullString(String value) {
            TestMutable<String> mutableString = new TestMutable<>("not null");
            mutableString.setValue(value);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());
        }
    }

    @Nested
    @DisplayName("General Behavior Tests")
    class GeneralBehaviorTests {

        @Test
        @DisplayName("get() and getValue() should return the same instance")
        void testGetAndGetValueReturnSameInstance() {
            TestMutable<String> mutableString = new TestMutable<>("test");
            assertSame(mutableString.get(), mutableString.getValue());

            TestMutable<Integer> mutableInteger = new TestMutable<>(123);
            assertSame(mutableInteger.get(), mutableInteger.getValue());

            TestMutable<Object> mutableObject = new TestMutable<>(new Object());
            assertSame(mutableObject.get(), mutableObject.getValue());
        }

        @Test
        @DisplayName("Initial value can be null")
        void testInitialValueCanBeNull() {
            TestMutable<String> mutableString = new TestMutable<>(null);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());

            TestMutable<Integer> mutableInteger = new TestMutable<>(null);
            assertNull(mutableInteger.get());
            assertNull(mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() with same value should not change behavior")
        void testSetValueWithSameValue() {
            TestMutable<String> mutableString = new TestMutable<>("same");
            String initialValue = mutableString.get();
            mutableString.setValue("same");
            assertSame(initialValue, mutableString.get()); // For String literals, it might be same instance
            assertEquals("same", mutableString.get());

            TestMutable<Integer> mutableInteger = new TestMutable<>(10);
            Integer initialInt = mutableInteger.get();
            mutableInteger.setValue(10);
            assertSame(initialInt, mutableInteger.get()); // For Integer caching, it might be same instance
            assertEquals(10, mutableInteger.get());

            Object obj = new Object();
            TestMutable<Object> mutableObject = new TestMutable<>(obj);
            mutableObject.setValue(obj);
            assertSame(obj, mutableObject.get());
        }
    }
}