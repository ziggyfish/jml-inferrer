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
 * Unit tests for the {@link Mutable} interface.
 * This test class aims to cover normal behavior, edge cases, and potential failure scenarios
 * for the methods defined in the Mutable interface based on the provided JML specifications.
 *
 * Since Mutable is an abstract interface, we will test concrete implementations.
 * For the purpose of these tests, we will create a simple anonymous inner class
 * implementation of Mutable<T>.
 */
class MutableTestP3P3 {

    // A simple concrete implementation for testing purposes
    private static class TestMutable<T> implements Mutable<T> {
        private T value;

        public TestMutable(T initialValue) {
            this.value = initialValue;
        }

        @Override
        public T get() {
            // @ensures \result == this.value;
            return value;
        }

        @Override
        public T getValue() {
            // @ensures \result == this.value;
            return value;
        }

        @Override
        public void setValue(T value) {
            // @ensures this.value == value;
            this.value = value;
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
        @DisplayName("get() should return the current value")
        void testGetString() {
            assertEquals("initial", mutableString.get(), "get() should return the initial string value");
        }

        @Test
        @DisplayName("getValue() should return the current value")
        void testGetValueString() {
            assertEquals("initial", mutableString.getValue(), "getValue() should return the initial string value");
        }

        @Test
        @DisplayName("setValue() should update the value and get() should reflect it")
        void testSetString() {
            String newValue = "updated";
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.get(), "get() should return the updated string value");
            assertEquals(newValue, mutableString.getValue(), "getValue() should return the updated string value");
        }

        @Test
        @DisplayName("setValue() with null should update the value to null")
        void testSetStringToNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get(), "get() should return null after setting to null");
            assertNull(mutableString.getValue(), "getValue() should return null after setting to null");
        }

        @Test
        @DisplayName("setValue() with empty string should update the value to empty string")
        void testSetStringToEmpty() {
            String emptyString = "";
            mutableString.setValue(emptyString);
            assertEquals(emptyString, mutableString.get(), "get() should return empty string after setting to empty string");
            assertEquals(emptyString, mutableString.getValue(), "getValue() should return empty string after setting to empty string");
        }

        @Test
        @DisplayName("Multiple setValue() calls should update correctly")
        void testMultipleSetString() {
            mutableString.setValue("first");
            assertEquals("first", mutableString.get());
            mutableString.setValue("second");
            assertEquals("second", mutableString.get());
            mutableString.setValue("third");
            assertEquals("third", mutableString.get());
        }
    }

    @Nested
    @DisplayName("Tests for Mutable<Integer>")
    class IntegerMutableTests {
        private TestMutable<Integer> mutableInteger;

        @BeforeEach
        void setUp() {
            mutableInteger = new TestMutable<>(100);
        }

        @Test
        @DisplayName("get() should return the current integer value")
        void testGetInteger() {
            assertEquals(100, mutableInteger.get(), "get() should return the initial integer value");
        }

        @Test
        @DisplayName("getValue() should return the current integer value")
        void testGetValueInteger() {
            assertEquals(100, mutableInteger.getValue(), "getValue() should return the initial integer value");
        }

        @Test
        @DisplayName("setValue() should update the integer value and get() should reflect it")
        void testSetInteger() {
            Integer newValue = 200;
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.get(), "get() should return the updated integer value");
            assertEquals(newValue, mutableInteger.getValue(), "getValue() should return the updated integer value");
        }

        @Test
        @DisplayName("setValue() with null should update the integer value to null")
        void testSetIntegerToNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get(), "get() should return null after setting to null");
            assertNull(mutableInteger.getValue(), "getValue() should return null after setting to null");
        }

        @ParameterizedTest(name = "setValue({0}) should update the value")
        @ValueSource(ints = {0, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
        @DisplayName("setValue() with various integer values")
        void testSetIntegerEdgeCases(int value) {
            mutableInteger.setValue(value);
            assertEquals(value, mutableInteger.get());
            assertEquals(value, mutableInteger.getValue());
        }
    }

    @Nested
    @DisplayName("Tests for Mutable<Boolean>")
    class BooleanMutableTests {
        private TestMutable<Boolean> mutableBoolean;

        @BeforeEach
        void setUp() {
            mutableBoolean = new TestMutable<>(true);
        }

        @Test
        @DisplayName("get() should return the current boolean value")
        void testGetBoolean() {
            assertTrue(mutableBoolean.get(), "get() should return the initial boolean value");
        }

        @Test
        @DisplayName("getValue() should return the current boolean value")
        void testGetValueBoolean() {
            assertTrue(mutableBoolean.getValue(), "getValue() should return the initial boolean value");
        }

        @Test
        @DisplayName("setValue() should update the boolean value and get() should reflect it")
        void testSetBoolean() {
            Boolean newValue = false;
            mutableBoolean.setValue(newValue);
            assertEquals(newValue, mutableBoolean.get(), "get() should return the updated boolean value");
            assertEquals(newValue, mutableBoolean.getValue(), "getValue() should return the updated boolean value");
        }

        @Test
        @DisplayName("setValue() with null should update the boolean value to null")
        void testSetBooleanToNull() {
            mutableBoolean.setValue(null);
            assertNull(mutableBoolean.get(), "get() should return null after setting to null");
            assertNull(mutableBoolean.getValue(), "getValue() should return null after setting to null");
        }
    }

    @Nested
    @DisplayName("General Tests for Mutable with initial null value")
    class NullInitialValueTests {
        private TestMutable<Object> mutableObject;

        @BeforeEach
        void setUp() {
            mutableObject = new TestMutable<>(null);
        }

        @Test
        @DisplayName("get() should return null when initialized with null")
        void testGetInitialNull() {
            assertNull(mutableObject.get(), "get() should return null if initialized with null");
        }

        @Test
        @DisplayName("getValue() should return null when initialized with null")
        void testGetValueInitialNull() {
            assertNull(mutableObject.getValue(), "getValue() should return null if initialized with null");
        }

        @Test
        @DisplayName("setValue() from null to a non-null value should work")
        void testSetFromNullToNonNull() {
            String newValue = "hello";
            mutableObject.setValue(newValue);
            assertEquals(newValue, mutableObject.get(), "get() should return the new non-null value");
            assertEquals(newValue, mutableObject.getValue(), "getValue() should return the new non-null value");
        }

        @Test
        @DisplayName("setValue() from null to null should remain null")
        void testSetFromNullToNull() {
            mutableObject.setValue(null);
            assertNull(mutableObject.get(), "get() should remain null after setting null to null");
            assertNull(mutableObject.getValue(), "getValue() should remain null after setting null to null");
        }
    }

    @Nested
    @DisplayName("Tests for get() and getValue() consistency")
    class ConsistencyTests {
        private TestMutable<String> mutableString;

        @BeforeEach
        void setUp() {
            mutableString = new TestMutable<>("consistent");
        }

        @Test
        @DisplayName("get() and getValue() should always return the same value")
        void testGetAndGetValueConsistency() {
            assertEquals(mutableString.get(), mutableString.getValue(),
                    "get() and getValue() should return the same value");

            mutableString.setValue("new value");
            assertEquals(mutableString.get(), mutableString.getValue(),
                    "get() and getValue() should return the same value after update");

            mutableString.setValue(null);
            assertEquals(mutableString.get(), mutableString.getValue(),
                    "get() and getValue() should return the same value (null) after update to null");
        }
    }

    @Nested
    @DisplayName("Parameterized Tests for setValue()")
    class ParameterizedSetValueTests {
        private TestMutable<String> mutableString;

        @BeforeEach
        void setUp() {
            mutableString = new TestMutable<>("initial");
        }

        @ParameterizedTest(name = "setValue({0})")
        @ValueSource(strings = {"", "test", "another test", "12345", "!@#$%^&*()"})
        @NullSource
        @DisplayName("setValue() with various string values including null and empty")
        void testSetValueWithVariousStrings(String value) {
            mutableString.setValue(value);
            assertEquals(value, mutableString.get(), "get() should reflect the set value");
            assertEquals(value, mutableString.getValue(), "getValue() should reflect the set value");
        }
    }
}