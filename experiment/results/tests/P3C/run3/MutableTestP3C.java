package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.Mutable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the {@link Mutable} abstract class.
 * This test class focuses on the contract defined by the abstract methods
 * {@code get()}, {@code getValue()}, and {@code setValue(T value)}.
 * Since {@link Mutable} is abstract, we will test concrete implementations
 * provided by Apache Commons Lang, specifically {@link org.apache.commons.lang3.mutable.MutableObject}.
 *
 * JML Specifications:
 * T get();
 *   @ensures \result == getValue();
 *
 * abstract T getValue();
 *
 * abstract void setValue(T value);
 */
class MutableTestP3CP3C {

    // Helper class to test the abstract Mutable interface directly if needed,
    // but for practical purposes, we'll use a concrete implementation.
    // For this problem, we'll use MutableObject as a representative concrete class.

    @Nested
    @DisplayName("Tests for MutableObject<String>")
    class MutableObjectStringTests {

        private Mutable<String> mutableString;

        @BeforeEach
        void setUp() {
            mutableString = new org.apache.commons.lang3.mutable.MutableObject<>("initial");
        }

        @Test
        @DisplayName("get() returns the initial value")
        void testGet_initialValue() {
            assertEquals("initial", mutableString.get());
        }

        @Test
        @DisplayName("getValue() returns the initial value")
        void testGetValue_initialValue() {
            assertEquals("initial", mutableString.getValue());
        }

        @Test
        @DisplayName("get() and getValue() return the same value initially")
        void testGetAndGetValue_sameInitial() {
            assertEquals(mutableString.getValue(), mutableString.get());
        }

        @Test
        @DisplayName("setValue() updates the value correctly")
        void testSetValue_updatesValue() {
            String newValue = "updated";
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.get());
            assertEquals(newValue, mutableString.getValue());
        }

        @Test
        @DisplayName("get() and getValue() return the same value after update")
        void testGetAndGetValue_sameAfterUpdate() {
            String newValue = "after update";
            mutableString.setValue(newValue);
            assertEquals(mutableString.getValue(), mutableString.get());
        }

        @Test
        @DisplayName("setValue() with null value and then get() returns null")
        void testSetValue_nullValue() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with null and then update to non-null works")
        void testSetValue_nullThenNonNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get());

            String anotherValue = "not null anymore";
            mutableString.setValue(anotherValue);
            assertEquals(anotherValue, mutableString.get());
            assertEquals(anotherValue, mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with empty string works")
        void testSetValue_emptyString() {
            String emptyString = "";
            mutableString.setValue(emptyString);
            assertEquals(emptyString, mutableString.get());
            assertEquals(emptyString, mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with same value does not change anything but is allowed")
        void testSetValue_sameValue() {
            String originalValue = mutableString.get();
            mutableString.setValue(originalValue);
            assertEquals(originalValue, mutableString.get());
            assertEquals(originalValue, mutableString.getValue());
        }

        @Test
        @DisplayName("Multiple updates to setValue() are reflected correctly")
        void testSetValue_multipleUpdates() {
            mutableString.setValue("first");
            assertEquals("first", mutableString.get());

            mutableString.setValue("second");
            assertEquals("second", mutableString.get());

            mutableString.setValue("third");
            assertEquals("third", mutableString.get());
        }
    }

    @Nested
    @DisplayName("Tests for MutableObject<Integer>")
    class MutableObjectIntegerTests {

        private Mutable<Integer> mutableInteger;

        @BeforeEach
        void setUp() {
            mutableInteger = new org.apache.commons.lang3.mutable.MutableObject<>(10);
        }

        @Test
        @DisplayName("get() returns the initial integer value")
        void testGet_initialValue() {
            assertEquals(10, mutableInteger.get());
        }

        @Test
        @DisplayName("getValue() returns the initial integer value")
        void testGetValue_initialValue() {
            assertEquals(10, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() updates the integer value correctly")
        void testSetValue_updatesValue() {
            Integer newValue = 20;
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.get());
            assertEquals(newValue, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() with null integer value")
        void testSetValue_nullInteger() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
            assertNull(mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() with zero integer value")
        void testSetValue_zeroInteger() {
            mutableInteger.setValue(0);
            assertEquals(0, mutableInteger.get());
            assertEquals(0, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() with negative integer value")
        void testSetValue_negativeInteger() {
            mutableInteger.setValue(-5);
            assertEquals(-5, mutableInteger.get());
            assertEquals(-5, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() with MAX_VALUE integer value")
        void testSetValue_maxValueInteger() {
            mutableInteger.setValue(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, mutableInteger.get());
            assertEquals(Integer.MAX_VALUE, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() with MIN_VALUE integer value")
        void testSetValue_minValueInteger() {
            mutableInteger.setValue(Integer.MIN_VALUE);
            assertEquals(Integer.MIN_VALUE, mutableInteger.get());
            assertEquals(Integer.MIN_VALUE, mutableInteger.getValue());
        }
    }

    @Nested
    @DisplayName("Tests for MutableObject<Object>")
    class MutableObjectObjectTests {

        private Mutable<Object> mutableObject;

        @BeforeEach
        void setUp() {
            mutableObject = new org.apache.commons.lang3.mutable.MutableObject<>(new Object());
        }

        @Test
        @DisplayName("setValue() with a different object instance")
        void testSetValue_differentObject() {
            Object originalObject = mutableObject.get();
            Object newObject = new Object();
            assertNotSame(originalObject, newObject); // Ensure they are different instances

            mutableObject.setValue(newObject);
            assertSame(newObject, mutableObject.get());
            assertSame(newObject, mutableObject.getValue());
            assertNotSame(originalObject, mutableObject.get());
        }

        @Test
        @DisplayName("setValue() with the same object instance")
        void testSetValue_sameObject() {
            Object originalObject = mutableObject.get();
            mutableObject.setValue(originalObject);
            assertSame(originalObject, mutableObject.get());
            assertSame(originalObject, mutableObject.getValue());
        }
    }
}