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
 * This class tests the contract defined by the JML specifications for
 * {@code get()}, {@code getValue()}, and {@code setValue(T value)}.
 *
 * Since Mutable is an abstract class, we will use a concrete anonymous
 * inner class implementation for testing.
 */
class MutableTestP3CP3C {

    // A concrete implementation of Mutable for testing purposes
    private static class TestMutable<T> extends Mutable<T> {
        private T value;

        public TestMutable(T initialValue) {
            this.value = initialValue;
        }

        @Override
        public T getValue() {
            // @ensures \result == this.value; (Implicitly handled by direct access)
            return value;
        }

        @Override
        public void setValue(T value) {
            // @ensures this.value == value;
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
        @DisplayName("get() should return the initial value for String")
        void get_shouldReturnInitialValue_String() {
            assertEquals("initial", mutableString.get());
        }

        @Test
        @DisplayName("get() should return the initial value for Integer")
        void get_shouldReturnInitialValue_Integer() {
            assertEquals(123, mutableInteger.get());
        }

        @Test
        @DisplayName("get() should return the initial value for Object")
        void get_shouldReturnInitialValue_Object() {
            Object initialObject = mutableObject.get(); // Store reference
            assertNotNull(initialObject);
            // Verify it's the same object, not just an equal one
            assertSame(initialObject, mutableObject.getValue());
        }

        @Test
        @DisplayName("get() should return null if initialized with null")
        void get_shouldReturnNull_ifInitializedWithNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.get());
        }

        @Test
        @DisplayName("get() should return the updated value after setValue for String")
        void get_shouldReturnUpdatedValue_String() {
            mutableString.setValue("updated");
            assertEquals("updated", mutableString.get());
        }

        @Test
        @DisplayName("get() should return the updated value after setValue for Integer")
        void get_shouldReturnUpdatedValue_Integer() {
            mutableInteger.setValue(456);
            assertEquals(456, mutableInteger.get());
        }

        @Test
        @DisplayName("get() should return null after setValue(null)")
        void get_shouldReturnNull_afterSetToNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
        }
    }

    @Nested
    @DisplayName("getValue() method tests")
    class GetValueMethodTests {

        @Test
        @DisplayName("getValue() should return the initial value for String")
        void getValue_shouldReturnInitialValue_String() {
            assertEquals("initial", mutableString.getValue());
        }

        @Test
        @DisplayName("getValue() should return the initial value for Integer")
        void getValue_shouldReturnInitialValue_Integer() {
            assertEquals(123, mutableInteger.getValue());
        }

        @Test
        @DisplayName("getValue() should return the initial value for Object")
        void getValue_shouldReturnInitialValue_Object() {
            Object initialObject = mutableObject.getValue(); // Store reference
            assertNotNull(initialObject);
            // Verify it's the same object, not just an equal one
            assertSame(initialObject, mutableObject.get());
        }

        @Test
        @DisplayName("getValue() should return null if initialized with null")
        void getValue_shouldReturnNull_ifInitializedWithNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.getValue());
        }

        @Test
        @DisplayName("getValue() should return the updated value after setValue for String")
        void getValue_shouldReturnUpdatedValue_String() {
            mutableString.setValue("updated");
            assertEquals("updated", mutableString.getValue());
        }

        @Test
        @DisplayName("getValue() should return the updated value after setValue for Integer")
        void getValue_shouldReturnUpdatedValue_Integer() {
            mutableInteger.setValue(456);
            assertEquals(456, mutableInteger.getValue());
        }

        @Test
        @DisplayName("getValue() should return null after setValue(null)")
        void getValue_shouldReturnNull_afterSetToNull() {
            mutableString.setValue(null);
            assertNull(mutableString.getValue());
        }
    }

    @Nested
    @DisplayName("setValue(T value) method tests")
    class SetValueMethodTests {

        @ParameterizedTest
        @ValueSource(strings = {"new value", "", "another value with spaces"})
        @DisplayName("setValue() should update the value for String with non-null values")
        void setValue_shouldUpdateValue_String(String newValue) {
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.getValue());
            assertEquals(newValue, mutableString.get()); // Also check get()
        }

        @ParameterizedTest
        @NullSource
        @DisplayName("setValue() should update the value for String with null")
        void setValue_shouldUpdateValue_String_toNull(String newValue) {
            mutableString.setValue(newValue);
            assertNull(mutableString.getValue());
            assertNull(mutableString.get()); // Also check get()
        }

        @ParameterizedTest
        @ValueSource(ints = {0, 1, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
        @DisplayName("setValue() should update the value for Integer with various values")
        void setValue_shouldUpdateValue_Integer(int newValue) {
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.getValue());
            assertEquals(newValue, mutableInteger.get()); // Also check get()
        }

        @Test
        @DisplayName("setValue() should update the value for Integer with null")
        void setValue_shouldUpdateValue_Integer_toNull() {
            // Integer is a wrapper type, so it can be null
            mutableInteger.setValue(null);
            assertNull(mutableInteger.getValue());
            assertNull(mutableInteger.get());
        }

        @Test
        @DisplayName("setValue() should update the value for Object with a new object")
        void setValue_shouldUpdateValue_Object() {
            Object newObject = new Object();
            mutableObject.setValue(newObject);
            assertSame(newObject, mutableObject.getValue());
            assertSame(newObject, mutableObject.get());
        }

        @Test
        @DisplayName("setValue() should update the value for Object with null")
        void setValue_shouldUpdateValue_Object_toNull() {
            mutableObject.setValue(null);
            assertNull(mutableObject.getValue());
            assertNull(mutableObject.get());
        }

        @Test
        @DisplayName("setValue() should allow setting the same value again")
        void setValue_shouldAllowSettingSameValue() {
            String initialValue = mutableString.getValue();
            mutableString.setValue(initialValue);
            assertEquals(initialValue, mutableString.getValue());
            assertEquals(initialValue, mutableString.get());
        }

        @Test
        @DisplayName("setValue() should allow setting null to null")
        void setValue_shouldAllowSettingNullToNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            nullMutable.setValue(null);
            assertNull(nullMutable.getValue());
            assertNull(nullMutable.get());
        }

        @Test
        @DisplayName("setValue() should handle multiple updates correctly")
        void setValue_shouldHandleMultipleUpdates() {
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

    @Test
    @DisplayName("toString() method should reflect the current value")
    void toString_shouldReflectCurrentValue() {
        assertEquals("initial", mutableString.toString());
        mutableString.setValue("changed");
        assertEquals("changed", mutableString.toString());
        mutableString.setValue(null);
        assertEquals("null", mutableString.toString()); // Default for null
    }

    @Test
    @DisplayName("equals() and hashCode() should behave consistently with value")
    void equalsAndHashCode_shouldBeConsistentWithValue() {
        TestMutable<String> mutable1 = new TestMutable<>("test");
        TestMutable<String> mutable2 = new TestMutable<>("test");
        TestMutable<String> mutable3 = new TestMutable<>("different");
        TestMutable<String> mutableNull1 = new TestMutable<>(null);
        TestMutable<String> mutableNull2 = new TestMutable<>(null);

        // equals
        assertEquals(mutable1, mutable2);
        assertNotEquals(mutable1, mutable3);
        assertNotEquals(mutable1, mutableNull1);
        assertEquals(mutableNull1, mutableNull2);

        // hashCode
        assertEquals(mutable1.hashCode(), mutable2.hashCode());
        assertNotEquals(mutable1.hashCode(), mutable3.hashCode());
        assertEquals(mutableNull1.hashCode(), mutableNull2.hashCode());

        // Change value and re-check
        mutable1.setValue("different");
        assertEquals(mutable1, mutable3);
        assertEquals(mutable1.hashCode(), mutable3.hashCode());
    }
}