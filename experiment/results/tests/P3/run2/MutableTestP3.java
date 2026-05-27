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
 * Comprehensive unit tests for the Mutable interface, covering normal behavior, edge cases,
 * and potential failure scenarios for its specified methods: get(), getValue(), and setValue().
 *
 * Since Mutable is an abstract interface, we will test concrete implementations.
 * For this purpose, we'll create a simple anonymous inner class implementation for testing.
 */
class MutableTestP3P3 {

    // A concrete implementation of Mutable for testing purposes
    private static class TestMutable<T> implements Mutable<T> {
        private T value;

        public TestMutable(T initialValue) {
            this.value = initialValue;
        }

        @Override
        public T get() {
            return value;
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
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            TestMutable<?> other = (TestMutable<?>) obj;
            if (this.value == null) {
                return other.value == null;
            }
            return this.value.equals(other.value);
        }

        @Override
        public int hashCode() {
            return value == null ? 0 : value.hashCode();
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

        @Test
        @DisplayName("get() should return the initial value for String")
        void get_shouldReturnInitialStringValue() {
            assertEquals("initial", mutableString.get());
        }

        @Test
        @DisplayName("get() should return the initial value for Integer")
        void get_shouldReturnInitialIntegerValue() {
            assertEquals(100, mutableInteger.get());
        }

        @Test
        @DisplayName("get() should return the initial value for Object")
        void get_shouldReturnInitialObjectValue() {
            assertNotNull(mutableObject.get());
        }

        @Test
        @DisplayName("get() should return null if initialized with null")
        void get_shouldReturnNullIfInitializedWithNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.get());
        }

        @Test
        @DisplayName("get() should return the updated value after setValue for String")
        void get_shouldReturnUpdatedStringValue() {
            mutableString.setValue("updated");
            assertEquals("updated", mutableString.get());
        }

        @Test
        @DisplayName("get() should return the updated value after setValue for Integer")
        void get_shouldReturnUpdatedIntegerValue() {
            mutableInteger.setValue(200);
            assertEquals(200, mutableInteger.get());
        }

        @Test
        @DisplayName("get() should return null after setValue(null)")
        void get_shouldReturnNullAfterSettingNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
        }
    }

    @Nested
    @DisplayName("getValue() method tests")
    class GetValueMethodTests {

        @Test
        @DisplayName("getValue() should return the initial value for String")
        void getValue_shouldReturnInitialStringValue() {
            assertEquals("initial", mutableString.getValue());
        }

        @Test
        @DisplayName("getValue() should return the initial value for Integer")
        void getValue_shouldReturnInitialIntegerValue() {
            assertEquals(100, mutableInteger.getValue());
        }

        @Test
        @DisplayName("getValue() should return the initial value for Object")
        void getValue_shouldReturnInitialObjectValue() {
            assertNotNull(mutableObject.getValue());
        }

        @Test
        @DisplayName("getValue() should return null if initialized with null")
        void getValue_shouldReturnNullIfInitializedWithNull() {
            TestMutable<String> nullMutable = new TestMutable<>(null);
            assertNull(nullMutable.getValue());
        }

        @Test
        @DisplayName("getValue() should return the updated value after setValue for String")
        void getValue_shouldReturnUpdatedStringValue() {
            mutableString.setValue("updated");
            assertEquals("updated", mutableString.getValue());
        }

        @Test
        @DisplayName("getValue() should return the updated value after setValue for Integer")
        void getValue_shouldReturnUpdatedIntegerValue() {
            mutableInteger.setValue(200);
            assertEquals(200, mutableInteger.getValue());
        }

        @Test
        @DisplayName("getValue() should return null after setValue(null)")
        void getValue_shouldReturnNullAfterSettingNull() {
            mutableString.setValue(null);
            assertNull(mutableString.getValue());
        }
    }

    @Nested
    @DisplayName("setValue(T value) method tests")
    class SetValueMethodTests {

        @ParameterizedTest
        @ValueSource(strings = {"new value", "", "another value with spaces"})
        @DisplayName("setValue() should update the String value correctly")
        void setValue_shouldUpdateStringValue(String newValue) {
            mutableString.setValue(newValue);
            assertEquals(newValue, mutableString.get());
            assertEquals(newValue, mutableString.getValue());
        }

        @ParameterizedTest
        @NullSource
        @DisplayName("setValue() should allow setting String value to null")
        void setValue_shouldAllowSettingStringValueToNull(String nullValue) {
            mutableString.setValue(nullValue);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());
        }

        @ParameterizedTest
        @ValueSource(ints = {0, 1, -1, Integer.MAX_VALUE, Integer.MIN_VALUE})
        @DisplayName("setValue() should update the Integer value correctly")
        void setValue_shouldUpdateIntegerValue(int newValue) {
            mutableInteger.setValue(newValue);
            assertEquals(newValue, mutableInteger.get());
            assertEquals(newValue, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() should allow setting Integer value to null")
        void setValue_shouldAllowSettingIntegerValueToNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
            assertNull(mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue() should update the Object value correctly")
        void setValue_shouldUpdateObjectValue() {
            Object newObject = new Object();
            mutableObject.setValue(newObject);
            assertSame(newObject, mutableObject.get());
            assertSame(newObject, mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue() should allow setting Object value to null")
        void setValue_shouldAllowSettingObjectValueToNull() {
            mutableObject.setValue(null);
            assertNull(mutableObject.get());
            assertNull(mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue() should handle multiple updates correctly")
        void setValue_shouldHandleMultipleUpdates() {
            mutableString.setValue("first update");
            assertEquals("first update", mutableString.get());

            mutableString.setValue("second update");
            assertEquals("second update", mutableString.get());

            mutableString.setValue(null);
            assertNull(mutableString.get());

            mutableString.setValue("final update");
            assertEquals("final update", mutableString.get());
        }

        @Test
        @DisplayName("setValue() should not affect other Mutable instances")
        void setValue_shouldNotAffectOtherInstances() {
            TestMutable<String> anotherMutable = new TestMutable<>("another");
            mutableString.setValue("changed");

            assertEquals("changed", mutableString.get());
            assertEquals("another", anotherMutable.get()); // Ensure it's unchanged
        }
    }

    @Nested
    @DisplayName("Combined behavior tests")
    class CombinedBehaviorTests {

        @Test
        @DisplayName("Initial state and subsequent changes for String")
        void combined_stringBehavior() {
            TestMutable<String> mutable = new TestMutable<>("start");
            assertEquals("start", mutable.get());
            assertEquals("start", mutable.getValue());

            mutable.setValue("middle");
            assertEquals("middle", mutable.get());
            assertEquals("middle", mutable.getValue());

            mutable.setValue(null);
            assertNull(mutable.get());
            assertNull(mutable.getValue());

            mutable.setValue("end");
            assertEquals("end", mutable.get());
            assertEquals("end", mutable.getValue());
        }

        @Test
        @DisplayName("Initial state and subsequent changes for Integer")
        void combined_integerBehavior() {
            TestMutable<Integer> mutable = new TestMutable<>(1);
            assertEquals(1, mutable.get());
            assertEquals(1, mutable.getValue());

            mutable.setValue(100);
            assertEquals(100, mutable.get());
            assertEquals(100, mutable.getValue());

            mutable.setValue(null);
            assertNull(mutable.get());
            assertNull(mutable.getValue());

            mutable.setValue(-50);
            assertEquals(-50, mutable.get());
            assertEquals(-50, mutable.getValue());
        }

        @Test
        @DisplayName("Initial state and subsequent changes for Object")
        void combined_objectBehavior() {
            Object obj1 = new Object();
            Object obj2 = new Object();

            TestMutable<Object> mutable = new TestMutable<>(obj1);
            assertSame(obj1, mutable.get());
            assertSame(obj1, mutable.getValue());

            mutable.setValue(obj2);
            assertSame(obj2, mutable.get());
            assertSame(obj2, mutable.getValue());

            mutable.setValue(null);
            assertNull(mutable.get());
            assertNull(mutable.getValue());

            Object obj3 = new Object();
            mutable.setValue(obj3);
            assertSame(obj3, mutable.get());
            assertSame(obj3, mutable.getValue());
        }
    }

    @Nested
    @DisplayName("toString(), equals(), hashCode() tests (for completeness of TestMutable)")
    class UtilityMethodTests {

        @Test
        @DisplayName("toString() should return string representation of value")
        void toString_shouldReturnStringRepresentation() {
            assertEquals("initial", mutableString.toString());
            mutableString.setValue("new");
            assertEquals("new", mutableString.toString());
            mutableString.setValue(null);
            assertEquals("null", mutableString.toString());

            assertEquals("100", mutableInteger.toString());
            mutableInteger.setValue(200);
            assertEquals("200", mutableInteger.toString());
            mutableInteger.setValue(null);
            assertEquals("null", mutableInteger.toString());
        }

        @Test
        @DisplayName("equals() should compare based on value")
        void equals_shouldCompareBasedOnValue() {
            TestMutable<String> sameValue = new TestMutable<>("initial");
            TestMutable<String> differentValue = new TestMutable<>("different");
            TestMutable<String> nullValue = new TestMutable<>(null);

            assertTrue(mutableString.equals(sameValue));
            assertFalse(mutableString.equals(differentValue));
            assertFalse(mutableString.equals(nullValue));
            assertFalse(mutableString.equals(null));
            assertFalse(mutableString.equals("initial")); // Different type

            TestMutable<String> mutableStringNull = new TestMutable<>(null);
            assertTrue(nullValue.equals(mutableStringNull));
            assertFalse(nullValue.equals(mutableString));
        }

        @Test
        @DisplayName("hashCode() should be consistent with equals()")
        void hashCode_shouldBeConsistentWithEquals() {
            TestMutable<String> sameValue = new TestMutable<>("initial");
            TestMutable<String> differentValue = new TestMutable<>("different");
            TestMutable<String> nullValue = new TestMutable<>(null);

            assertEquals(mutableString.hashCode(), sameValue.hashCode());
            assertNotEquals(mutableString.hashCode(), differentValue.hashCode());

            TestMutable<String> mutableStringNull = new TestMutable<>(null);
            assertEquals(nullValue.hashCode(), mutableStringNull.hashCode());
            assertNotEquals(mutableString.hashCode(), nullValue.hashCode());
        }
    }
}