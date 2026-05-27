package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.Mutable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive unit tests for the {@link Mutable} abstract class.
 * This test suite covers normal behavior, edge cases, and potential failure scenarios
 * for the `get()`, `getValue()`, and `setValue()` methods.
 *
 * Since `Mutable` is an abstract class, we will test it using a concrete anonymous
 * inner class implementation for various types.
 */
class MutableTestP3CP3C {

    // Helper concrete implementation for testing Mutable<T>
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

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof TestMutable) {
                return this.getValue().equals(((TestMutable<?>) obj).getValue());
            }
            return false;
        }

        @Override
        public int hashCode() {
            return value != null ? value.hashCode() : 0;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }
    }

    @Nested
    @DisplayName("Tests for Mutable<Integer>")
    class IntegerMutableTests {
        private TestMutable<Integer> mutableInteger;

        @BeforeEach
        void setUp() {
            mutableInteger = new TestMutable<>(10);
        }

        @Test
        @DisplayName("get(): Should return the initial value")
        void get_initialValue_shouldReturnCorrectValue() {
            assertEquals(10, mutableInteger.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial value")
        void getValue_initialValue_shouldReturnCorrectValue() {
            assertEquals(10, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue(): Should update the value correctly")
        void setValue_newValue_shouldUpdateValue() {
            mutableInteger.setValue(20);
            assertEquals(20, mutableInteger.get());
            assertEquals(20, mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null value")
        void setValue_nullValue_shouldSetToNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
            assertNull(mutableInteger.getValue());
        }

        @Test
        @DisplayName("get() after setValue(null): Should return null")
        void get_afterSetNull_shouldReturnNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.get());
        }

        @Test
        @DisplayName("getValue() after setValue(null): Should return null")
        void getValue_afterSetNull_shouldReturnNull() {
            mutableInteger.setValue(null);
            assertNull(mutableInteger.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting the same value")
        void setValue_sameValue_shouldNotChangeValue() {
            Integer initialValue = mutableInteger.get();
            mutableInteger.setValue(initialValue);
            assertEquals(initialValue, mutableInteger.get());
        }

        @Test
        @DisplayName("Multiple setValue() calls: Should reflect the last set value")
        void setValue_multipleCalls_shouldReflectLastValue() {
            mutableInteger.setValue(5);
            mutableInteger.setValue(15);
            mutableInteger.setValue(25);
            assertEquals(25, mutableInteger.get());
            assertEquals(25, mutableInteger.getValue());
        }

        @Test
        @DisplayName("toString(): Should return string representation of the value")
        void toString_shouldReturnCorrectString() {
            assertEquals("10", mutableInteger.toString());
            mutableInteger.setValue(null);
            assertEquals("null", mutableInteger.toString());
            mutableInteger.setValue(123);
            assertEquals("123", mutableInteger.toString());
        }

        @Test
        @DisplayName("equals(): Should return true for equal values")
        void equals_sameValue_shouldReturnTrue() {
            TestMutable<Integer> other = new TestMutable<>(10);
            assertTrue(mutableInteger.equals(other));
        }

        @Test
        @DisplayName("equals(): Should return false for different values")
        void equals_differentValue_shouldReturnFalse() {
            TestMutable<Integer> other = new TestMutable<>(20);
            assertFalse(mutableInteger.equals(other));
        }

        @Test
        @DisplayName("equals(): Should return false for null value compared to non-null")
        void equals_nullValueComparedToNonNull_shouldReturnFalse() {
            mutableInteger.setValue(null);
            TestMutable<Integer> other = new TestMutable<>(10);
            assertFalse(mutableInteger.equals(other));
        }

        @Test
        @DisplayName("equals(): Should return true for two null values")
        void equals_twoNullValues_shouldReturnTrue() {
            mutableInteger.setValue(null);
            TestMutable<Integer> other = new TestMutable<>(null);
            assertTrue(mutableInteger.equals(other));
        }

        @Test
        @DisplayName("equals(): Should return false for different types")
        void equals_differentType_shouldReturnFalse() {
            assertFalse(mutableInteger.equals("hello"));
        }

        @Test
        @DisplayName("hashCode(): Should return consistent hash code")
        void hashCode_shouldBeConsistent() {
            int initialHashCode = mutableInteger.hashCode();
            assertEquals(initialHashCode, mutableInteger.hashCode());
            mutableInteger.setValue(20);
            assertNotEquals(initialHashCode, mutableInteger.hashCode());
        }

        @Test
        @DisplayName("hashCode(): Should return 0 for null value")
        void hashCode_nullValue_shouldReturnZero() {
            mutableInteger.setValue(null);
            assertEquals(0, mutableInteger.hashCode());
        }

        @Test
        @DisplayName("hashCode(): Equal objects should have equal hash codes")
        void hashCode_equalObjects_shouldHaveEqualHashCodes() {
            TestMutable<Integer> other = new TestMutable<>(10);
            assertEquals(mutableInteger.hashCode(), other.hashCode());
        }
    }

    @Nested
    @DisplayName("Tests for Mutable<String>")
    class StringMutableTests {
        private TestMutable<String> mutableString;

        @BeforeEach
        void setUp() {
            mutableString = new TestMutable<>("hello");
        }

        @Test
        @DisplayName("get(): Should return the initial string value")
        void get_initialValue_shouldReturnCorrectString() {
            assertEquals("hello", mutableString.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial string value")
        void getValue_initialValue_shouldReturnCorrectString() {
            assertEquals("hello", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue(): Should update the string value correctly")
        void setValue_newValue_shouldUpdateString() {
            mutableString.setValue("world");
            assertEquals("world", mutableString.get());
            assertEquals("world", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting an empty string")
        void setValue_emptyString_shouldSetEmptyString() {
            mutableString.setValue("");
            assertEquals("", mutableString.get());
            assertEquals("", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null string value")
        void setValue_nullString_shouldSetToNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());
        }

        @Test
        @DisplayName("get() after setValue(null): Should return null")
        void get_afterSetNull_shouldReturnNull() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
        }

        @Test
        @DisplayName("getValue() after setValue(null): Should return null")
        void getValue_afterSetNull_shouldReturnNull() {
            mutableString.setValue(null);
            assertNull(mutableString.getValue());
        }

        @Test
        @DisplayName("toString(): Should return string representation of the value")
        void toString_shouldReturnCorrectString() {
            assertEquals("hello", mutableString.toString());
            mutableString.setValue(null);
            assertEquals("null", mutableString.toString());
            mutableString.setValue("test");
            assertEquals("test", mutableString.toString());
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
        @DisplayName("get(): Should return the initial boolean value")
        void get_initialValue_shouldReturnCorrectBoolean() {
            assertTrue(mutableBoolean.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial boolean value")
        void getValue_initialValue_shouldReturnCorrectBoolean() {
            assertTrue(mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue(): Should update the boolean value correctly")
        void setValue_newValue_shouldUpdateBoolean() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.get());
            assertFalse(mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null boolean value")
        void setValue_nullBoolean_shouldSetToNull() {
            mutableBoolean.setValue(null);
            assertNull(mutableBoolean.get());
            assertNull(mutableBoolean.getValue());
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
        @DisplayName("get(): Should return the initial object reference")
        void get_initialValue_shouldReturnCorrectObject() {
            assertSame(obj1, mutableObject.get());
        }

        @Test
        @DisplayName("getValue(): Should return the initial object reference")
        void getValue_initialValue_shouldReturnCorrectObject() {
            assertSame(obj1, mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue(): Should update the object reference correctly")
        void setValue_newValue_shouldUpdateObject() {
            mutableObject.setValue(obj2);
            assertSame(obj2, mutableObject.get());
            assertSame(obj2, mutableObject.getValue());
        }

        @Test
        @DisplayName("setValue(): Should allow setting null object reference")
        void setValue_nullObject_shouldSetToNull() {
            mutableObject.setValue(null);
            assertNull(mutableObject.get());
            assertNull(mutableObject.getValue());
        }

        @Test
        @DisplayName("toString(): Should return string representation of the object")
        void toString_shouldReturnCorrectString() {
            assertEquals(obj1.toString(), mutableObject.toString());
            mutableObject.setValue(null);
            assertEquals("null", mutableObject.toString());
            mutableObject.setValue("test"); // Set a string to test its toString
            assertEquals("test", mutableObject.toString());
        }
    }

    @Nested
    @DisplayName("General Edge Cases and Failure Scenarios (Conceptual)")
    class GeneralEdgeCases {

        // The JML specifications for get(), getValue(), and setValue() are very simple:
        // get(): @ensures \result == getValue();
        // getValue(): @ensures \result == this.value; (conceptually, as it's abstract)
        // setValue(T value): @ensures getValue() == value;

        // These specifications imply that the methods should always work as long as
        // the underlying concrete implementation correctly handles the storage and retrieval
        // of the value. There are no explicit @requires clauses that would lead to
        // specific failure scenarios like IllegalArgumentException or NullPointerException
        // from the Mutable interface itself, as it allows null values.

        // The "failure scenarios" would primarily arise from:
        // 1. Incorrect implementation of the abstract methods in a concrete subclass.
        // 2. Misuse of the Mutable object (e.g., trying to dereference a null value
        //    returned by get() or getValue() without checking for null).

        @Test
        @DisplayName("Concrete implementation returning inconsistent values for get() and getValue()")
        void inconsistentImplementation_shouldFailAssertion() {
            Mutable<String> inconsistentMutable = new Mutable<String>() {
                private String value = "initial";

                @Override
                public String getValue() {
                    return value;
                }

                @Override
                public void setValue(String value) {
                    this.value = value;
                }

                @Override
                public String get() {
                    // Intentionally return a different value to violate @ensures \result == getValue();
                    return "inconsistent";
                }
            };

            // This test demonstrates how an incorrect implementation would violate the JML contract
            assertNotEquals(inconsistentMutable.getValue(), inconsistentMutable.get(),
                    "An inconsistent implementation should violate the get() postcondition");
        }

        @Test
        @DisplayName("Concrete implementation not updating value correctly on setValue()")
        void setValue_incorrectImplementation_shouldFailAssertion() {
            Mutable<Integer> buggyMutable = new Mutable<Integer>() {
                private Integer value = 1;

                @Override
                public Integer getValue() {
                    return value;
                }

                @Override
                public void setValue(Integer newValue) {
                    // Bug: does not update the value
                    // this.value = newValue;
                }

                @Override
                public Integer get() {
                    return getValue();
                }
            };

            buggyMutable.setValue(100);
            assertNotEquals(100, buggyMutable.get(),
                    "A buggy setValue implementation should not update the value as per contract");
            assertEquals(1, buggyMutable.get(), "Value should remain initial due to bug");
        }

        @Test
        @DisplayName("Null initial value for Mutable<T>")
        void constructor_nullInitialValue_shouldBeHandled() {
            TestMutable<String> mutableNull = new TestMutable<>(null);
            assertNull(mutableNull.get());
            assertNull(mutableNull.getValue());
            mutableNull.setValue("new value");
            assertEquals("new value", mutableNull.get());
        }
    }
}