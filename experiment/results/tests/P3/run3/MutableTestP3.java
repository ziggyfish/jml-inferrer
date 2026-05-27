package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.Mutable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the Mutable abstract class.
 * This class tests the contract defined by the JML specifications
 * for the get(), getValue(), and setValue() methods.
 *
 * Since Mutable is abstract, we will test it using a concrete anonymous
 * inner class implementation for various types.
 */
class MutableTestP3P3 {

    // Helper method to create a concrete Mutable instance for testing
    private <T> Mutable<T> createMutable(T initialValue) {
        return new Mutable<T>() {
            private T value = initialValue;

            @Override
            public T get() {
                // @ensures \result == this.value;
                return this.value;
            }

            @Override
            public T getValue() {
                // @ensures \result == this.value;
                return this.value;
            }

            @Override
            public void setValue(T value) {
                // @ensures this.value == value;
                this.value = value;
            }
        };
    }

    @Nested
    @DisplayName("Tests for Integer type")
    class IntegerMutableTests {
        private Mutable<Integer> mutableInt;

        @BeforeEach
        void setUp() {
            mutableInt = createMutable(10);
        }

        @Test
        @DisplayName("get() should return the initial value")
        void testGetInitialValue() {
            assertEquals(10, mutableInt.get());
        }

        @Test
        @DisplayName("getValue() should return the initial value")
        void testGetValueInitialValue() {
            assertEquals(10, mutableInt.getValue());
        }

        @Test
        @DisplayName("setValue() should update the value and get() should reflect it")
        void testSetValueAndUpdateGet() {
            mutableInt.setValue(20);
            assertEquals(20, mutableInt.get());
        }

        @Test
        @DisplayName("setValue() should update the value and getValue() should reflect it")
        void testSetValueAndUpdateGetValue() {
            mutableInt.setValue(30);
            assertEquals(30, mutableInt.getValue());
        }

        @Test
        @DisplayName("setValue() with null should be allowed for Integer")
        void testSetValueWithNull() {
            mutableInt.setValue(null);
            assertNull(mutableInt.get());
            assertNull(mutableInt.getValue());
        }

        @Test
        @DisplayName("Multiple setValue() calls should update correctly")
        void testMultipleSetValues() {
            mutableInt.setValue(5);
            assertEquals(5, mutableInt.get());
            mutableInt.setValue(100);
            assertEquals(100, mutableInt.getValue());
            mutableInt.setValue(-1);
            assertEquals(-1, mutableInt.get());
        }

        @Test
        @DisplayName("get() and getValue() should return the same value")
        void testGetAndGetValueConsistency() {
            assertEquals(mutableInt.get(), mutableInt.getValue());
            mutableInt.setValue(50);
            assertEquals(mutableInt.get(), mutableInt.getValue());
        }
    }

    @Nested
    @DisplayName("Tests for String type")
    class StringMutableTests {
        private Mutable<String> mutableString;

        @BeforeEach
        void setUp() {
            mutableString = createMutable("Hello");
        }

        @Test
        @DisplayName("get() should return the initial string value")
        void testGetInitialStringValue() {
            assertEquals("Hello", mutableString.get());
        }

        @Test
        @DisplayName("getValue() should return the initial string value")
        void testGetValueInitialStringValue() {
            assertEquals("Hello", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with a new string should update correctly")
        void testSetValueNewString() {
            mutableString.setValue("World");
            assertEquals("World", mutableString.get());
            assertEquals("World", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with an empty string should update correctly")
        void testSetValueEmptyString() {
            mutableString.setValue("");
            assertEquals("", mutableString.get());
            assertEquals("", mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() with null should be allowed for String")
        void testSetValueNullString() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
            assertNull(mutableString.getValue());
        }

        @Test
        @DisplayName("setValue() from null to a value should work")
        void testSetValueFromNullToValue() {
            mutableString.setValue(null);
            assertNull(mutableString.get());
            mutableString.setValue("New Value");
            assertEquals("New Value", mutableString.get());
        }

        @Test
        @DisplayName("setValue() from value to null should work")
        void testSetValueFromValueToNull() {
            mutableString.setValue("Initial");
            assertEquals("Initial", mutableString.get());
            mutableString.setValue(null);
            assertNull(mutableString.get());
        }
    }

    @Nested
    @DisplayName("Tests for Boolean type")
    class BooleanMutableTests {
        private Mutable<Boolean> mutableBoolean;

        @BeforeEach
        void setUp() {
            mutableBoolean = createMutable(true);
        }

        @Test
        @DisplayName("get() should return the initial boolean value")
        void testGetInitialBooleanValue() {
            assertTrue(mutableBoolean.get());
        }

        @Test
        @DisplayName("getValue() should return the initial boolean value")
        void testGetValueInitialBooleanValue() {
            assertTrue(mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue() to false should update correctly")
        void testSetValueFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.get());
            assertFalse(mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue() to true should update correctly")
        void testSetValueTrue() {
            mutableBoolean.setValue(false); // Set to false first
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.get());
            assertTrue(mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue() with null should be allowed for Boolean")
        void testSetValueNullBoolean() {
            mutableBoolean.setValue(null);
            assertNull(mutableBoolean.get());
            assertNull(mutableBoolean.getValue());
        }
    }

    @Nested
    @DisplayName("Tests for custom Object type")
    class CustomObjectMutableTests {
        private static class MyObject {
            private String name;

            public MyObject(String name) {
                this.name = name;
            }

            public String getName() {
                return name;
            }

            public void setName(String name) {
                this.name = name;
            }

            @Override
            public boolean equals(Object o) {
                if (this == o) return true;
                if (o == null || getClass() != o.getClass()) return false;
                MyObject myObject = (MyObject) o;
                return name != null ? name.equals(myObject.name) : myObject.name == null;
            }

            @Override
            public int hashCode() {
                return name != null ? name.hashCode() : 0;
            }
        }

        private Mutable<MyObject> mutableMyObject;
        private MyObject initialObject;

        @BeforeEach
        void setUp() {
            initialObject = new MyObject("Initial");
            mutableMyObject = createMutable(initialObject);
        }

        @Test
        @DisplayName("get() should return the initial custom object")
        void testGetInitialCustomObject() {
            assertEquals(initialObject, mutableMyObject.get());
            assertSame(initialObject, mutableMyObject.get()); // Should be the same instance
        }

        @Test
        @DisplayName("getValue() should return the initial custom object")
        void testGetValueInitialCustomObject() {
            assertEquals(initialObject, mutableMyObject.getValue());
            assertSame(initialObject, mutableMyObject.getValue()); // Should be the same instance
        }

        @Test
        @DisplayName("setValue() with a new custom object should update correctly")
        void testSetValueNewCustomObject() {
            MyObject newObject = new MyObject("Updated");
            mutableMyObject.setValue(newObject);
            assertEquals(newObject, mutableMyObject.get());
            assertSame(newObject, mutableMyObject.get()); // Should be the same instance
        }

        @Test
        @DisplayName("setValue() with null should be allowed for custom objects")
        void testSetValueNullCustomObject() {
            mutableMyObject.setValue(null);
            assertNull(mutableMyObject.get());
            assertNull(mutableMyObject.getValue());
        }

        @Test
        @DisplayName("Modifying the object returned by get() should reflect in subsequent calls (if mutable)")
        void testModifyingReturnedObject() {
            MyObject retrievedObject = mutableMyObject.get();
            retrievedObject.setName("Modified via reference"); // Modifying the object itself
            assertEquals("Modified via reference", mutableMyObject.get().getName());
            assertEquals("Modified via reference", mutableMyObject.getValue().getName());
        }

        @Test
        @DisplayName("Setting the same object instance should not change anything")
        void testSetSameObjectInstance() {
            MyObject currentObject = mutableMyObject.get();
            mutableMyObject.setValue(currentObject);
            assertSame(currentObject, mutableMyObject.get());
        }
    }

    @Nested
    @DisplayName("Edge Cases and General Behavior")
    class EdgeCasesAndGeneralBehavior {

        @Test
        @DisplayName("Mutable initialized with null should return null")
        void testInitialNullValue() {
            Mutable<Object> mutableNull = createMutable(null);
            assertNull(mutableNull.get());
            assertNull(mutableNull.getValue());
        }

        @Test
        @DisplayName("setValue() to null then to a value should work")
        void testSetNullThenValue() {
            Mutable<String> mutable = createMutable("Initial");
            mutable.setValue(null);
            assertNull(mutable.get());
            mutable.setValue("New Value");
            assertEquals("New Value", mutable.get());
        }

        @Test
        @DisplayName("setValue() to a value then to null should work")
        void testSetValueThenNull() {
            Mutable<Integer> mutable = createMutable(100);
            assertEquals(100, mutable.get());
            mutable.setValue(null);
            assertNull(mutable.get());
        }

        @Test
        @DisplayName("get() and getValue() should always return the same reference for objects")
        void testGetAndGetValueSameReference() {
            MyObject obj = new MyObject("Test");
            Mutable<MyObject> mutable = createMutable(obj);
            assertSame(mutable.get(), mutable.getValue());

            MyObject newObj = new MyObject("New Test");
            mutable.setValue(newObj);
            assertSame(mutable.get(), mutable.getValue());
        }

        @Test
        @DisplayName("get() and getValue() should return equal values for primitive wrappers")
        void testGetAndGetValueEqualValues() {
            Mutable<Integer> mutableInt = createMutable(5);
            assertEquals(mutableInt.get(), mutableInt.getValue());

            Mutable<Boolean> mutableBool = createMutable(true);
            assertEquals(mutableBool.get(), mutableBool.getValue());
        }
    }
}