package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.MutableInt;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class MutableIntTestP3CP3C {

    private MutableInt mutableInt;

    @BeforeEach
    void setUp() {
        mutableInt = new MutableInt(0);
    }

    @Nested
    @DisplayName("add(int operand) tests")
    class AddIntTests {

        @Test
        @DisplayName("Should add a positive integer correctly")
        void addInt_positive() {
            mutableInt.setValue(5);
            mutableInt.add(3);
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should add a negative integer correctly")
        void addInt_negative() {
            mutableInt.setValue(5);
            mutableInt.add(-3);
            assertEquals(2, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should add zero correctly")
        void addInt_zero() {
            mutableInt.setValue(5);
            mutableInt.add(0);
            assertEquals(5, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle large positive additions without overflow (within int limits)")
        void addInt_largePositive() {
            mutableInt.setValue(Integer.MAX_VALUE - 10);
            mutableInt.add(5);
            assertEquals(Integer.MAX_VALUE - 5, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle large negative additions without underflow (within int limits)")
        void addInt_largeNegative() {
            mutableInt.setValue(Integer.MIN_VALUE + 10);
            mutableInt.add(-5);
            assertEquals(Integer.MIN_VALUE + 5, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle overflow when adding positive values")
        void addInt_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            mutableInt.add(1);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue()); // Expected Java overflow behavior
        }

        @Test
        @DisplayName("Should handle underflow when adding negative values")
        void addInt_underflow() {
            mutableInt.setValue(Integer.MIN_VALUE);
            mutableInt.add(-1);
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue()); // Expected Java underflow behavior
        }
    }

    @Nested
    @DisplayName("add(Number operand) tests")
    class AddNumberTests {

        @Test
        @DisplayName("Should add an Integer correctly")
        void addNumber_Integer() {
            mutableInt.setValue(5);
            mutableInt.add(Integer.valueOf(3));
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should add a Long correctly")
        void addNumber_Long() {
            mutableInt.setValue(5);
            mutableInt.add(Long.valueOf(3L));
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should add a Double correctly (truncates decimal part)")
        void addNumber_Double() {
            mutableInt.setValue(5);
            mutableInt.add(Double.valueOf(3.7));
            assertEquals(8, mutableInt.intValue()); // 5 + 3 = 8 (truncates .7)
        }

        @Test
        @DisplayName("Should add a Float correctly (truncates decimal part)")
        void addNumber_Float() {
            mutableInt.setValue(5);
            mutableInt.add(Float.valueOf(3.2f));
            assertEquals(8, mutableInt.intValue()); // 5 + 3 = 8 (truncates .2)
        }

        @Test
        @DisplayName("Should add a Byte correctly")
        void addNumber_Byte() {
            mutableInt.setValue(5);
            mutableInt.add(Byte.valueOf((byte) 3));
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should add a Short correctly")
        void addNumber_Short() {
            mutableInt.setValue(5);
            mutableInt.add(Short.valueOf((short) 3));
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle null operand by throwing NullPointerException")
        void addNumber_nullOperand() {
            mutableInt.setValue(5);
            assertThrows(NullPointerException.class, () -> mutableInt.add((Number) null));
            assertEquals(5, mutableInt.intValue()); // Value should remain unchanged
        }

        @Test
        @DisplayName("Should handle overflow with Number operand")
        void addNumber_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            mutableInt.add(Integer.valueOf(1));
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("addAndGet(int operand) tests")
    class AddAndGetIntTests {

        @Test
        @DisplayName("Should add and return the new value correctly")
        void addAndGetInt_normal() {
            mutableInt.setValue(5);
            int result = mutableInt.addAndGet(3);
            assertEquals(8, result);
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle overflow and return the new value")
        void addAndGetInt_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            int result = mutableInt.addAndGet(1);
            assertEquals(Integer.MIN_VALUE, result);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("addAndGet(Number operand) tests")
    class AddAndGetNumberTests {

        @Test
        @DisplayName("Should add and return the new value correctly with Number")
        void addAndGetNumber_normal() {
            mutableInt.setValue(5);
            int result = mutableInt.addAndGet(Integer.valueOf(3));
            assertEquals(8, result);
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle null operand by throwing NullPointerException")
        void addAndGetNumber_nullOperand() {
            mutableInt.setValue(5);
            assertThrows(NullPointerException.class, () -> mutableInt.addAndGet((Number) null));
            assertEquals(5, mutableInt.intValue()); // Value should remain unchanged
        }
    }

    @Nested
    @DisplayName("compareTo(MutableInt other) tests")
    class CompareToTests {

        @Test
        @DisplayName("Should return 0 when values are equal")
        void compareTo_equal() {
            mutableInt.setValue(10);
            MutableInt other = new MutableInt(10);
            assertEquals(0, mutableInt.compareTo(other));
        }

        @Test
        @DisplayName("Should return a positive value when this is greater than other")
        void compareTo_greater() {
            mutableInt.setValue(15);
            MutableInt other = new MutableInt(10);
            assertTrue(mutableInt.compareTo(other) > 0);
        }

        @Test
        @DisplayName("Should return a negative value when this is less than other")
        void compareTo_less() {
            mutableInt.setValue(5);
            MutableInt other = new MutableInt(10);
            assertTrue(mutableInt.compareTo(other) < 0);
        }

        @Test
        @DisplayName("Should handle minimum int values")
        void compareTo_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            MutableInt other = new MutableInt(Integer.MIN_VALUE + 1);
            assertTrue(mutableInt.compareTo(other) < 0);
        }

        @Test
        @DisplayName("Should handle maximum int values")
        void compareTo_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            MutableInt other = new MutableInt(Integer.MAX_VALUE - 1);
            assertTrue(mutableInt.compareTo(other) > 0);
        }

        @Test
        @DisplayName("Should throw NullPointerException if other is null")
        void compareTo_nullOther() {
            assertThrows(NullPointerException.class, () -> mutableInt.compareTo(null));
        }
    }

    @Nested
    @DisplayName("decrement() tests")
    class DecrementTests {

        @Test
        @DisplayName("Should decrement a positive value correctly")
        void decrement_positive() {
            mutableInt.setValue(5);
            mutableInt.decrement();
            assertEquals(4, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should decrement zero correctly")
        void decrement_zero() {
            mutableInt.setValue(0);
            mutableInt.decrement();
            assertEquals(-1, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should decrement a negative value correctly")
        void decrement_negative() {
            mutableInt.setValue(-5);
            mutableInt.decrement();
            assertEquals(-6, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle underflow when decrementing Integer.MIN_VALUE")
        void decrement_underflow() {
            mutableInt.setValue(Integer.MIN_VALUE);
            mutableInt.decrement();
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue()); // Expected Java underflow behavior
        }
    }

    @Nested
    @DisplayName("decrementAndGet() tests")
    class DecrementAndGetTests {

        @Test
        @DisplayName("Should decrement and return the new value correctly")
        void decrementAndGet_normal() {
            mutableInt.setValue(5);
            int result = mutableInt.decrementAndGet();
            assertEquals(4, result);
            assertEquals(4, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle underflow and return the new value")
        void decrementAndGet_underflow() {
            mutableInt.setValue(Integer.MIN_VALUE);
            int result = mutableInt.decrementAndGet();
            assertEquals(Integer.MAX_VALUE, result);
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("doubleValue() tests")
    class DoubleValueTests {

        @Test
        @DisplayName("Should return correct double value for positive int")
        void doubleValue_positive() {
            mutableInt.setValue(123);
            assertEquals(123.0, mutableInt.doubleValue(), 0.001);
        }

        @Test
        @DisplayName("Should return correct double value for zero")
        void doubleValue_zero() {
            mutableInt.setValue(0);
            assertEquals(0.0, mutableInt.doubleValue(), 0.001);
        }

        @Test
        @DisplayName("Should return correct double value for negative int")
        void doubleValue_negative() {
            mutableInt.setValue(-456);
            assertEquals(-456.0, mutableInt.doubleValue(), 0.001);
        }

        @Test
        @DisplayName("Should return correct double value for Integer.MAX_VALUE")
        void doubleValue_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            assertEquals((double) Integer.MAX_VALUE, mutableInt.doubleValue(), 0.001);
        }

        @Test
        @DisplayName("Should return correct double value for Integer.MIN_VALUE")
        void doubleValue_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            assertEquals((double) Integer.MIN_VALUE, mutableInt.doubleValue(), 0.001);
        }
    }

    @Nested
    @DisplayName("equals(Object obj) tests")
    class EqualsTests {

        @Test
        @DisplayName("Should return true for same object reference")
        void equals_sameObject() {
            assertTrue(mutableInt.equals(mutableInt));
        }

        @Test
        @DisplayName("Should return true for equal MutableInt objects")
        void equals_equalMutableInt() {
            mutableInt.setValue(10);
            MutableInt other = new MutableInt(10);
            assertTrue(mutableInt.equals(other));
        }

        @Test
        @DisplayName("Should return false for different MutableInt objects")
        void equals_differentMutableInt() {
            mutableInt.setValue(10);
            MutableInt other = new MutableInt(20);
            assertFalse(mutableInt.equals(other));
        }

        @Test
        @DisplayName("Should return false for null object")
        void equals_nullObject() {
            assertFalse(mutableInt.equals(null));
        }

        @Test
        @DisplayName("Should return false for different class type")
        void equals_differentClass() {
            assertFalse(mutableInt.equals("a string"));
        }

        @Test
        @DisplayName("Should return true for equal values after modification")
        void equals_afterModification() {
            mutableInt.setValue(5);
            MutableInt other = new MutableInt(0);
            other.setValue(5);
            assertTrue(mutableInt.equals(other));
        }
    }

    @Nested
    @DisplayName("floatValue() tests")
    class FloatValueTests {

        @Test
        @DisplayName("Should return correct float value for positive int")
        void floatValue_positive() {
            mutableInt.setValue(123);
            assertEquals(123.0f, mutableInt.floatValue(), 0.001f);
        }

        @Test
        @DisplayName("Should return correct float value for zero")
        void floatValue_zero() {
            mutableInt.setValue(0);
            assertEquals(0.0f, mutableInt.floatValue(), 0.001f);
        }

        @Test
        @DisplayName("Should return correct float value for negative int")
        void floatValue_negative() {
            mutableInt.setValue(-456);
            assertEquals(-456.0f, mutableInt.floatValue(), 0.001f);
        }

        @Test
        @DisplayName("Should return correct float value for Integer.MAX_VALUE")
        void floatValue_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            assertEquals((float) Integer.MAX_VALUE, mutableInt.floatValue(), 0.001f);
        }

        @Test
        @DisplayName("Should return correct float value for Integer.MIN_VALUE")
        void floatValue_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            assertEquals((float) Integer.MIN_VALUE, mutableInt.floatValue(), 0.001f);
        }
    }

    @Nested
    @DisplayName("getAndAdd(int operand) tests")
    class GetAndAddIntTests {

        @Test
        @DisplayName("Should return old value and then add correctly")
        void getAndAddInt_normal() {
            mutableInt.setValue(5);
            int oldValue = mutableInt.getAndAdd(3);
            assertEquals(5, oldValue);
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle overflow, return old value, and set new value")
        void getAndAddInt_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            int oldValue = mutableInt.getAndAdd(1);
            assertEquals(Integer.MAX_VALUE, oldValue);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("getAndAdd(Number operand) tests")
    class GetAndAddNumberTests {

        @Test
        @DisplayName("Should return old value and then add correctly with Number")
        void getAndAddNumber_normal() {
            mutableInt.setValue(5);
            int oldValue = mutableInt.getAndAdd(Integer.valueOf(3));
            assertEquals(5, oldValue);
            assertEquals(8, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle null operand by throwing NullPointerException")
        void getAndAddNumber_nullOperand() {
            mutableInt.setValue(5);
            assertThrows(NullPointerException.class, () -> mutableInt.getAndAdd((Number) null));
            assertEquals(5, mutableInt.intValue()); // Value should remain unchanged
        }
    }

    @Nested
    @DisplayName("getAndDecrement() tests")
    class GetAndDecrementTests {

        @Test
        @DisplayName("Should return old value and then decrement correctly")
        void getAndDecrement_normal() {
            mutableInt.setValue(5);
            int oldValue = mutableInt.getAndDecrement();
            assertEquals(5, oldValue);
            assertEquals(4, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle underflow, return old value, and set new value")
        void getAndDecrement_underflow() {
            mutableInt.setValue(Integer.MIN_VALUE);
            int oldValue = mutableInt.getAndDecrement();
            assertEquals(Integer.MIN_VALUE, oldValue);
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("getAndIncrement() tests")
    class GetAndIncrementTests {

        @Test
        @DisplayName("Should return old value and then increment correctly")
        void getAndIncrement_normal() {
            mutableInt.setValue(5);
            int oldValue = mutableInt.getAndIncrement();
            assertEquals(5, oldValue);
            assertEquals(6, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle overflow, return old value, and set new value")
        void getAndIncrement_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            int oldValue = mutableInt.getAndIncrement();
            assertEquals(Integer.MAX_VALUE, oldValue);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("getValue() tests")
    class GetValueTests {

        @Test
        @DisplayName("Should return the current value as an Integer object")
        void getValue_normal() {
            mutableInt.setValue(100);
            Integer value = mutableInt.getValue();
            assertNotNull(value);
            assertEquals(100, value.intValue());
            assertInstanceOf(Integer.class, value);
        }

        @Test
        @DisplayName("Should return Integer.valueOf(0) for default constructor")
        void getValue_defaultConstructor() {
            MutableInt defaultMutableInt = new MutableInt();
            assertEquals(Integer.valueOf(0), defaultMutableInt.getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() tests")
    class HashCodeTests {

        @Test
        @DisplayName("Should return same hash code for equal objects")
        void hashCode_equalObjects() {
            mutableInt.setValue(10);
            MutableInt other = new MutableInt(10);
            assertEquals(mutableInt.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("Should return different hash code for different objects")
        void hashCode_differentObjects() {
            mutableInt.setValue(10);
            MutableInt other = new MutableInt(20);
            assertNotEquals(mutableInt.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("Should return hash code consistent with Integer.hashCode()")
        void hashCode_consistency() {
            mutableInt.setValue(12345);
            assertEquals(Integer.valueOf(12345).hashCode(), mutableInt.hashCode());
        }
    }

    @Nested
    @DisplayName("increment() tests")
    class IncrementTests {

        @Test
        @DisplayName("Should increment a positive value correctly")
        void increment_positive() {
            mutableInt.setValue(5);
            mutableInt.increment();
            assertEquals(6, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should increment zero correctly")
        void increment_zero() {
            mutableInt.setValue(0);
            mutableInt.increment();
            assertEquals(1, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should increment a negative value correctly")
        void increment_negative() {
            mutableInt.setValue(-5);
            mutableInt.increment();
            assertEquals(-4, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle overflow when incrementing Integer.MAX_VALUE")
        void increment_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            mutableInt.increment();
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue()); // Expected Java overflow behavior
        }
    }

    @Nested
    @DisplayName("incrementAndGet() tests")
    class IncrementAndGetTests {

        @Test
        @DisplayName("Should increment and return the new value correctly")
        void incrementAndGet_normal() {
            mutableInt.setValue(5);
            int result = mutableInt.incrementAndGet();
            assertEquals(6, result);
            assertEquals(6, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle overflow and return the new value")
        void incrementAndGet_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            int result = mutableInt.incrementAndGet();
            assertEquals(Integer.MIN_VALUE, result);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("intValue() tests")
    class IntValueTests {

        @Test
        @DisplayName("Should return the current value as an int")
        void intValue_normal() {
            mutableInt.setValue(100);
            assertEquals(100, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should return 0 for default constructor")
        void intValue_defaultConstructor() {
            MutableInt defaultMutableInt = new MutableInt();
            assertEquals(0, defaultMutableInt.intValue());
        }

        @Test
        @DisplayName("Should return Integer.MAX_VALUE correctly")
        void intValue_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should return Integer.MIN_VALUE correctly")
        void intValue_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("longValue() tests")
    class LongValueTests {

        @Test
        @DisplayName("Should return correct long value for positive int")
        void longValue_positive() {
            mutableInt.setValue(123);
            assertEquals(123L, mutableInt.longValue());
        }

        @Test
        @DisplayName("Should return correct long value for zero")
        void longValue_zero() {
            mutableInt.setValue(0);
            assertEquals(0L, mutableInt.longValue());
        }

        @Test
        @DisplayName("Should return correct long value for negative int")
        void longValue_negative() {
            mutableInt.setValue(-456);
            assertEquals(-456L, mutableInt.longValue());
        }

        @Test
        @DisplayName("Should return correct long value for Integer.MAX_VALUE")
        void longValue_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            assertEquals((long) Integer.MAX_VALUE, mutableInt.longValue());
        }

        @Test
        @DisplayName("Should return correct long value for Integer.MIN_VALUE")
        void longValue_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            assertEquals((long) Integer.MIN_VALUE, mutableInt.longValue());
        }
    }

    @Nested
    @DisplayName("setValue(int value) tests")
    class SetValueIntTests {

        @Test
        @DisplayName("Should set a positive integer correctly")
        void setValueInt_positive() {
            mutableInt.setValue(100);
            assertEquals(100, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set zero correctly")
        void setValueInt_zero() {
            mutableInt.setValue(0);
            assertEquals(0, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set a negative integer correctly")
        void setValueInt_negative() {
            mutableInt.setValue(-50);
            assertEquals(-50, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set Integer.MAX_VALUE correctly")
        void setValueInt_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set Integer.MIN_VALUE correctly")
        void setValueInt_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
        }
    }

    @Nested
    @DisplayName("setValue(Number value) tests")
    class SetValueNumberTests {

        @Test
        @DisplayName("Should set value from Integer correctly")
        void setValueNumber_Integer() {
            mutableInt.setValue(Integer.valueOf(100));
            assertEquals(100, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set value from Long correctly (truncates if out of int range)")
        void setValueNumber_Long() {
            mutableInt.setValue(Long.valueOf(12345678901L)); // This will be truncated
            assertEquals(12345678901L, mutableInt.longValue()); // longValue() will return the full value
            assertEquals((int) 12345678901L, mutableInt.intValue()); // intValue() will show truncation
        }

        @Test
        @DisplayName("Should set value from Double correctly (truncates decimal part)")
        void setValueNumber_Double() {
            mutableInt.setValue(Double.valueOf(100.75));
            assertEquals(100, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set value from Float correctly (truncates decimal part)")
        void setValueNumber_Float() {
            mutableInt.setValue(Float.valueOf(50.25f));
            assertEquals(50, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set value from Byte correctly")
        void setValueNumber_Byte() {
            mutableInt.setValue(Byte.valueOf((byte) 120));
            assertEquals(120, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should set value from Short correctly")
        void setValueNumber_Short() {
            mutableInt.setValue(Short.valueOf((short) 30000));
            assertEquals(30000, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should throw NullPointerException if value is null")
        void setValueNumber_nullValue() {
            assertThrows(NullPointerException.class, () -> mutableInt.setValue((Number) null));
            assertEquals(0, mutableInt.intValue()); // Value should remain unchanged
        }
    }

    @Nested
    @DisplayName("subtract(int operand) tests")
    class SubtractIntTests {

        @Test
        @DisplayName("Should subtract a positive integer correctly")
        void subtractInt_positive() {
            mutableInt.setValue(10);
            mutableInt.subtract(3);
            assertEquals(7, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should subtract a negative integer correctly (effectively adds)")
        void subtractInt_negative() {
            mutableInt.setValue(10);
            mutableInt.subtract(-3);
            assertEquals(13, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should subtract zero correctly")
        void subtractInt_zero() {
            mutableInt.setValue(10);
            mutableInt.subtract(0);
            assertEquals(10, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should handle underflow when subtracting positive values")
        void subtractInt_underflow() {
            mutableInt.setValue(Integer.MIN_VALUE);
            mutableInt.subtract(1);
            assertEquals(Integer.MAX_VALUE, mutableInt.intValue()); // Expected Java underflow behavior
        }

        @Test
        @DisplayName("Should handle overflow when subtracting negative values")
        void subtractInt_overflow() {
            mutableInt.setValue(Integer.MAX_VALUE);
            mutableInt.subtract(-1);
            assertEquals(Integer.MIN_VALUE, mutableInt.intValue()); // Expected Java overflow behavior
        }
    }

    @Nested
    @DisplayName("subtract(Number operand) tests")
    class SubtractNumberTests {

        @Test
        @DisplayName("Should subtract an Integer correctly")
        void subtractNumber_Integer() {
            mutableInt.setValue(10);
            mutableInt.subtract(Integer.valueOf(3));
            assertEquals(7, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should subtract a Long correctly")
        void subtractNumber_Long() {
            mutableInt.setValue(10);
            mutableInt.subtract(Long.valueOf(3L));
            assertEquals(7, mutableInt.intValue());
        }

        @Test
        @DisplayName("Should subtract a Double correctly (truncates decimal part)")
        void subtractNumber_Double() {
            mutableInt.setValue(10);
            mutableInt.subtract(Double.valueOf(3.7));
            assertEquals(7, mutableInt.intValue()); // 10 - 3 = 7 (truncates .7)
        }

        @Test
        @DisplayName("Should handle null operand by throwing NullPointerException")
        void subtractNumber_nullOperand() {
            mutableInt.setValue(10);
            assertThrows(NullPointerException.class, () -> mutableInt.subtract((Number) null));
            assertEquals(10, mutableInt.intValue()); // Value should remain unchanged
        }
    }

    @Nested
    @DisplayName("toInteger() tests")
    class ToIntegerTests {

        @Test
        @DisplayName("Should return the current value as an Integer object")
        void toInteger_normal() {
            mutableInt.setValue(100);
            Integer value = mutableInt.toInteger();
            assertNotNull(value);
            assertEquals(100, value.intValue());
            assertInstanceOf(Integer.class, value);
        }

        @Test
        @DisplayName("Should return Integer.valueOf(0) for default constructor")
        void toInteger_defaultConstructor() {
            MutableInt defaultMutableInt = new MutableInt();
            assertEquals(Integer.valueOf(0), defaultMutableInt.toInteger());
        }
    }

    @Nested
    @DisplayName("toString() tests")
    class ToStringTests {

        @Test
        @DisplayName("Should return string representation of positive integer")
        void toString_positive() {
            mutableInt.setValue(123);
            assertEquals("123", mutableInt.toString());
        }

        @Test
        @DisplayName("Should return string representation of zero")
        void toString_zero() {
            mutableInt.setValue(0);
            assertEquals("0", mutableInt.toString());
        }

        @Test
        @DisplayName("Should return string representation of negative integer")
        void toString_negative() {
            mutableInt.setValue(-456);
            assertEquals("-456", mutableInt.toString());
        }

        @Test
        @DisplayName("Should return string representation of Integer.MAX_VALUE")
        void toString_maxInt() {
            mutableInt.setValue(Integer.MAX_VALUE);
            assertEquals(String.valueOf(Integer.MAX_VALUE), mutableInt.toString());
        }

        @Test
        @DisplayName("Should return string representation of Integer.MIN_VALUE")
        void toString_minInt() {
            mutableInt.setValue(Integer.MIN_VALUE);
            assertEquals(String.valueOf(Integer.MIN_VALUE), mutableInt.toString());
        }
    }

    // Constructor tests
    @Nested
    @DisplayName("Constructor tests")
    class ConstructorTests {

        @Test
        @DisplayName("Default constructor should initialize to 0")
        void constructor_default() {
            MutableInt mi = new MutableInt();
            assertEquals(0, mi.intValue());
        }

        @Test
        @DisplayName("Constructor with int should set initial value")
        void constructor_int() {
            MutableInt mi = new MutableInt(123);
            assertEquals(123, mi.intValue());
        }

        @Test
        @DisplayName("Constructor with Number should set initial value")
        void constructor_number() {
            MutableInt mi = new MutableInt(Integer.valueOf(456));
            assertEquals(456, mi.intValue());
        }

        @Test
        @DisplayName("Constructor with null Number should throw NullPointerException")
        void constructor_nullNumber() {
            assertThrows(NullPointerException.class, () -> new MutableInt((Number) null));
        }

        @Test
        @DisplayName("Constructor with String should parse initial value")
        void constructor_string() {
            MutableInt mi = new MutableInt("789");
            assertEquals(789, mi.intValue());
        }

        @ParameterizedTest
        @NullSource
        @ValueSource(strings = {"", "abc", "123.45"})
        @DisplayName("Constructor with invalid String should throw NumberFormatException")
        void constructor_invalidString(String invalidString) {
            assertThrows(NumberFormatException.class, () -> new MutableInt(invalidString));
        }
    }
}