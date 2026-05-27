package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.MutableInt;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

class MutableIntTestP3P3 {

    private MutableInt mutableInt;

    @BeforeEach
    void setUp() {
        mutableInt = new MutableInt(0);
    }

    // --- Constructor Tests (Implicitly covered by setUp and other tests) ---
    @Test
    @DisplayName("Test constructor with int value")
    void testConstructorInt() {
        MutableInt mi = new MutableInt(123);
        assertEquals(123, mi.intValue());
    }

    @Test
    @DisplayName("Test constructor with Number value (Integer)")
    void testConstructorNumberInteger() {
        MutableInt mi = new MutableInt(Integer.valueOf(456));
        assertEquals(456, mi.intValue());
    }

    @Test
    @DisplayName("Test constructor with Number value (Double) - should truncate")
    void testConstructorNumberDouble() {
        MutableInt mi = new MutableInt(Double.valueOf(789.99));
        assertEquals(789, mi.intValue()); // Expect truncation
    }

    @Test
    @DisplayName("Test constructor with null Number value - should throw NullPointerException")
    void testConstructorNumberNull() {
        assertThrows(NullPointerException.class, () -> new MutableInt((Number) null));
    }

    // --- add(int operand) ---
    @Test
    @DisplayName("add(int operand): Test normal positive addition")
    void testAddIntNormalPositive() {
        mutableInt.add(5);
        assertEquals(5, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(int operand): Test normal negative addition")
    void testAddIntNormalNegative() {
        mutableInt.add(-5);
        assertEquals(-5, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(int operand): Test adding zero")
    void testAddIntZero() {
        mutableInt.add(0);
        assertEquals(0, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(int operand): Test adding to a non-zero initial value")
    void testAddIntNonZeroInitial() {
        mutableInt.setValue(10);
        mutableInt.add(5);
        assertEquals(15, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(int operand): Test adding to a negative initial value")
    void testAddIntNegativeInitial() {
        mutableInt.setValue(-10);
        mutableInt.add(5);
        assertEquals(-5, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(int operand): Test adding to a negative initial value with negative operand")
    void testAddIntNegativeInitialNegativeOperand() {
        mutableInt.setValue(-10);
        mutableInt.add(-5);
        assertEquals(-15, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(int operand): Test integer overflow (positive)")
    void testAddIntOverflowPositive() {
        mutableInt.setValue(Integer.MAX_VALUE);
        mutableInt.add(1);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue()); // Expected overflow behavior
    }

    @Test
    @DisplayName("add(int operand): Test integer underflow (negative)")
    void testAddIntUnderflowNegative() {
        mutableInt.setValue(Integer.MIN_VALUE);
        mutableInt.add(-1);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue()); // Expected underflow behavior
    }

    // --- add(Number operand) ---
    @ParameterizedTest
    @MethodSource("numberProviderForAdd")
    @DisplayName("add(Number operand): Test with various Number types")
    void testAddNumberVariousTypes(Number operand, int expected) {
        mutableInt.setValue(10);
        mutableInt.add(operand);
        assertEquals(expected, mutableInt.intValue());
    }

    private static Stream<Arguments> numberProviderForAdd() {
        return Stream.of(
                Arguments.of(5, 15),
                Arguments.of(5L, 15),
                Arguments.of(5.0f, 15),
                Arguments.of(5.99, 15), // Expect truncation
                Arguments.of(new BigInteger("5"), 15),
                Arguments.of(new BigDecimal("5.123"), 15), // Expect truncation
                Arguments.of(-5, 5),
                Arguments.of(0, 10)
        );
    }

    @Test
    @DisplayName("add(Number operand): Test with null operand - should throw NullPointerException")
    void testAddNumberNull() {
        assertThrows(NullPointerException.class, () -> mutableInt.add((Number) null));
    }

    @Test
    @DisplayName("add(Number operand): Test overflow with Number (Integer.MAX_VALUE + 1)")
    void testAddNumberOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        mutableInt.add(1);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    @Test
    @DisplayName("add(Number operand): Test underflow with Number (Integer.MIN_VALUE - 1)")
    void testAddNumberUnderflow() {
        mutableInt.setValue(Integer.MIN_VALUE);
        mutableInt.add(-1);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
    }

    // --- addAndGet(int operand) ---
    @Test
    @DisplayName("addAndGet(int operand): Test normal positive addition and return")
    void testAddAndGetIntNormalPositive() {
        int result = mutableInt.addAndGet(5);
        assertEquals(5, result);
        assertEquals(5, mutableInt.intValue());
    }

    @Test
    @DisplayName("addAndGet(int operand): Test normal negative addition and return")
    void testAddAndGetIntNormalNegative() {
        int result = mutableInt.addAndGet(-5);
        assertEquals(-5, result);
        assertEquals(-5, mutableInt.intValue());
    }

    @Test
    @DisplayName("addAndGet(int operand): Test overflow and return")
    void testAddAndGetIntOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        int result = mutableInt.addAndGet(1);
        assertEquals(Integer.MIN_VALUE, result);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- addAndGet(Number operand) ---
    @ParameterizedTest
    @MethodSource("numberProviderForAdd")
    @DisplayName("addAndGet(Number operand): Test with various Number types and return")
    void testAddAndGetNumberVariousTypes(Number operand, int expected) {
        mutableInt.setValue(10);
        int result = mutableInt.addAndGet(operand);
        assertEquals(expected, result);
        assertEquals(expected, mutableInt.intValue());
    }

    @Test
    @DisplayName("addAndGet(Number operand): Test with null operand - should throw NullPointerException")
    void testAddAndGetNumberNull() {
        assertThrows(NullPointerException.class, () -> mutableInt.addAndGet((Number) null));
    }

    // --- compareTo(MutableInt other) ---
    @Test
    @DisplayName("compareTo: Test equal values")
    void testCompareToEqual() {
        MutableInt other = new MutableInt(0);
        assertEquals(0, mutableInt.compareTo(other));
    }

    @Test
    @DisplayName("compareTo: Test current value is less than other")
    void testCompareToLessThan() {
        MutableInt other = new MutableInt(5);
        assertTrue(mutableInt.compareTo(other) < 0);
    }

    @Test
    @DisplayName("compareTo: Test current value is greater than other")
    void testCompareToGreaterThan() {
        mutableInt.setValue(5);
        MutableInt other = new MutableInt(0);
        assertTrue(mutableInt.compareTo(other) > 0);
    }

    @Test
    @DisplayName("compareTo: Test with negative values")
    void testCompareToNegativeValues() {
        mutableInt.setValue(-10);
        MutableInt other = new MutableInt(-5);
        assertTrue(mutableInt.compareTo(other) < 0);
    }

    @Test
    @DisplayName("compareTo: Test with null other - should throw NullPointerException")
    void testCompareToNull() {
        assertThrows(NullPointerException.class, () -> mutableInt.compareTo(null));
    }

    // --- decrement() ---
    @Test
    @DisplayName("decrement(): Test normal decrement")
    void testDecrementNormal() {
        mutableInt.setValue(5);
        mutableInt.decrement();
        assertEquals(4, mutableInt.intValue());
    }

    @Test
    @DisplayName("decrement(): Test decrement from zero")
    void testDecrementFromZero() {
        mutableInt.decrement();
        assertEquals(-1, mutableInt.intValue());
    }

    @Test
    @DisplayName("decrement(): Test decrement from negative value")
    void testDecrementFromNegative() {
        mutableInt.setValue(-5);
        mutableInt.decrement();
        assertEquals(-6, mutableInt.intValue());
    }

    @Test
    @DisplayName("decrement(): Test integer underflow")
    void testDecrementUnderflow() {
        mutableInt.setValue(Integer.MIN_VALUE);
        mutableInt.decrement();
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue()); // Expected underflow behavior
    }

    // --- decrementAndGet() ---
    @Test
    @DisplayName("decrementAndGet(): Test normal decrement and return")
    void testDecrementAndGetNormal() {
        mutableInt.setValue(5);
        int result = mutableInt.decrementAndGet();
        assertEquals(4, result);
        assertEquals(4, mutableInt.intValue());
    }

    @Test
    @DisplayName("decrementAndGet(): Test underflow and return")
    void testDecrementAndGetUnderflow() {
        mutableInt.setValue(Integer.MIN_VALUE);
        int result = mutableInt.decrementAndGet();
        assertEquals(Integer.MAX_VALUE, result);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
    }

    // --- doubleValue() ---
    @Test
    @DisplayName("doubleValue(): Test normal conversion")
    void testDoubleValueNormal() {
        mutableInt.setValue(123);
        assertEquals(123.0, mutableInt.doubleValue(), 0.001);
    }

    @Test
    @DisplayName("doubleValue(): Test zero conversion")
    void testDoubleValueZero() {
        assertEquals(0.0, mutableInt.doubleValue(), 0.001);
    }

    @Test
    @DisplayName("doubleValue(): Test negative conversion")
    void testDoubleValueNegative() {
        mutableInt.setValue(-123);
        assertEquals(-123.0, mutableInt.doubleValue(), 0.001);
    }

    @Test
    @DisplayName("doubleValue(): Test max int conversion")
    void testDoubleValueMaxInt() {
        mutableInt.setValue(Integer.MAX_VALUE);
        assertEquals((double) Integer.MAX_VALUE, mutableInt.doubleValue(), 0.001);
    }

    @Test
    @DisplayName("doubleValue(): Test min int conversion")
    void testDoubleValueMinInt() {
        mutableInt.setValue(Integer.MIN_VALUE);
        assertEquals((double) Integer.MIN_VALUE, mutableInt.doubleValue(), 0.001);
    }

    // --- equals(Object obj) ---
    @Test
    @DisplayName("equals: Test with self")
    void testEqualsSelf() {
        assertTrue(mutableInt.equals(mutableInt));
    }

    @Test
    @DisplayName("equals: Test with null object")
    void testEqualsNull() {
        assertFalse(mutableInt.equals(null));
    }

    @Test
    @DisplayName("equals: Test with different class object")
    void testEqualsDifferentClass() {
        assertFalse(mutableInt.equals("a string"));
    }

    @Test
    @DisplayName("equals: Test with equal MutableInt")
    void testEqualsEqualMutableInt() {
        MutableInt other = new MutableInt(0);
        assertTrue(mutableInt.equals(other));
    }

    @Test
    @DisplayName("equals: Test with different MutableInt value")
    void testEqualsDifferentMutableInt() {
        MutableInt other = new MutableInt(5);
        assertFalse(mutableInt.equals(other));
    }

    @Test
    @DisplayName("equals: Test with equal Integer object")
    void testEqualsEqualInteger() {
        assertTrue(mutableInt.equals(Integer.valueOf(0)));
    }

    @Test
    @DisplayName("equals: Test with different Integer object")
    void testEqualsDifferentInteger() {
        assertFalse(mutableInt.equals(Integer.valueOf(5)));
    }

    @Test
    @DisplayName("equals: Test with equal Long object (within int range)")
    void testEqualsEqualLong() {
        assertTrue(mutableInt.equals(Long.valueOf(0L)));
    }

    @Test
    @DisplayName("equals: Test with different Long object (within int range)")
    void testEqualsDifferentLong() {
        assertFalse(mutableInt.equals(Long.valueOf(5L)));
    }

    @Test
    @DisplayName("equals: Test with Long object outside int range - should be false")
    void testEqualsLongOutOfIntRange() {
        mutableInt.setValue(1);
        assertFalse(mutableInt.equals(Long.valueOf(Integer.MAX_VALUE + 1L)));
    }

    @Test
    @DisplayName("equals: Test with equal Double object (exact int value)")
    void testEqualsEqualDouble() {
        assertTrue(mutableInt.equals(Double.valueOf(0.0)));
    }

    @Test
    @DisplayName("equals: Test with different Double object (exact int value)")
    void testEqualsDifferentDouble() {
        assertFalse(mutableInt.equals(Double.valueOf(5.0)));
    }

    @Test
    @DisplayName("equals: Test with Double object with fractional part - should be false")
    void testEqualsDoubleFractional() {
        assertFalse(mutableInt.equals(Double.valueOf(0.5)));
    }

    // --- floatValue() ---
    @Test
    @DisplayName("floatValue(): Test normal conversion")
    void testFloatValueNormal() {
        mutableInt.setValue(123);
        assertEquals(123.0f, mutableInt.floatValue(), 0.001f);
    }

    @Test
    @DisplayName("floatValue(): Test zero conversion")
    void testFloatValueZero() {
        assertEquals(0.0f, mutableInt.floatValue(), 0.001f);
    }

    @Test
    @DisplayName("floatValue(): Test negative conversion")
    void testFloatValueNegative() {
        mutableInt.setValue(-123);
        assertEquals(-123.0f, mutableInt.floatValue(), 0.001f);
    }

    @Test
    @DisplayName("floatValue(): Test max int conversion")
    void testFloatValueMaxInt() {
        mutableInt.setValue(Integer.MAX_VALUE);
        assertEquals((float) Integer.MAX_VALUE, mutableInt.floatValue(), 0.001f);
    }

    @Test
    @DisplayName("floatValue(): Test min int conversion")
    void testFloatValueMinInt() {
        mutableInt.setValue(Integer.MIN_VALUE);
        assertEquals((float) Integer.MIN_VALUE, mutableInt.floatValue(), 0.001f);
    }

    // --- getAndAdd(int operand) ---
    @Test
    @DisplayName("getAndAdd(int operand): Test normal positive addition and return old value")
    void testGetAndAddIntNormalPositive() {
        mutableInt.setValue(10);
        int oldValue = mutableInt.getAndAdd(5);
        assertEquals(10, oldValue);
        assertEquals(15, mutableInt.intValue());
    }

    @Test
    @DisplayName("getAndAdd(int operand): Test normal negative addition and return old value")
    void testGetAndAddIntNormalNegative() {
        mutableInt.setValue(10);
        int oldValue = mutableInt.getAndAdd(-5);
        assertEquals(10, oldValue);
        assertEquals(5, mutableInt.intValue());
    }

    @Test
    @DisplayName("getAndAdd(int operand): Test overflow and return old value")
    void testGetAndAddIntOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        int oldValue = mutableInt.getAndAdd(1);
        assertEquals(Integer.MAX_VALUE, oldValue);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- getAndAdd(Number operand) ---
    @ParameterizedTest
    @MethodSource("numberProviderForAdd")
    @DisplayName("getAndAdd(Number operand): Test with various Number types and return old value")
    void testGetAndAddNumberVariousTypes(Number operand, int expectedNewValue) {
        mutableInt.setValue(10);
        int oldValue = mutableInt.getAndAdd(operand);
        assertEquals(10, oldValue);
        assertEquals(expectedNewValue, mutableInt.intValue());
    }

    @Test
    @DisplayName("getAndAdd(Number operand): Test with null operand - should throw NullPointerException")
    void testGetAndAddNumberNull() {
        assertThrows(NullPointerException.class, () -> mutableInt.getAndAdd((Number) null));
    }

    // --- getAndDecrement() ---
    @Test
    @DisplayName("getAndDecrement(): Test normal decrement and return old value")
    void testGetAndDecrementNormal() {
        mutableInt.setValue(5);
        int oldValue = mutableInt.getAndDecrement();
        assertEquals(5, oldValue);
        assertEquals(4, mutableInt.intValue());
    }

    @Test
    @DisplayName("getAndDecrement(): Test underflow and return old value")
    void testGetAndDecrementUnderflow() {
        mutableInt.setValue(Integer.MIN_VALUE);
        int oldValue = mutableInt.getAndDecrement();
        assertEquals(Integer.MIN_VALUE, oldValue);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
    }

    // --- getAndIncrement() ---
    @Test
    @DisplayName("getAndIncrement(): Test normal increment and return old value")
    void testGetAndIncrementNormal() {
        mutableInt.setValue(5);
        int oldValue = mutableInt.getAndIncrement();
        assertEquals(5, oldValue);
        assertEquals(6, mutableInt.intValue());
    }

    @Test
    @DisplayName("getAndIncrement(): Test overflow and return old value")
    void testGetAndIncrementOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        int oldValue = mutableInt.getAndIncrement();
        assertEquals(Integer.MAX_VALUE, oldValue);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- getValue() ---
    @Test
    @DisplayName("getValue(): Test normal retrieval")
    void testGetValueNormal() {
        mutableInt.setValue(123);
        assertEquals(Integer.valueOf(123), mutableInt.getValue());
    }

    @Test
    @DisplayName("getValue(): Test zero retrieval")
    void testGetValueZero() {
        assertEquals(Integer.valueOf(0), mutableInt.getValue());
    }

    @Test
    @DisplayName("getValue(): Test negative retrieval")
    void testGetValueNegative() {
        mutableInt.setValue(-123);
        assertEquals(Integer.valueOf(-123), mutableInt.getValue());
    }

    // --- hashCode() ---
    @Test
    @DisplayName("hashCode(): Test consistent hash code for equal objects")
    void testHashCodeConsistent() {
        MutableInt other = new MutableInt(0);
        assertEquals(mutableInt.hashCode(), other.hashCode());
    }

    @Test
    @DisplayName("hashCode(): Test hash code changes with value")
    void testHashCodeChangesWithValue() {
        int initialHashCode = mutableInt.hashCode();
        mutableInt.setValue(5);
        assertNotEquals(initialHashCode, mutableInt.hashCode());
    }

    @Test
    @DisplayName("hashCode(): Test hash code for specific values")
    void testHashCodeSpecificValues() {
        mutableInt.setValue(123);
        assertEquals(Integer.valueOf(123).hashCode(), mutableInt.hashCode());
        mutableInt.setValue(-456);
        assertEquals(Integer.valueOf(-456).hashCode(), mutableInt.hashCode());
        mutableInt.setValue(0);
        assertEquals(Integer.valueOf(0).hashCode(), mutableInt.hashCode());
    }

    // --- increment() ---
    @Test
    @DisplayName("increment(): Test normal increment")
    void testIncrementNormal() {
        mutableInt.setValue(5);
        mutableInt.increment();
        assertEquals(6, mutableInt.intValue());
    }

    @Test
    @DisplayName("increment(): Test increment from zero")
    void testIncrementFromZero() {
        mutableInt.increment();
        assertEquals(1, mutableInt.intValue());
    }

    @Test
    @DisplayName("increment(): Test increment from negative value")
    void testIncrementFromNegative() {
        mutableInt.setValue(-5);
        mutableInt.increment();
        assertEquals(-4, mutableInt.intValue());
    }

    @Test
    @DisplayName("increment(): Test integer overflow")
    void testIncrementOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        mutableInt.increment();
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue()); // Expected overflow behavior
    }

    // --- incrementAndGet() ---
    @Test
    @DisplayName("incrementAndGet(): Test normal increment and return")
    void testIncrementAndGetNormal() {
        mutableInt.setValue(5);
        int result = mutableInt.incrementAndGet();
        assertEquals(6, result);
        assertEquals(6, mutableInt.intValue());
    }

    @Test
    @DisplayName("incrementAndGet(): Test overflow and return")
    void testIncrementAndGetOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        int result = mutableInt.incrementAndGet();
        assertEquals(Integer.MIN_VALUE, result);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- intValue() ---
    @Test
    @DisplayName("intValue(): Test normal retrieval")
    void testIntValueNormal() {
        mutableInt.setValue(123);
        assertEquals(123, mutableInt.intValue());
    }

    @Test
    @DisplayName("intValue(): Test zero retrieval")
    void testIntValueZero() {
        assertEquals(0, mutableInt.intValue());
    }

    @Test
    @DisplayName("intValue(): Test negative retrieval")
    void testIntValueNegative() {
        mutableInt.setValue(-123);
        assertEquals(-123, mutableInt.intValue());
    }

    @Test
    @DisplayName("intValue(): Test max int retrieval")
    void testIntValueMaxInt() {
        mutableInt.setValue(Integer.MAX_VALUE);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
    }

    @Test
    @DisplayName("intValue(): Test min int retrieval")
    void testIntValueMinInt() {
        mutableInt.setValue(Integer.MIN_VALUE);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- longValue() ---
    @Test
    @DisplayName("longValue(): Test normal conversion")
    void testLongValueNormal() {
        mutableInt.setValue(123);
        assertEquals(123L, mutableInt.longValue());
    }

    @Test
    @DisplayName("longValue(): Test zero conversion")
    void testLongValueZero() {
        assertEquals(0L, mutableInt.longValue());
    }

    @Test
    @DisplayName("longValue(): Test negative conversion")
    void testLongValueNegative() {
        mutableInt.setValue(-123);
        assertEquals(-123L, mutableInt.longValue());
    }

    @Test
    @DisplayName("longValue(): Test max int conversion")
    void testLongValueMaxInt() {
        mutableInt.setValue(Integer.MAX_VALUE);
        assertEquals((long) Integer.MAX_VALUE, mutableInt.longValue());
    }

    @Test
    @DisplayName("longValue(): Test min int conversion")
    void testLongValueMinInt() {
        mutableInt.setValue(Integer.MIN_VALUE);
        assertEquals((long) Integer.MIN_VALUE, mutableInt.longValue());
    }

    // --- setValue(int value) ---
    @Test
    @DisplayName("setValue(int value): Test setting positive value")
    void testSetIntValuePositive() {
        mutableInt.setValue(100);
        assertEquals(100, mutableInt.intValue());
    }

    @Test
    @DisplayName("setValue(int value): Test setting negative value")
    void testSetIntValueNegative() {
        mutableInt.setValue(-100);
        assertEquals(-100, mutableInt.intValue());
    }

    @Test
    @DisplayName("setValue(int value): Test setting zero")
    void testSetIntValueZero() {
        mutableInt.setValue(10); // Change from initial
        mutableInt.setValue(0);
        assertEquals(0, mutableInt.intValue());
    }

    @Test
    @DisplayName("setValue(int value): Test setting max int")
    void testSetIntValueMaxInt() {
        mutableInt.setValue(Integer.MAX_VALUE);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
    }

    @Test
    @DisplayName("setValue(int value): Test setting min int")
    void testSetIntValueMinInt() {
        mutableInt.setValue(Integer.MIN_VALUE);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- setValue(Number value) ---
    @ParameterizedTest
    @MethodSource("numberProviderForSetValue")
    @DisplayName("setValue(Number value): Test with various Number types")
    void testSetNumberValueVariousTypes(Number value, int expected) {
        mutableInt.setValue(value);
        assertEquals(expected, mutableInt.intValue());
    }

    private static Stream<Arguments> numberProviderForSetValue() {
        return Stream.of(
                Arguments.of(123, 123),
                Arguments.of(123L, 123),
                Arguments.of(123.0f, 123),
                Arguments.of(123.99, 123), // Expect truncation
                Arguments.of(new BigInteger("456"), 456),
                Arguments.of(new BigDecimal("789.123"), 789), // Expect truncation
                Arguments.of(Integer.MAX_VALUE, Integer.MAX_VALUE),
                Arguments.of(Integer.MIN_VALUE, Integer.MIN_VALUE),
                Arguments.of(Long.valueOf(Integer.MAX_VALUE + 1L), Integer.MAX_VALUE + 1), // Expect overflow/truncation to int
                Arguments.of(Long.valueOf(Integer.MIN_VALUE - 1L), Integer.MIN_VALUE - 1)  // Expect underflow/truncation to int
        );
    }

    @Test
    @DisplayName("setValue(Number value): Test with null value - should throw NullPointerException")
    void testSetNumberValueNull() {
        assertThrows(NullPointerException.class, () -> mutableInt.setValue((Number) null));
    }

    // --- subtract(int operand) ---
    @Test
    @DisplayName("subtract(int operand): Test normal positive subtraction")
    void testSubtractIntNormalPositive() {
        mutableInt.setValue(10);
        mutableInt.subtract(5);
        assertEquals(5, mutableInt.intValue());
    }

    @Test
    @DisplayName("subtract(int operand): Test normal negative subtraction (addition)")
    void testSubtractIntNormalNegative() {
        mutableInt.setValue(10);
        mutableInt.subtract(-5);
        assertEquals(15, mutableInt.intValue());
    }

    @Test
    @DisplayName("subtract(int operand): Test subtracting zero")
    void testSubtractIntZero() {
        mutableInt.setValue(10);
        mutableInt.subtract(0);
        assertEquals(10, mutableInt.intValue());
    }

    @Test
    @DisplayName("subtract(int operand): Test integer underflow (positive to negative)")
    void testSubtractIntUnderflow() {
        mutableInt.setValue(Integer.MIN_VALUE);
        mutableInt.subtract(1);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue()); // Expected underflow behavior
    }

    @Test
    @DisplayName("subtract(int operand): Test integer overflow (negative to positive)")
    void testSubtractIntOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        mutableInt.subtract(-1);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue()); // Expected overflow behavior
    }

    // --- subtract(Number operand) ---
    @ParameterizedTest
    @MethodSource("numberProviderForSubtract")
    @DisplayName("subtract(Number operand): Test with various Number types")
    void testSubtractNumberVariousTypes(Number operand, int expected) {
        mutableInt.setValue(10);
        mutableInt.subtract(operand);
        assertEquals(expected, mutableInt.intValue());
    }

    private static Stream<Arguments> numberProviderForSubtract() {
        return Stream.of(
                Arguments.of(5, 5),
                Arguments.of(5L, 5),
                Arguments.of(5.0f, 5),
                Arguments.of(5.99, 5), // Expect truncation
                Arguments.of(new BigInteger("5"), 5),
                Arguments.of(new BigDecimal("5.123"), 5), // Expect truncation
                Arguments.of(-5, 15),
                Arguments.of(0, 10)
        );
    }

    @Test
    @DisplayName("subtract(Number operand): Test with null operand - should throw NullPointerException")
    void testSubtractNumberNull() {
        assertThrows(NullPointerException.class, () -> mutableInt.subtract((Number) null));
    }

    @Test
    @DisplayName("subtract(Number operand): Test underflow with Number (Integer.MIN_VALUE - 1)")
    void testSubtractNumberUnderflow() {
        mutableInt.setValue(Integer.MIN_VALUE);
        mutableInt.subtract(1);
        assertEquals(Integer.MAX_VALUE, mutableInt.intValue());
    }

    @Test
    @DisplayName("subtract(Number operand): Test overflow with Number (Integer.MAX_VALUE - (-1))")
    void testSubtractNumberOverflow() {
        mutableInt.setValue(Integer.MAX_VALUE);
        mutableInt.subtract(-1);
        assertEquals(Integer.MIN_VALUE, mutableInt.intValue());
    }

    // --- toInteger() ---
    @Test
    @DisplayName("toInteger(): Test normal conversion")
    void testToIntegerNormal() {
        mutableInt.setValue(123);
        assertEquals(Integer.valueOf(123), mutableInt.toInteger());
        assertNotSame(mutableInt.getValue(), mutableInt.toInteger()); // Should return a new Integer object
    }

    @Test
    @DisplayName("toInteger(): Test zero conversion")
    void testToIntegerZero() {
        assertEquals(Integer.valueOf(0), mutableInt.toInteger());
    }

    @Test
    @DisplayName("toInteger(): Test negative conversion")
    void testToIntegerNegative() {
        mutableInt.setValue(-123);
        assertEquals(Integer.valueOf(-123), mutableInt.toInteger());
    }

    // --- toString() ---
    @Test
    @DisplayName("toString(): Test normal string representation")
    void testToStringNormal() {
        mutableInt.setValue(123);
        assertEquals("123", mutableInt.toString());
    }

    @Test
    @DisplayName("toString(): Test zero string representation")
    void testToStringZero() {
        assertEquals("0", mutableInt.toString());
    }

    @Test
    @DisplayName("toString(): Test negative string representation")
    void testToStringNegative() {
        mutableInt.setValue(-123);
        assertEquals("-123", mutableInt.toString());
    }

    @Test
    @DisplayName("toString(): Test max int string representation")
    void testToStringMaxInt() {
        mutableInt.setValue(Integer.MAX_VALUE);
        assertEquals(String.valueOf(Integer.MAX_VALUE), mutableInt.toString());
    }

    @Test
    @DisplayName("toString(): Test min int string representation")
    void testToStringMinInt() {
        mutableInt.setValue(Integer.MIN_VALUE);
        assertEquals(String.valueOf(Integer.MIN_VALUE), mutableInt.toString());
    }
}