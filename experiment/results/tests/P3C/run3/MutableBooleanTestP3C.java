package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class MutableBooleanTestP3CP3C {

    // Test for booleanValue()
    // @ensures \result == this.value;
    @Test
    void testBooleanValue() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertTrue(mbTrue.booleanValue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertFalse(mbFalse.booleanValue());

        // Test after modification
        mbTrue.setValue(false);
        assertFalse(mbTrue.booleanValue());

        mbFalse.setValue(true);
        assertTrue(mbFalse.booleanValue());
    }

    // Test for compareTo(final MutableBoolean other)
    // @requires other != null;
    // @ensures \result == (this.value == other.value ? 0 : (this.value ? 1 : -1));
    @Test
    void testCompareTo() {
        MutableBoolean mbTrue1 = new MutableBoolean(true);
        MutableBoolean mbTrue2 = new MutableBoolean(true);
        MutableBoolean mbFalse1 = new MutableBoolean(false);
        MutableBoolean mbFalse2 = new MutableBoolean(false);

        // Both true
        assertEquals(0, mbTrue1.compareTo(mbTrue2));
        assertEquals(0, mbTrue2.compareTo(mbTrue1));

        // Both false
        assertEquals(0, mbFalse1.compareTo(mbFalse2));
        assertEquals(0, mbFalse2.compareTo(mbFalse1));

        // This true, other false
        assertEquals(1, mbTrue1.compareTo(mbFalse1));

        // This false, other true
        assertEquals(-1, mbFalse1.compareTo(mbTrue1));

        // Test after modification
        mbTrue1.setValue(false);
        assertEquals(0, mbTrue1.compareTo(mbFalse1));
        assertEquals(-1, mbTrue1.compareTo(mbTrue2));
        assertEquals(1, mbTrue2.compareTo(mbTrue1));
    }

    @Test
    void testCompareTo_nullOther_throwsNPE() {
        MutableBoolean mb = new MutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.compareTo(null));
    }

    // Test for equals(final Object obj)
    // @ensures \result == (obj instanceof MutableBoolean && ((MutableBoolean) obj).booleanValue() == this.value);
    @Test
    void testEquals() {
        MutableBoolean mbTrue1 = new MutableBoolean(true);
        MutableBoolean mbTrue2 = new MutableBoolean(true);
        MutableBoolean mbFalse1 = new MutableBoolean(false);
        MutableBoolean mbFalse2 = new MutableBoolean(false);

        // Same object
        assertTrue(mbTrue1.equals(mbTrue1));
        assertTrue(mbFalse1.equals(mbFalse1));

        // Equal objects
        assertTrue(mbTrue1.equals(mbTrue2));
        assertTrue(mbFalse1.equals(mbFalse2));

        // Not equal objects
        assertFalse(mbTrue1.equals(mbFalse1));
        assertFalse(mbFalse1.equals(mbTrue1));

        // Different type
        assertFalse(mbTrue1.equals("true"));
        assertFalse(mbTrue1.equals(Boolean.TRUE)); // Even though it's a Boolean, it's not a MutableBoolean
        assertFalse(mbTrue1.equals(1));

        // Null object
        assertFalse(mbTrue1.equals(null));

        // Test after modification
        mbTrue1.setValue(false);
        assertTrue(mbTrue1.equals(mbFalse1));
        assertFalse(mbTrue1.equals(mbTrue2));
    }

    // Test for getValue()
    // @ensures \result != null && \result.booleanValue() == this.value;
    @Test
    void testGetValue() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertEquals(Boolean.TRUE, mbTrue.getValue());
        assertTrue(mbTrue.getValue().booleanValue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertEquals(Boolean.FALSE, mbFalse.getValue());
        assertFalse(mbFalse.getValue().booleanValue());

        // Test after modification
        mbTrue.setValue(false);
        assertEquals(Boolean.FALSE, mbTrue.getValue());

        mbFalse.setValue(true);
        assertEquals(Boolean.TRUE, mbFalse.getValue());
    }

    // Test for hashCode()
    // @ensures \result == (this.value ? Boolean.TRUE.hashCode() : Boolean.FALSE.hashCode());
    @Test
    void testHashCode() {
        MutableBoolean mbTrue1 = new MutableBoolean(true);
        MutableBoolean mbTrue2 = new MutableBoolean(true);
        MutableBoolean mbFalse1 = new MutableBoolean(false);
        MutableBoolean mbFalse2 = new MutableBoolean(false);

        // Equal objects must have equal hash codes
        assertEquals(mbTrue1.hashCode(), mbTrue2.hashCode());
        assertEquals(mbFalse1.hashCode(), mbFalse2.hashCode());

        // Hash codes should match Boolean.TRUE/FALSE hash codes
        assertEquals(Boolean.TRUE.hashCode(), mbTrue1.hashCode());
        assertEquals(Boolean.FALSE.hashCode(), mbFalse1.hashCode());

        // Different values should have different hash codes
        assertNotEquals(mbTrue1.hashCode(), mbFalse1.hashCode());

        // Test after modification
        mbTrue1.setValue(false);
        assertEquals(Boolean.FALSE.hashCode(), mbTrue1.hashCode());
        assertNotEquals(Boolean.TRUE.hashCode(), mbTrue1.hashCode());
    }

    // Test for isFalse()
    // @ensures \result == !this.value;
    @Test
    void testIsFalse() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertFalse(mbTrue.isFalse());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertTrue(mbFalse.isFalse());

        // Test after modification
        mbTrue.setValue(false);
        assertTrue(mbTrue.isFalse());

        mbFalse.setValue(true);
        assertFalse(mbFalse.isFalse());
    }

    // Test for isTrue()
    // @ensures \result == this.value;
    @Test
    void testIsTrue() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertTrue(mbTrue.isTrue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertFalse(mbFalse.isTrue());

        // Test after modification
        mbTrue.setValue(false);
        assertFalse(mbTrue.isTrue());

        mbFalse.setValue(true);
        assertTrue(mbFalse.isTrue());
    }

    // Test for setFalse()
    // @ensures this.value == false;
    @Test
    void testSetFalse() {
        MutableBoolean mb = new MutableBoolean(true);
        assertTrue(mb.booleanValue()); // Initially true

        mb.setFalse();
        assertFalse(mb.booleanValue());
        assertTrue(mb.isFalse());
        assertFalse(mb.isTrue());

        // Calling setFalse again should have no effect on the value
        mb.setFalse();
        assertFalse(mb.booleanValue());
    }

    // Test for setTrue()
    // @ensures this.value == true;
    @Test
    void testSetTrue() {
        MutableBoolean mb = new MutableBoolean(false);
        assertFalse(mb.booleanValue()); // Initially false

        mb.setTrue();
        assertTrue(mb.booleanValue());
        assertTrue(mb.isTrue());
        assertFalse(mb.isFalse());

        // Calling setTrue again should have no effect on the value
        mb.setTrue();
        assertTrue(mb.booleanValue());
    }

    // Test for setValue(final boolean value)
    // @ensures this.value == value;
    @ParameterizedTest
    @ValueSource(booleans = {true, false})
    void testSetValue_boolean(boolean value) {
        MutableBoolean mb = new MutableBoolean(!value); // Initialize with opposite value

        mb.setValue(value);
        assertEquals(value, mb.booleanValue());
        assertEquals(value, mb.isTrue());
        assertEquals(!value, mb.isFalse());
    }

    // Test for setValue(final Boolean value)
    // @requires value != null;
    // @ensures this.value == value.booleanValue();
    @ParameterizedTest
    @CsvSource({"true", "false"})
    void testSetValue_Boolean(boolean value) {
        MutableBoolean mb = new MutableBoolean(!value); // Initialize with opposite value

        mb.setValue(Boolean.valueOf(value));
        assertEquals(value, mb.booleanValue());
        assertEquals(value, mb.isTrue());
        assertEquals(!value, mb.isFalse());
    }

    @Test
    void testSetValue_Boolean_nullValue_throwsNPE() {
        MutableBoolean mb = new MutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.setValue((Boolean) null));
    }

    // Test for toBoolean()
    // @ensures \result != null && \result.booleanValue() == this.value;
    @Test
    void testToBoolean() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertEquals(Boolean.TRUE, mbTrue.toBoolean());
        assertTrue(mbTrue.toBoolean().booleanValue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertEquals(Boolean.FALSE, mbFalse.toBoolean());
        assertFalse(mbFalse.toBoolean().booleanValue());

        // Test after modification
        mbTrue.setValue(false);
        assertEquals(Boolean.FALSE, mbTrue.toBoolean());

        mbFalse.setValue(true);
        assertEquals(Boolean.TRUE, mbFalse.toBoolean());
    }

    // Test for toString()
    // @ensures \result != null && \result.equals(String.valueOf(this.value));
    @Test
    void testToString() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertEquals("true", mbTrue.toString());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertEquals("false", mbFalse.toString());

        // Test after modification
        mbTrue.setValue(false);
        assertEquals("false", mbTrue.toString());

        mbFalse.setValue(true);
        assertEquals("true", mbFalse.toString());
    }

    // Constructor tests (not explicitly in the provided signatures, but good to cover)
    @Test
    void testConstructor_default() {
        MutableBoolean mb = new MutableBoolean();
        assertFalse(mb.booleanValue()); // Default value is false
    }

    @ParameterizedTest
    @ValueSource(booleans = {true, false})
    void testConstructor_boolean(boolean value) {
        MutableBoolean mb = new MutableBoolean(value);
        assertEquals(value, mb.booleanValue());
    }

    @ParameterizedTest
    @CsvSource({"true", "false"})
    void testConstructor_Boolean(boolean value) {
        MutableBoolean mb = new MutableBoolean(Boolean.valueOf(value));
        assertEquals(value, mb.booleanValue());
    }

    @Test
    void testConstructor_Boolean_null() {
        assertThrows(NullPointerException.class, () -> new MutableBoolean((Boolean) null));
    }
}