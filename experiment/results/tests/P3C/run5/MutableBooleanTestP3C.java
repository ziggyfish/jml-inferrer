package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class MutableBooleanTestP3CP3C {

    // Test booleanValue()
    // @ensures \result == this.value;
    @Test
    void testBooleanValue_true() {
        MutableBoolean mb = new MutableBoolean(true);
        assertTrue(mb.booleanValue());
    }

    @Test
    void testBooleanValue_false() {
        MutableBoolean mb = new MutableBoolean(false);
        assertFalse(mb.booleanValue());
    }

    // Test compareTo(final MutableBoolean other)
    // @requires other != null;
    // @ensures \result == (this.value == other.value ? 0 : (this.value ? 1 : -1));
    @Test
    void testCompareTo_equalTrue() {
        MutableBoolean mb1 = new MutableBoolean(true);
        MutableBoolean mb2 = new MutableBoolean(true);
        assertEquals(0, mb1.compareTo(mb2));
    }

    @Test
    void testCompareTo_equalFalse() {
        MutableBoolean mb1 = new MutableBoolean(false);
        MutableBoolean mb2 = new MutableBoolean(false);
        assertEquals(0, mb1.compareTo(mb2));
    }

    @Test
    void testCompareTo_thisTrueOtherFalse() {
        MutableBoolean mb1 = new MutableBoolean(true);
        MutableBoolean mb2 = new MutableBoolean(false);
        assertTrue(mb1.compareTo(mb2) > 0); // true is greater than false
    }

    @Test
    void testCompareTo_thisFalseOtherTrue() {
        MutableBoolean mb1 = new MutableBoolean(false);
        MutableBoolean mb2 = new MutableBoolean(true);
        assertTrue(mb1.compareTo(mb2) < 0); // false is less than true
    }

    @Test
    void testCompareTo_nullOther_throwsNullPointerException() {
        MutableBoolean mb = new MutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.compareTo(null));
    }

    // Test equals(final Object obj)
    // @ensures \result == (obj instanceof MutableBoolean && ((MutableBoolean)obj).value == this.value);
    @Test
    void testEquals_sameObject() {
        MutableBoolean mb = new MutableBoolean(true);
        assertEquals(mb, mb);
    }

    @Test
    void testEquals_equalMutableBooleanTrue() {
        MutableBoolean mb1 = new MutableBoolean(true);
        MutableBoolean mb2 = new MutableBoolean(true);
        assertEquals(mb1, mb2);
    }

    @Test
    void testEquals_equalMutableBooleanFalse() {
        MutableBoolean mb1 = new MutableBoolean(false);
        MutableBoolean mb2 = new MutableBoolean(false);
        assertEquals(mb1, mb2);
    }

    @Test
    void testEquals_differentMutableBoolean() {
        MutableBoolean mb1 = new MutableBoolean(true);
        MutableBoolean mb2 = new MutableBoolean(false);
        assertNotEquals(mb1, mb2);
    }

    @Test
    void testEquals_nullObject() {
        MutableBoolean mb = new MutableBoolean(true);
        assertNotEquals(mb, null);
    }

    @Test
    void testEquals_differentClass() {
        MutableBoolean mb = new MutableBoolean(true);
        assertNotEquals(mb, "a string");
    }

    @Test
    void testEquals_differentClassWithSameValue() {
        MutableBoolean mb = new MutableBoolean(true);
        // This is a bit of a contrived test, as Boolean is not MutableBoolean
        assertNotEquals(mb, Boolean.TRUE);
    }

    // Test getValue()
    // @ensures \result != null && \result.booleanValue() == this.value;
    @Test
    void testGetValue_true() {
        MutableBoolean mb = new MutableBoolean(true);
        assertEquals(Boolean.TRUE, mb.getValue());
    }

    @Test
    void testGetValue_false() {
        MutableBoolean mb = new MutableBoolean(false);
        assertEquals(Boolean.FALSE, mb.getValue());
    }

    @Test
    void testGetValue_notNull() {
        MutableBoolean mb = new MutableBoolean(true);
        assertNotNull(mb.getValue());
    }

    // Test hashCode()
    // @ensures \result == (this.value ? Boolean.TRUE.hashCode() : Boolean.FALSE.hashCode());
    @Test
    void testHashCode_true() {
        MutableBoolean mb = new MutableBoolean(true);
        assertEquals(Boolean.TRUE.hashCode(), mb.hashCode());
    }

    @Test
    void testHashCode_false() {
        MutableBoolean mb = new MutableBoolean(false);
        assertEquals(Boolean.FALSE.hashCode(), mb.hashCode());
    }

    @Test
    void testHashCode_consistency() {
        MutableBoolean mb1 = new MutableBoolean(true);
        MutableBoolean mb2 = new MutableBoolean(true);
        assertEquals(mb1.hashCode(), mb2.hashCode());

        MutableBoolean mb3 = new MutableBoolean(false);
        MutableBoolean mb4 = new MutableBoolean(false);
        assertEquals(mb3.hashCode(), mb4.hashCode());
    }

    // Test isFalse()
    // @ensures \result == !this.value;
    @Test
    void testIsFalse_whenTrue() {
        MutableBoolean mb = new MutableBoolean(true);
        assertFalse(mb.isFalse());
    }

    @Test
    void testIsFalse_whenFalse() {
        MutableBoolean mb = new MutableBoolean(false);
        assertTrue(mb.isFalse());
    }

    // Test isTrue()
    // @ensures \result == this.value;
    @Test
    void testIsTrue_whenTrue() {
        MutableBoolean mb = new MutableBoolean(true);
        assertTrue(mb.isTrue());
    }

    @Test
    void testIsTrue_whenFalse() {
        MutableBoolean mb = new MutableBoolean(false);
        assertFalse(mb.isTrue());
    }

    // Test setFalse()
    // @ensures this.value == false;
    @Test
    void testSetFalse_fromTrue() {
        MutableBoolean mb = new MutableBoolean(true);
        mb.setFalse();
        assertFalse(mb.booleanValue());
        assertTrue(mb.isFalse());
        assertFalse(mb.isTrue());
    }

    @Test
    void testSetFalse_fromFalse() {
        MutableBoolean mb = new MutableBoolean(false);
        mb.setFalse();
        assertFalse(mb.booleanValue());
        assertTrue(mb.isFalse());
        assertFalse(mb.isTrue());
    }

    // Test setTrue()
    // @ensures this.value == true;
    @Test
    void testSetTrue_fromFalse() {
        MutableBoolean mb = new MutableBoolean(false);
        mb.setTrue();
        assertTrue(mb.booleanValue());
        assertFalse(mb.isFalse());
        assertTrue(mb.isTrue());
    }

    @Test
    void testSetTrue_fromTrue() {
        MutableBoolean mb = new MutableBoolean(true);
        mb.setTrue();
        assertTrue(mb.booleanValue());
        assertFalse(mb.isFalse());
        assertTrue(mb.isTrue());
    }

    // Test setValue(final boolean value)
    // @ensures this.value == value;
    @ParameterizedTest
    @ValueSource(booleans = {true, false})
    void testSetValue_boolean(boolean value) {
        MutableBoolean mb = new MutableBoolean(!value); // Initialize with opposite value
        mb.setValue(value);
        assertEquals(value, mb.booleanValue());
    }

    // Test setValue(final Boolean value)
    // @requires value != null;
    // @ensures this.value == value.booleanValue();
    @ParameterizedTest
    @CsvSource({"TRUE", "FALSE"})
    void testSetValue_Boolean(Boolean value) {
        MutableBoolean mb = new MutableBoolean(!value); // Initialize with opposite value
        mb.setValue(value);
        assertEquals(value.booleanValue(), mb.booleanValue());
    }

    @Test
    void testSetValue_Boolean_null_throwsNullPointerException() {
        MutableBoolean mb = new MutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.setValue((Boolean) null));
    }

    // Test toBoolean()
    // @ensures \result != null && \result.booleanValue() == this.value;
    @Test
    void testToBoolean_true() {
        MutableBoolean mb = new MutableBoolean(true);
        assertEquals(Boolean.TRUE, mb.toBoolean());
    }

    @Test
    void testToBoolean_false() {
        MutableBoolean mb = new MutableBoolean(false);
        assertEquals(Boolean.FALSE, mb.toBoolean());
    }

    @Test
    void testToBoolean_notNull() {
        MutableBoolean mb = new MutableBoolean(true);
        assertNotNull(mb.toBoolean());
    }

    // Test toString()
    // @ensures \result != null && \result.equals(String.valueOf(this.value));
    @Test
    void testToString_true() {
        MutableBoolean mb = new MutableBoolean(true);
        assertEquals("true", mb.toString());
    }

    @Test
    void testToString_false() {
        MutableBoolean mb = new MutableBoolean(false);
        assertEquals("false", mb.toString());
    }

    @Test
    void testToString_notNull() {
        MutableBoolean mb = new MutableBoolean(true);
        assertNotNull(mb.toString());
    }

    // Constructor tests (not explicitly in the provided signatures, but good to cover)
    @Test
    void testConstructor_default() {
        MutableBoolean mb = new MutableBoolean();
        assertFalse(mb.booleanValue()); // Default is false
    }

    @Test
    void testConstructor_boolean() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertTrue(mbTrue.booleanValue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertFalse(mbFalse.booleanValue());
    }

    @Test
    void testConstructor_Boolean() {
        MutableBoolean mbTrue = new MutableBoolean(Boolean.TRUE);
        assertTrue(mbTrue.booleanValue());

        MutableBoolean mbFalse = new MutableBoolean(Boolean.FALSE);
        assertFalse(mbFalse.booleanValue());
    }

    @Test
    void testConstructor_Boolean_null_throwsNullPointerException() {
        assertThrows(NullPointerException.class, () -> new MutableBoolean((Boolean) null));
    }
}