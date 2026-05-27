package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class MutableBooleanTestP3P3 {

    // Test for booleanValue()
    // @ensures \result == this.value;
    @Test
    void testBooleanValue() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertTrue(mbTrue.booleanValue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertFalse(mbFalse.booleanValue());

        // After change
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

        // Same value
        assertEquals(0, mbTrue1.compareTo(mbTrue2));
        assertEquals(0, mbFalse1.compareTo(mbFalse2));

        // This is true, other is false (true > false)
        assertTrue(mbTrue1.compareTo(mbFalse1) > 0);
        assertEquals(1, mbTrue1.compareTo(mbFalse1)); // JML specifies 1

        // This is false, other is true (false < true)
        assertTrue(mbFalse1.compareTo(mbTrue1) < 0);
        assertEquals(-1, mbFalse1.compareTo(mbTrue1)); // JML specifies -1

        // Test after value change
        mbTrue1.setValue(false);
        assertEquals(0, mbTrue1.compareTo(mbFalse1));
        assertTrue(mbFalse1.compareTo(mbTrue2) < 0);
    }

    @Test
    void testCompareTo_nullOther_throwsNPE() {
        MutableBoolean mb = new MutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.compareTo(null));
    }

    // Test for equals(final Object obj)
    // @ensures \result == (obj instanceof MutableBoolean && ((MutableBoolean)obj).value == this.value);
    @Test
    void testEquals() {
        MutableBoolean mbTrue1 = new MutableBoolean(true);
        MutableBoolean mbTrue2 = new MutableBoolean(true);
        MutableBoolean mbFalse1 = new MutableBoolean(false);
        MutableBoolean mbFalse2 = new MutableBoolean(false);

        // Same object
        assertEquals(mbTrue1, mbTrue1);

        // Equal values
        assertEquals(mbTrue1, mbTrue2);
        assertEquals(mbFalse1, mbFalse2);

        // Different values
        assertNotEquals(mbTrue1, mbFalse1);

        // Different type
        assertNotEquals(mbTrue1, new Object());
        assertNotEquals(mbTrue1, Boolean.TRUE);

        // Null object
        assertNotEquals(mbTrue1, null);

        // After value change
        mbTrue1.setValue(false);
        assertEquals(mbTrue1, mbFalse1);
        assertNotEquals(mbTrue1, mbTrue2);
    }

    // Test for getValue()
    // @ensures \result.booleanValue() == this.value;
    @Test
    void testGetValue() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertEquals(Boolean.TRUE, mbTrue.getValue());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertEquals(Boolean.FALSE, mbFalse.getValue());

        // After change
        mbTrue.setValue(false);
        assertEquals(Boolean.FALSE, mbTrue.getValue());

        mbFalse.setValue(true);
        assertEquals(Boolean.TRUE, mbFalse.getValue());
    }

    // Test for hashCode()
    // @ensures \result == Boolean.valueOf(this.value).hashCode();
    @Test
    void testHashCode() {
        MutableBoolean mbTrue1 = new MutableBoolean(true);
        MutableBoolean mbTrue2 = new MutableBoolean(true);
        MutableBoolean mbFalse1 = new MutableBoolean(false);
        MutableBoolean mbFalse2 = new MutableBoolean(false);

        // Equal objects must have equal hash codes
        assertEquals(mbTrue1.hashCode(), mbTrue2.hashCode());
        assertEquals(mbFalse1.hashCode(), mbFalse2.hashCode());

        // Hash codes should match Boolean.hashCode()
        assertEquals(Boolean.TRUE.hashCode(), mbTrue1.hashCode());
        assertEquals(Boolean.FALSE.hashCode(), mbFalse1.hashCode());

        // After value change
        mbTrue1.setValue(false);
        assertEquals(Boolean.FALSE.hashCode(), mbTrue1.hashCode());
        assertEquals(mbTrue1.hashCode(), mbFalse1.hashCode());
    }

    // Test for isFalse()
    // @ensures \result == !this.value;
    @Test
    void testIsFalse() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertFalse(mbTrue.isFalse());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertTrue(mbFalse.isFalse());

        // After change
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

        // After change
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
        assertTrue(mb.booleanValue());

        mb.setFalse();
        assertFalse(mb.booleanValue());
        assertFalse(mb.isTrue());
        assertTrue(mb.isFalse());

        // Calling again should not change state
        mb.setFalse();
        assertFalse(mb.booleanValue());
    }

    // Test for setTrue()
    // @ensures this.value == true;
    @Test
    void testSetTrue() {
        MutableBoolean mb = new MutableBoolean(false);
        assertFalse(mb.booleanValue());

        mb.setTrue();
        assertTrue(mb.booleanValue());
        assertTrue(mb.isTrue());
        assertFalse(mb.isFalse());

        // Calling again should not change state
        mb.setTrue();
        assertTrue(mb.booleanValue());
    }

    // Test for setValue(final boolean value)
    // @ensures this.value == value;
    @Test
    void testSetValue_boolean() {
        MutableBoolean mb = new MutableBoolean(false);
        assertFalse(mb.booleanValue());

        mb.setValue(true);
        assertTrue(mb.booleanValue());
        assertTrue(mb.isTrue());
        assertFalse(mb.isFalse());

        mb.setValue(false);
        assertFalse(mb.booleanValue());
        assertFalse(mb.isTrue());
        assertTrue(mb.isFalse());
    }

    // Test for setValue(final Boolean value)
    // @requires value != null;
    // @ensures this.value == value.booleanValue();
    @Test
    void testSetValue_Boolean() {
        MutableBoolean mb = new MutableBoolean(false);
        assertFalse(mb.booleanValue());

        mb.setValue(Boolean.TRUE);
        assertTrue(mb.booleanValue());
        assertTrue(mb.isTrue());
        assertFalse(mb.isFalse());

        mb.setValue(Boolean.FALSE);
        assertFalse(mb.booleanValue());
        assertFalse(mb.isTrue());
        assertTrue(mb.isFalse());
    }

    @Test
    void testSetValue_Boolean_nullValue_throwsNPE() {
        MutableBoolean mb = new MutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.setValue((Boolean) null));
    }

    // Test for toBoolean()
    // @ensures \result.booleanValue() == this.value;
    @Test
    void testToBoolean() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertEquals(Boolean.TRUE, mbTrue.toBoolean());
        assertSame(Boolean.TRUE, mbTrue.toBoolean()); // Should return cached Boolean instance

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertEquals(Boolean.FALSE, mbFalse.toBoolean());
        assertSame(Boolean.FALSE, mbFalse.toBoolean()); // Should return cached Boolean instance

        // After change
        mbTrue.setValue(false);
        assertEquals(Boolean.FALSE, mbTrue.toBoolean());
        assertSame(Boolean.FALSE, mbTrue.toBoolean());

        mbFalse.setValue(true);
        assertEquals(Boolean.TRUE, mbFalse.toBoolean());
        assertSame(Boolean.TRUE, mbFalse.toBoolean());
    }

    // Test for toString()
    // @ensures \result.equals(Boolean.valueOf(this.value).toString());
    @Test
    void testToString() {
        MutableBoolean mbTrue = new MutableBoolean(true);
        assertEquals("true", mbTrue.toString());

        MutableBoolean mbFalse = new MutableBoolean(false);
        assertEquals("false", mbFalse.toString());

        // After change
        mbTrue.setValue(false);
        assertEquals("false", mbTrue.toString());

        mbFalse.setValue(true);
        assertEquals("true", mbFalse.toString());
    }

    // Constructor tests (not explicitly in JML, but good to cover)
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
    void testConstructor_Boolean_null() {
        // JML for constructor is not provided, but typically null Boolean would result in false
        MutableBoolean mbNull = new MutableBoolean((Boolean) null);
        assertFalse(mbNull.booleanValue());
    }

    @Test
    void testConstructor_String() {
        MutableBoolean mbTrue = new MutableBoolean("true");
        assertTrue(mbTrue.booleanValue());

        MutableBoolean mbFalse = new MutableBoolean("false");
        assertFalse(mbFalse.booleanValue());

        MutableBoolean mbOther = new MutableBoolean("any other string");
        assertFalse(mbOther.booleanValue()); // Any string other than "true" (case-insensitive) is false
    }

    @Test
    void testConstructor_String_null() {
        MutableBoolean mbNull = new MutableBoolean((String) null);
        assertFalse(mbNull.booleanValue());
    }
}