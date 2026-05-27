package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

class MutableBooleanTestP3CP3C {

    // Helper method to create MutableBoolean instances for tests
    private MutableBoolean createMutableBoolean(boolean value) {
        return new MutableBoolean(value);
    }

    /*
     * Test for booleanValue()
     * public boolean booleanValue();
     * @ensures \result == this.value;
     */
    @Test
    void testBooleanValue_true() {
        MutableBoolean mb = createMutableBoolean(true);
        assertTrue(mb.booleanValue());
    }

    @Test
    void testBooleanValue_false() {
        MutableBoolean mb = createMutableBoolean(false);
        assertFalse(mb.booleanValue());
    }

    @Test
    void testBooleanValue_afterSetTrue() {
        MutableBoolean mb = createMutableBoolean(false);
        mb.setTrue();
        assertTrue(mb.booleanValue());
    }

    @Test
    void testBooleanValue_afterSetFalse() {
        MutableBoolean mb = createMutableBoolean(true);
        mb.setFalse();
        assertFalse(mb.booleanValue());
    }

    /*
     * Test for compareTo(final MutableBoolean other)
     * public int compareTo(final MutableBoolean other);
     * @requires other != null;
     * @ensures (\result == 0) <==> (this.value == other.value);
     * @ensures (\result < 0) <==> (!this.value && other.value);
     * @ensures (\result > 0) <==> (this.value && !other.value);
     */
    @Test
    void testCompareTo_equalValues_trueTrue() {
        MutableBoolean mb1 = createMutableBoolean(true);
        MutableBoolean mb2 = createMutableBoolean(true);
        assertEquals(0, mb1.compareTo(mb2));
    }

    @Test
    void testCompareTo_equalValues_falseFalse() {
        MutableBoolean mb1 = createMutableBoolean(false);
        MutableBoolean mb2 = createMutableBoolean(false);
        assertEquals(0, mb1.compareTo(mb2));
    }

    @Test
    void testCompareTo_thisFalseOtherTrue() {
        MutableBoolean mb1 = createMutableBoolean(false);
        MutableBoolean mb2 = createMutableBoolean(true);
        assertTrue(mb1.compareTo(mb2) < 0);
    }

    @Test
    void testCompareTo_thisTrueOtherFalse() {
        MutableBoolean mb1 = createMutableBoolean(true);
        MutableBoolean mb2 = createMutableBoolean(false);
        assertTrue(mb1.compareTo(mb2) > 0);
    }

    @Test
    void testCompareTo_self() {
        MutableBoolean mb = createMutableBoolean(true);
        assertEquals(0, mb.compareTo(mb));
    }

    @Test
    void testCompareTo_nullOther_throwsNullPointerException() {
        MutableBoolean mb = createMutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.compareTo(null));
    }

    /*
     * Test for equals(final Object obj)
     * public boolean equals(final Object obj);
     * @ensures (\result == true) <==> (obj instanceof MutableBoolean && ((MutableBoolean)obj).value == this.value);
     */
    @Test
    void testEquals_sameInstance() {
        MutableBoolean mb = createMutableBoolean(true);
        assertTrue(mb.equals(mb));
    }

    @Test
    void testEquals_equalValues_trueTrue() {
        MutableBoolean mb1 = createMutableBoolean(true);
        MutableBoolean mb2 = createMutableBoolean(true);
        assertTrue(mb1.equals(mb2));
    }

    @Test
    void testEquals_equalValues_falseFalse() {
        MutableBoolean mb1 = createMutableBoolean(false);
        MutableBoolean mb2 = createMutableBoolean(false);
        assertTrue(mb1.equals(mb2));
    }

    @Test
    void testEquals_differentValues_trueFalse() {
        MutableBoolean mb1 = createMutableBoolean(true);
        MutableBoolean mb2 = createMutableBoolean(false);
        assertFalse(mb1.equals(mb2));
    }

    @Test
    void testEquals_differentValues_falseTrue() {
        MutableBoolean mb1 = createMutableBoolean(false);
        MutableBoolean mb2 = createMutableBoolean(true);
        assertFalse(mb1.equals(mb2));
    }

    @Test
    void testEquals_nullObject() {
        MutableBoolean mb = createMutableBoolean(true);
        assertFalse(mb.equals(null));
    }

    @Test
    void testEquals_differentClass() {
        MutableBoolean mb = createMutableBoolean(true);
        assertFalse(mb.equals("some string"));
    }

    @Test
    void testEquals_differentClass_Boolean() {
        MutableBoolean mb = createMutableBoolean(true);
        assertFalse(mb.equals(Boolean.TRUE)); // Should be false as it's a different class
    }

    /*
     * Test for getValue()
     * public Boolean getValue();
     * @ensures \result != null;
     * @ensures \result.booleanValue() == this.value;
     */
    @Test
    void testGetValue_true() {
        MutableBoolean mb = createMutableBoolean(true);
        assertEquals(Boolean.TRUE, mb.getValue());
        assertTrue(mb.getValue().booleanValue());
    }

    @Test
    void testGetValue_false() {
        MutableBoolean mb = createMutableBoolean(false);
        assertEquals(Boolean.FALSE, mb.getValue());
        assertFalse(mb.getValue().booleanValue());
    }

    @Test
    void testGetValue_notNull() {
        MutableBoolean mb = createMutableBoolean(true);
        assertNotNull(mb.getValue());
    }

    /*
     * Test for hashCode()
     * public int hashCode();
     * @ensures \result == Boolean.valueOf(this.value).hashCode();
     */
    @Test
    void testHashCode_true() {
        MutableBoolean mb = createMutableBoolean(true);
        assertEquals(Boolean.TRUE.hashCode(), mb.hashCode());
    }

    @Test
    void testHashCode_false() {
        MutableBoolean mb = createMutableBoolean(false);
        assertEquals(Boolean.FALSE.hashCode(), mb.hashCode());
    }

    @Test
    void testHashCode_consistency() {
        MutableBoolean mb1 = createMutableBoolean(true);
        MutableBoolean mb2 = createMutableBoolean(true);
        assertEquals(mb1.hashCode(), mb2.hashCode());

        MutableBoolean mb3 = createMutableBoolean(false);
        MutableBoolean mb4 = createMutableBoolean(false);
        assertEquals(mb3.hashCode(), mb4.hashCode());

        assertNotEquals(mb1.hashCode(), mb3.hashCode());
    }

    /*
     * Test for isFalse()
     * public boolean isFalse();
     * @ensures \result == !this.value;
     */
    @Test
    void testIsFalse_whenTrue() {
        MutableBoolean mb = createMutableBoolean(true);
        assertFalse(mb.isFalse());
    }

    @Test
    void testIsFalse_whenFalse() {
        MutableBoolean mb = createMutableBoolean(false);
        assertTrue(mb.isFalse());
    }

    @Test
    void testIsFalse_afterSetTrue() {
        MutableBoolean mb = createMutableBoolean(false);
        mb.setTrue();
        assertFalse(mb.isFalse());
    }

    @Test
    void testIsFalse_afterSetFalse() {
        MutableBoolean mb = createMutableBoolean(true);
        mb.setFalse();
        assertTrue(mb.isFalse());
    }

    /*
     * Test for isTrue()
     * public boolean isTrue();
     * @ensures \result == this.value;
     */
    @Test
    void testIsTrue_whenTrue() {
        MutableBoolean mb = createMutableBoolean(true);
        assertTrue(mb.isTrue());
    }

    @Test
    void testIsTrue_whenFalse() {
        MutableBoolean mb = createMutableBoolean(false);
        assertFalse(mb.isTrue());
    }

    @Test
    void testIsTrue_afterSetTrue() {
        MutableBoolean mb = createMutableBoolean(false);
        mb.setTrue();
        assertTrue(mb.isTrue());
    }

    @Test
    void testIsTrue_afterSetFalse() {
        MutableBoolean mb = createMutableBoolean(true);
        mb.setFalse();
        assertFalse(mb.isTrue());
    }

    /*
     * Test for setFalse()
     * public void setFalse();
     * @ensures this.value == false;
     */
    @Test
    void testSetFalse_fromTrue() {
        MutableBoolean mb = createMutableBoolean(true);
        mb.setFalse();
        assertFalse(mb.booleanValue());
        assertTrue(mb.isFalse());
        assertFalse(mb.isTrue());
    }

    @Test
    void testSetFalse_fromFalse() {
        MutableBoolean mb = createMutableBoolean(false);
        mb.setFalse();
        assertFalse(mb.booleanValue());
        assertTrue(mb.isFalse());
        assertFalse(mb.isTrue());
    }

    /*
     * Test for setTrue()
     * public void setTrue();
     * @ensures this.value == true;
     */
    @Test
    void testSetTrue_fromFalse() {
        MutableBoolean mb = createMutableBoolean(false);
        mb.setTrue();
        assertTrue(mb.booleanValue());
        assertFalse(mb.isFalse());
        assertTrue(mb.isTrue());
    }

    @Test
    void testSetTrue_fromTrue() {
        MutableBoolean mb = createMutableBoolean(true);
        mb.setTrue();
        assertTrue(mb.booleanValue());
        assertFalse(mb.isFalse());
        assertTrue(mb.isTrue());
    }

    /*
     * Test for setValue(final boolean value)
     * public void setValue(final boolean value);
     * @ensures this.value == value;
     */
    @ParameterizedTest
    @ValueSource(booleans = {true, false})
    void testSetValue_boolean(boolean value) {
        MutableBoolean mb = createMutableBoolean(!value); // Initialize with opposite value
        mb.setValue(value);
        assertEquals(value, mb.booleanValue());
        assertEquals(value, mb.isTrue());
        assertEquals(!value, mb.isFalse());
    }

    /*
     * Test for setValue(final Boolean value)
     * public void setValue(final Boolean value);
     * @requires value != null;
     * @ensures this.value == value.booleanValue();
     */
    @ParameterizedTest
    @MethodSource("provideBooleanValues")
    void testSetValue_Boolean(Boolean value) {
        MutableBoolean mb = createMutableBoolean(!value); // Initialize with opposite value
        mb.setValue(value);
        assertEquals(value.booleanValue(), mb.booleanValue());
        assertEquals(value.booleanValue(), mb.isTrue());
        assertEquals(!value.booleanValue(), mb.isFalse());
    }

    @Test
    void testSetValue_Boolean_nullValue_throwsNullPointerException() {
        MutableBoolean mb = createMutableBoolean(true);
        assertThrows(NullPointerException.class, () -> mb.setValue((Boolean) null));
    }

    private static Stream<Arguments> provideBooleanValues() {
        return Stream.of(
                Arguments.of(Boolean.TRUE),
                Arguments.of(Boolean.FALSE)
        );
    }

    /*
     * Test for toBoolean()
     * public Boolean toBoolean();
     * @ensures \result != null;
     * @ensures \result.booleanValue() == this.value;
     */
    @Test
    void testToBoolean_true() {
        MutableBoolean mb = createMutableBoolean(true);
        assertEquals(Boolean.TRUE, mb.toBoolean());
        assertTrue(mb.toBoolean().booleanValue());
    }

    @Test
    void testToBoolean_false() {
        MutableBoolean mb = createMutableBoolean(false);
        assertEquals(Boolean.FALSE, mb.toBoolean());
        assertFalse(mb.toBoolean().booleanValue());
    }

    @Test
    void testToBoolean_notNull() {
        MutableBoolean mb = createMutableBoolean(true);
        assertNotNull(mb.toBoolean());
    }

    @Test
    void testToBoolean_identity() {
        MutableBoolean mb = createMutableBoolean(true);
        Boolean result1 = mb.toBoolean();
        Boolean result2 = mb.toBoolean();
        // Boolean.TRUE and Boolean.FALSE are singletons, so identity should hold
        assertSame(Boolean.TRUE, result1);
        assertSame(result1, result2);
    }

    /*
     * Test for toString()
     * public String toString();
     * @ensures \result.equals(String.valueOf(this.value));
     */
    @Test
    void testToString_true() {
        MutableBoolean mb = createMutableBoolean(true);
        assertEquals("true", mb.toString());
    }

    @Test
    void testToString_false() {
        MutableBoolean mb = createMutableBoolean(false);
        assertEquals("false", mb.toString());
    }

    @Test
    void testToString_afterChange() {
        MutableBoolean mb = createMutableBoolean(true);
        assertEquals("true", mb.toString());
        mb.setFalse();
        assertEquals("false", mb.toString());
    }

    // Constructor tests (not explicitly in the provided signatures, but good to cover)
    @Test
    void testConstructor_default() {
        MutableBoolean mb = new MutableBoolean();
        assertFalse(mb.booleanValue()); // Default constructor initializes to false
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
        assertThrows(NullPointerException.class, () -> new MutableBoolean((Boolean) null));
    }
}