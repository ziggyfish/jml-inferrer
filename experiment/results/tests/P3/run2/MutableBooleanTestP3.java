package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class MutableBooleanTestP3P3 {

    private MutableBoolean mutableBoolean;

    @BeforeEach
    void setUp() {
        mutableBoolean = new MutableBoolean(); // Default constructor initializes to false
    }

    @Nested
    @DisplayName("booleanValue() Tests")
    class BooleanValueTests {

        // @ensures \result == this.value;
        @Test
        @DisplayName("booleanValue() returns true when internal value is true")
        void booleanValue_whenTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false when internal value is false")
        void booleanValue_whenFalse_returnsFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false after default construction")
        void booleanValue_afterDefaultConstruction_returnsFalse() {
            assertFalse(new MutableBoolean().booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns true after constructing with true")
        void booleanValue_afterConstructionWithTrue_returnsTrue() {
            assertTrue(new MutableBoolean(true).booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false after constructing with false")
        void booleanValue_afterConstructionWithFalse_returnsFalse() {
            assertFalse(new MutableBoolean(false).booleanValue());
        }
    }

    @Nested
    @DisplayName("compareTo(MutableBoolean other) Tests")
    class CompareToTests {

        // @requires other != null;
        // @ensures \result == (this.value == other.value ? 0 : (this.value ? 1 : -1));
        @Test
        @DisplayName("compareTo() returns 0 when both are true")
        void compareTo_bothTrue_returnsZero() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertEquals(0, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo() returns 0 when both are false")
        void compareTo_bothFalse_returnsZero() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertEquals(0, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo() returns 1 when this is true and other is false")
        void compareTo_thisTrueOtherFalse_returnsOne() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertEquals(1, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo() returns -1 when this is false and other is true")
        void compareTo_thisFalseOtherTrue_returnsMinusOne() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(true);
            assertEquals(-1, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo() throws NullPointerException when other is null")
        void compareTo_otherIsNull_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> mutableBoolean.compareTo(null));
        }
    }

    @Nested
    @DisplayName("equals(Object obj) Tests")
    class EqualsTests {

        // @ensures \result == (obj instanceof MutableBoolean && ((MutableBoolean)obj).value == this.value);
        @Test
        @DisplayName("equals() returns true for same object reference")
        void equals_sameObject_returnsTrue() {
            assertTrue(mutableBoolean.equals(mutableBoolean));
        }

        @Test
        @DisplayName("equals() returns true for two MutableBoolean objects with same true value")
        void equals_twoTrueMutableBooleans_returnsTrue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns true for two MutableBoolean objects with same false value")
        void equals_twoFalseMutableBooleans_returnsTrue() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for two MutableBoolean objects with different values (true vs false)")
        void equals_trueAndFalseMutableBooleans_returnsFalse() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for two MutableBoolean objects with different values (false vs true)")
        void equals_falseAndTrueMutableBooleans_returnsFalse() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(true);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false when obj is null")
        void equals_nullObject_returnsFalse() {
            assertFalse(mutableBoolean.equals(null));
        }

        @Test
        @DisplayName("equals() returns false when obj is of different type")
        void equals_differentTypeObject_returnsFalse() {
            assertFalse(mutableBoolean.equals("a string"));
            assertFalse(mutableBoolean.equals(Boolean.TRUE)); // Even Boolean is a different type
        }
    }

    @Nested
    @DisplayName("getValue() Tests")
    class GetValueTests {

        // @ensures \result != null;
        // @ensures \result.booleanValue() == this.value;
        @Test
        @DisplayName("getValue() returns Boolean.TRUE when internal value is true")
        void getValue_whenTrue_returnsBooleanTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE when internal value is false")
        void getValue_whenFalse_returnsBooleanFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns non-null value")
        void getValue_returnsNonNull() {
            assertNotNull(mutableBoolean.getValue());
            mutableBoolean.setValue(true);
            assertNotNull(mutableBoolean.getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {

        // @ensures \result == (this.value ? Boolean.TRUE.hashCode() : Boolean.FALSE.hashCode());
        @Test
        @DisplayName("hashCode() returns Boolean.TRUE's hash code when internal value is true")
        void hashCode_whenTrue_returnsTrueHashCode() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE.hashCode(), mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns Boolean.FALSE's hash code when internal value is false")
        void hashCode_whenFalse_returnsFalseHashCode() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE.hashCode(), mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode() is consistent with equals() for true values")
        void hashCode_consistentWithEquals_trueValues() {
            MutableBoolean mb1 = new MutableBoolean(true);
            MutableBoolean mb2 = new MutableBoolean(true);
            assertTrue(mb1.equals(mb2));
            assertEquals(mb1.hashCode(), mb2.hashCode());
        }

        @Test
        @DisplayName("hashCode() is consistent with equals() for false values")
        void hashCode_consistentWithEquals_falseValues() {
            MutableBoolean mb1 = new MutableBoolean(false);
            MutableBoolean mb2 = new MutableBoolean(false);
            assertTrue(mb1.equals(mb2));
            assertEquals(mb1.hashCode(), mb2.hashCode());
        }

        @Test
        @DisplayName("hashCode() is different for different values")
        void hashCode_differentForDifferentValues() {
            MutableBoolean mbTrue = new MutableBoolean(true);
            MutableBoolean mbFalse = new MutableBoolean(false);
            assertNotEquals(mbTrue.hashCode(), mbFalse.hashCode());
        }
    }

    @Nested
    @DisplayName("isFalse() Tests")
    class IsFalseTests {

        // @ensures \result == !this.value;
        @Test
        @DisplayName("isFalse() returns true when internal value is false")
        void isFalse_whenFalse_returnsTrue() {
            mutableBoolean.setValue(false);
            assertTrue(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns false when internal value is true")
        void isFalse_whenTrue_returnsFalse() {
            mutableBoolean.setValue(true);
            assertFalse(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns true after default construction")
        void isFalse_afterDefaultConstruction_returnsTrue() {
            assertTrue(new MutableBoolean().isFalse());
        }
    }

    @Nested
    @DisplayName("isTrue() Tests")
    class IsTrueTests {

        // @ensures \result == this.value;
        @Test
        @DisplayName("isTrue() returns true when internal value is true")
        void isTrue_whenTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false when internal value is false")
        void isTrue_whenFalse_returnsFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false after default construction")
        void isTrue_afterDefaultConstruction_returnsFalse() {
            assertFalse(new MutableBoolean().isTrue());
        }
    }

    @Nested
    @DisplayName("setFalse() Tests")
    class SetFalseTests {

        // @ensures this.value == false;
        @Test
        @DisplayName("setFalse() sets internal value to false when it was true")
        void setFalse_whenTrue_becomesFalse() {
            mutableBoolean.setValue(true);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            assertFalse(mutableBoolean.isTrue());
            assertTrue(mutableBoolean.isFalse());
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setFalse() keeps internal value false when it was already false")
        void setFalse_whenFalse_remainsFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            assertFalse(mutableBoolean.isTrue());
            assertTrue(mutableBoolean.isFalse());
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }
    }

    @Nested
    @DisplayName("setTrue() Tests")
    class SetTrueTests {

        // @ensures this.value == true;
        @Test
        @DisplayName("setTrue() sets internal value to true when it was false")
        void setTrue_whenFalse_becomesTrue() {
            mutableBoolean.setValue(false);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            assertTrue(mutableBoolean.isTrue());
            assertFalse(mutableBoolean.isFalse());
            assertEquals(Boolean.TRUE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setTrue() keeps internal value true when it was already true")
        void setTrue_whenTrue_remainsTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            assertTrue(mutableBoolean.isTrue());
            assertFalse(mutableBoolean.isFalse());
            assertEquals(Boolean.TRUE, mutableBoolean.getValue());
        }
    }

    @Nested
    @DisplayName("setValue(boolean value) Tests")
    class SetValueBooleanTests {

        // @ensures this.value == value;
        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("setValue(boolean) correctly sets the internal boolean value")
        void setValue_boolean_setsValueCorrectly(boolean value) {
            mutableBoolean.setValue(value);
            assertEquals(value, mutableBoolean.booleanValue());
            assertEquals(value, mutableBoolean.isTrue());
            assertEquals(!value, mutableBoolean.isFalse());
            assertEquals(Boolean.valueOf(value), mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue(true) changes false to true")
        void setValue_true_changesFalseToTrue() {
            mutableBoolean.setValue(false);
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(false) changes true to false")
        void setValue_false_changesTrueToFalse() {
            mutableBoolean.setValue(true);
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(Boolean value) Tests")
    class SetValueBooleanWrapperTests {

        // @requires value != null;
        // @ensures this.value == value.booleanValue();
        @ParameterizedTest
        @CsvSource({"TRUE, true", "FALSE, false"})
        @DisplayName("setValue(Boolean) correctly sets the internal boolean value")
        void setValue_Boolean_setsValueCorrectly(Boolean inputBoolean, boolean expectedBoolean) {
            mutableBoolean.setValue(inputBoolean);
            assertEquals(expectedBoolean, mutableBoolean.booleanValue());
            assertEquals(expectedBoolean, mutableBoolean.isTrue());
            assertEquals(!expectedBoolean, mutableBoolean.isFalse());
            assertEquals(inputBoolean, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("setValue(Boolean.TRUE) changes false to true")
        void setValue_BooleanTrue_changesFalseToTrue() {
            mutableBoolean.setValue(false);
            mutableBoolean.setValue(Boolean.TRUE);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean.FALSE) changes true to false")
        void setValue_BooleanFalse_changesTrueToFalse() {
            mutableBoolean.setValue(true);
            mutableBoolean.setValue(Boolean.FALSE);
            assertFalse(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(null) throws NullPointerException")
        void setValue_null_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> mutableBoolean.setValue(null));
        }
    }

    @Nested
    @DisplayName("toBoolean() Tests")
    class ToBooleanTests {

        // @ensures \result != null;
        // @ensures \result.booleanValue() == this.value;
        @Test
        @DisplayName("toBoolean() returns Boolean.TRUE when internal value is true")
        void toBoolean_whenTrue_returnsBooleanTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE when internal value is false")
        void toBoolean_whenFalse_returnsBooleanFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns non-null value")
        void toBoolean_returnsNonNull() {
            assertNotNull(mutableBoolean.toBoolean());
            mutableBoolean.setValue(true);
            assertNotNull(mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns same instance as Boolean.TRUE/FALSE")
        void toBoolean_returnsCachedInstance() {
            mutableBoolean.setValue(true);
            assertSame(Boolean.TRUE, mutableBoolean.toBoolean());
            mutableBoolean.setValue(false);
            assertSame(Boolean.FALSE, mutableBoolean.toBoolean());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {

        // @ensures \result != null;
        // @ensures \result.equals(String.valueOf(this.value));
        @Test
        @DisplayName("toString() returns 'true' when internal value is true")
        void toString_whenTrue_returnsTrueString() {
            mutableBoolean.setValue(true);
            assertEquals("true", mutableBoolean.toString());
        }

        @Test
        @DisplayName("toString() returns 'false' when internal value is false")
        void toString_whenFalse_returnsFalseString() {
            mutableBoolean.setValue(false);
            assertEquals("false", mutableBoolean.toString());
        }

        @Test
        @DisplayName("toString() returns non-null string")
        void toString_returnsNonNull() {
            assertNotNull(mutableBoolean.toString());
            mutableBoolean.setValue(true);
            assertNotNull(mutableBoolean.toString());
        }
    }

    @Nested
    @DisplayName("Constructor Tests")
    class ConstructorTests {
        @Test
        @DisplayName("Default constructor initializes to false")
        void defaultConstructor_initializesToFalse() {
            MutableBoolean mb = new MutableBoolean();
            assertFalse(mb.booleanValue());
            assertFalse(mb.isTrue());
            assertTrue(mb.isFalse());
        }

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("Constructor with boolean argument initializes correctly")
        void constructor_withBoolean_initializesCorrectly(boolean value) {
            MutableBoolean mb = new MutableBoolean(value);
            assertEquals(value, mb.booleanValue());
            assertEquals(value, mb.isTrue());
            assertEquals(!value, mb.isFalse());
        }

        @ParameterizedTest
        @CsvSource({"TRUE, true", "FALSE, false"})
        @DisplayName("Constructor with Boolean argument initializes correctly")
        void constructor_withBooleanWrapper_initializesCorrectly(Boolean value, boolean expected) {
            MutableBoolean mb = new MutableBoolean(value);
            assertEquals(expected, mb.booleanValue());
            assertEquals(expected, mb.isTrue());
            assertEquals(!expected, mb.isFalse());
        }

        @Test
        @DisplayName("Constructor with null Boolean argument throws NullPointerException")
        void constructor_withNullBooleanWrapper_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> new MutableBoolean(null));
        }
    }

    @Nested
    @DisplayName("General Behavior and Edge Cases")
    class GeneralBehaviorTests {

        @Test
        @DisplayName("Chained operations maintain correct state")
        void chainedOperations_maintainState() {
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
            mutableBoolean.setValue(Boolean.FALSE);
            assertFalse(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("Object identity for Boolean wrappers returned by getValue/toBoolean")
        void objectIdentity_forBooleanWrappers() {
            mutableBoolean.setValue(true);
            assertSame(Boolean.TRUE, mutableBoolean.getValue());
            assertSame(Boolean.TRUE, mutableBoolean.toBoolean());

            mutableBoolean.setValue(false);
            assertSame(Boolean.FALSE, mutableBoolean.getValue());
            assertSame(Boolean.FALSE, mutableBoolean.toBoolean());
        }
    }
}