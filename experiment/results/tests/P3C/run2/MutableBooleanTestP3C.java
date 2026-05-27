package org.apache.commons.lang3.mutable.p3c;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("MutableBoolean Test Suite")
class MutableBooleanTestP3CP3C {

    // Helper method to create MutableBoolean instances for tests
    private MutableBoolean createMutableBoolean(boolean value) {
        return new MutableBoolean(value);
    }

    @Nested
    @DisplayName("Constructor Tests")
    class ConstructorTests {
        @Test
        @DisplayName("Constructor with boolean true")
        void testConstructorBooleanTrue() {
            MutableBoolean mb = new MutableBoolean(true);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("Constructor with boolean false")
        void testConstructorBooleanFalse() {
            MutableBoolean mb = new MutableBoolean(false);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("Constructor with Boolean true")
        void testConstructorBooleanObjectTrue() {
            MutableBoolean mb = new MutableBoolean(Boolean.TRUE);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("Constructor with Boolean false")
        void testConstructorBooleanObjectFalse() {
            MutableBoolean mb = new MutableBoolean(Boolean.FALSE);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("Constructor with null Boolean")
        void testConstructorBooleanObjectNull() {
            // JML spec for constructor not provided, but common sense dictates
            // that null should result in false or throw an exception.
            // Commons Lang's MutableBoolean treats null as false.
            MutableBoolean mb = new MutableBoolean((Boolean) null);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("Default Constructor (initializes to false)")
        void testDefaultConstructor() {
            MutableBoolean mb = new MutableBoolean();
            assertFalse(mb.booleanValue());
        }
    }

    @Nested
    @DisplayName("booleanValue() Tests")
    class BooleanValueTests {
        // @ensures \result == this.value;

        @Test
        @DisplayName("booleanValue() returns true when value is true")
        void testBooleanValueTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false when value is false")
        void testBooleanValueFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() reflects changes after setValue(true)")
        void testBooleanValueAfterSetTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(true);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() reflects changes after setValue(false)")
        void testBooleanValueAfterSetFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertFalse(mb.booleanValue());
        }
    }

    @Nested
    @DisplayName("compareTo(MutableBoolean other) Tests")
    class CompareToTests {
        // @requires other != null;
        // @ensures \result == (this.booleanValue() == other.booleanValue() ? 0 : (this.booleanValue() ? 1 : -1));

        @Test
        @DisplayName("compareTo() returns 0 when both are true")
        void testCompareToTrueTrue() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertEquals(0, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() returns 0 when both are false")
        void testCompareToFalseFalse() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertEquals(0, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() returns 1 when this is true and other is false")
        void testCompareToTrueFalse() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertEquals(1, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() returns -1 when this is false and other is true")
        void testCompareToFalseTrue() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertEquals(-1, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() throws NullPointerException when other is null")
        void testCompareToNull() {
            MutableBoolean mb = createMutableBoolean(true);
            assertThrows(NullPointerException.class, () -> mb.compareTo(null));
        }

        @Test
        @DisplayName("compareTo() is consistent with equals for equal objects")
        void testCompareToConsistentWithEquals() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertEquals(0, mb1.compareTo(mb2));
            assertTrue(mb1.equals(mb2));

            MutableBoolean mb3 = createMutableBoolean(false);
            MutableBoolean mb4 = createMutableBoolean(false);
            assertEquals(0, mb3.compareTo(mb4));
            assertTrue(mb3.equals(mb4));
        }
    }

    @Nested
    @DisplayName("equals(Object obj) Tests")
    class EqualsTests {
        // @ensures \result == (obj instanceof MutableBoolean && ((MutableBoolean) obj).booleanValue() == this.booleanValue());

        @Test
        @DisplayName("equals() returns true for same object")
        void testEqualsSameObject() {
            MutableBoolean mb = createMutableBoolean(true);
            assertTrue(mb.equals(mb));
        }

        @Test
        @DisplayName("equals() returns true for two true MutableBooleans")
        void testEqualsTrueTrue() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertTrue(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns true for two false MutableBooleans")
        void testEqualsFalseFalse() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertTrue(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns false for true and false MutableBooleans")
        void testEqualsTrueFalse() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertFalse(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns false for false and true MutableBooleans")
        void testEqualsFalseTrue() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertFalse(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns false for null object")
        void testEqualsNull() {
            MutableBoolean mb = createMutableBoolean(true);
            assertFalse(mb.equals(null));
        }

        @Test
        @DisplayName("equals() returns false for different class object")
        void testEqualsDifferentClass() {
            MutableBoolean mb = createMutableBoolean(true);
            assertFalse(mb.equals("a string"));
            assertFalse(mb.equals(Boolean.TRUE)); // Boolean is not MutableBoolean
        }

        @Test
        @DisplayName("equals() is symmetric")
        void testEqualsSymmetric() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertTrue(mb1.equals(mb2));
            assertTrue(mb2.equals(mb1));

            MutableBoolean mb3 = createMutableBoolean(false);
            MutableBoolean mb4 = createMutableBoolean(false);
            assertTrue(mb3.equals(mb4));
            assertTrue(mb4.equals(mb3));

            MutableBoolean mb5 = createMutableBoolean(true);
            MutableBoolean mb6 = createMutableBoolean(false);
            assertFalse(mb5.equals(mb6));
            assertFalse(mb6.equals(mb5));
        }

        @Test
        @DisplayName("equals() is transitive")
        void testEqualsTransitive() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            MutableBoolean mb3 = createMutableBoolean(true);

            assertTrue(mb1.equals(mb2));
            assertTrue(mb2.equals(mb3));
            assertTrue(mb1.equals(mb3));
        }

        @Test
        @DisplayName("equals() is consistent")
        void testEqualsConsistent() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertTrue(mb1.equals(mb2));
            assertTrue(mb1.equals(mb2)); // Calling multiple times
        }
    }

    @Nested
    @DisplayName("getValue() Tests")
    class GetValueTests {
        // @ensures \result == Boolean.valueOf(this.booleanValue());

        @Test
        @DisplayName("getValue() returns Boolean.TRUE when value is true")
        void testGetValueTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE, mb.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE when value is false")
        void testGetValueFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals(Boolean.FALSE, mb.getValue());
        }

        @Test
        @DisplayName("getValue() reflects changes after setValue(true)")
        void testGetValueAfterSetTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(true);
            assertEquals(Boolean.TRUE, mb.getValue());
        }

        @Test
        @DisplayName("getValue() reflects changes after setValue(false)")
        void testGetValueAfterSetFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertEquals(Boolean.FALSE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {
        // @ensures \result == (this.booleanValue() ? Boolean.TRUE.hashCode() : Boolean.FALSE.hashCode());

        @Test
        @DisplayName("hashCode() returns Boolean.TRUE.hashCode() when value is true")
        void testHashCodeTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE.hashCode(), mb.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns Boolean.FALSE.hashCode() when value is false")
        void testHashCodeFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals(Boolean.FALSE.hashCode(), mb.hashCode());
        }

        @Test
        @DisplayName("hashCode() is consistent with equals for true values")
        void testHashCodeConsistentWithEqualsTrue() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertTrue(mb1.equals(mb2));
            assertEquals(mb1.hashCode(), mb2.hashCode());
        }

        @Test
        @DisplayName("hashCode() is consistent with equals for false values")
        void testHashCodeConsistentWithEqualsFalse() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertTrue(mb1.equals(mb2));
            assertEquals(mb1.hashCode(), mb2.hashCode());
        }

        @Test
        @DisplayName("hashCode() changes after value changes")
        void testHashCodeChangesAfterSet() {
            MutableBoolean mb = createMutableBoolean(true);
            int initialHashCode = mb.hashCode();
            mb.setValue(false);
            assertNotEquals(initialHashCode, mb.hashCode());
            assertEquals(Boolean.FALSE.hashCode(), mb.hashCode());
        }
    }

    @Nested
    @DisplayName("isFalse() Tests")
    class IsFalseTests {
        // @ensures \result == !this.booleanValue();

        @Test
        @DisplayName("isFalse() returns true when value is false")
        void testIsFalseWhenFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertTrue(mb.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns false when value is true")
        void testIsFalseWhenTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertFalse(mb.isFalse());
        }

        @Test
        @DisplayName("isFalse() reflects changes after setTrue()")
        void testIsFalseAfterSetTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setTrue();
            assertFalse(mb.isFalse());
        }

        @Test
        @DisplayName("isFalse() reflects changes after setFalse()")
        void testIsFalseAfterSetFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setFalse();
            assertTrue(mb.isFalse());
        }
    }

    @Nested
    @DisplayName("isTrue() Tests")
    class IsTrueTests {
        // @ensures \result == this.booleanValue();

        @Test
        @DisplayName("isTrue() returns true when value is true")
        void testIsTrueWhenTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertTrue(mb.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false when value is false")
        void testIsTrueWhenFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertFalse(mb.isTrue());
        }

        @Test
        @DisplayName("isTrue() reflects changes after setTrue()")
        void testIsTrueAfterSetTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setTrue();
            assertTrue(mb.isTrue());
        }

        @Test
        @DisplayName("isTrue() reflects changes after setFalse()")
        void testIsTrueAfterSetFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setFalse();
            assertFalse(mb.isTrue());
        }
    }

    @Nested
    @DisplayName("setFalse() Tests")
    class SetFalseTests {
        // @ensures this.booleanValue() == false;

        @Test
        @DisplayName("setFalse() sets value to false when initially true")
        void testSetFalseFromTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setFalse();
            assertFalse(mb.booleanValue());
            assertTrue(mb.isFalse());
            assertFalse(mb.isTrue());
        }

        @Test
        @DisplayName("setFalse() keeps value false when initially false")
        void testSetFalseFromFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setFalse();
            assertFalse(mb.booleanValue());
            assertTrue(mb.isFalse());
            assertFalse(mb.isTrue());
        }

        @Test
        @DisplayName("setFalse() affects getValue()")
        void testSetFalseAffectsGetValue() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setFalse();
            assertEquals(Boolean.FALSE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("setTrue() Tests")
    class SetTrueTests {
        // @ensures this.booleanValue() == true;

        @Test
        @DisplayName("setTrue() sets value to true when initially false")
        void testSetTrueFromFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setTrue();
            assertTrue(mb.booleanValue());
            assertFalse(mb.isFalse());
            assertTrue(mb.isTrue());
        }

        @Test
        @DisplayName("setTrue() keeps value true when initially true")
        void testSetTrueFromTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setTrue();
            assertTrue(mb.booleanValue());
            assertFalse(mb.isFalse());
            assertTrue(mb.isTrue());
        }

        @Test
        @DisplayName("setTrue() affects getValue()")
        void testSetTrueAffectsGetValue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setTrue();
            assertEquals(Boolean.TRUE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("setValue(boolean value) Tests")
    class SetValueBooleanTests {
        // @ensures this.booleanValue() == value;

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("setValue(boolean) sets the value correctly")
        void testSetValueBoolean(boolean value) {
            MutableBoolean mb = createMutableBoolean(!value); // Initialize to opposite
            mb.setValue(value);
            assertEquals(value, mb.booleanValue());
            assertEquals(Boolean.valueOf(value), mb.getValue());
        }

        @Test
        @DisplayName("setValue(true) on false MutableBoolean")
        void testSetValueTrueOnFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(true);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("setValue(false) on true MutableBoolean")
        void testSetValueFalseOnTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertFalse(mb.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(Boolean value) Tests")
    class SetValueBooleanObjectTests {
        // @ensures this.booleanValue() == (value == null ? false : value.booleanValue());

        @ParameterizedTest
        @CsvSource({"true, true", "false, false"})
        @DisplayName("setValue(Boolean) sets the value correctly for non-null Boolean")
        void testSetValueBooleanObjectNonNull(boolean initialValue, boolean newValue) {
            MutableBoolean mb = createMutableBoolean(initialValue);
            mb.setValue(Boolean.valueOf(newValue));
            assertEquals(newValue, mb.booleanValue());
            assertEquals(Boolean.valueOf(newValue), mb.getValue());
        }

        @Test
        @DisplayName("setValue(null) sets value to false")
        void testSetValueBooleanObjectNull() {
            MutableBoolean mb = createMutableBoolean(true); // Start with true
            mb.setValue((Boolean) null);
            assertFalse(mb.booleanValue());
            assertEquals(Boolean.FALSE, mb.getValue());
        }

        @Test
        @DisplayName("setValue(null) on already false MutableBoolean")
        void testSetValueBooleanObjectNullOnFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue((Boolean) null);
            assertFalse(mb.booleanValue());
            assertEquals(Boolean.FALSE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("toBoolean() Tests")
    class ToBooleanTests {
        // @ensures \result == Boolean.valueOf(this.booleanValue());

        @Test
        @DisplayName("toBoolean() returns Boolean.TRUE when value is true")
        void testToBooleanTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE, mb.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE when value is false")
        void testToBooleanFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals(Boolean.FALSE, mb.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() reflects changes after setValue(true)")
        void testToBooleanAfterSetTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(true);
            assertEquals(Boolean.TRUE, mb.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() reflects changes after setValue(false)")
        void testToBooleanAfterSetFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertEquals(Boolean.FALSE, mb.toBoolean());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {
        // @ensures \result == String.valueOf(this.booleanValue());

        @Test
        @DisplayName("toString() returns 'true' when value is true")
        void testToStringTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals("true", mb.toString());
        }

        @Test
        @DisplayName("toString() returns 'false' when value is false")
        void testToStringFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals("false", mb.toString());
        }

        @Test
        @DisplayName("toString() reflects changes after setValue(true)")
        void testToStringAfterSetTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(true);
            assertEquals("true", mb.toString());
        }

        @Test
        @DisplayName("toString() reflects changes after setValue(false)")
        void testToStringAfterSetFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertEquals("false", mb.toString());
        }
    }
}