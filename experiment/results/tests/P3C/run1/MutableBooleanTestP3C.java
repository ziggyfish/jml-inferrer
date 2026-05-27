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

    // Helper method to create MutableBoolean instances
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
        @DisplayName("Constructor with null Boolean should default to false")
        void testConstructorBooleanObjectNull() {
            MutableBoolean mb = new MutableBoolean((Boolean) null);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("Default constructor should initialize to false")
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
        @DisplayName("booleanValue() returns true when internal value is true")
        void testBooleanValueTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false when internal value is false")
        void testBooleanValueFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() reflects changes after setValue(boolean)")
        void testBooleanValueAfterSetValueBoolean() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertFalse(mb.booleanValue());
            mb.setValue(true);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() reflects changes after setValue(Boolean)")
        void testBooleanValueAfterSetValueBooleanObject() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(Boolean.FALSE);
            assertFalse(mb.booleanValue());
            mb.setValue(Boolean.TRUE);
            assertTrue(mb.booleanValue());
        }
    }

    @Nested
    @DisplayName("compareTo(MutableBoolean other) Tests")
    class CompareToTests {
        // @requires other != null;
        // @ensures \result == (this.value == other.value ? 0 : (this.value ? 1 : -1));

        @Test
        @DisplayName("compareTo() returns 0 when both are true")
        void testCompareToBothTrue() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertEquals(0, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() returns 0 when both are false")
        void testCompareToBothFalse() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertEquals(0, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() returns 1 when this is true and other is false")
        void testCompareToThisTrueOtherFalse() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertEquals(1, mb1.compareTo(mb2));
        }

        @Test
        @DisplayName("compareTo() returns -1 when this is false and other is true")
        void testCompareToThisFalseOtherTrue() {
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
            MutableBoolean mb3 = createMutableBoolean(false);

            assertTrue(mb1.equals(mb2));
            assertEquals(0, mb1.compareTo(mb2));

            assertFalse(mb1.equals(mb3));
            assertNotEquals(0, mb1.compareTo(mb3));
        }
    }

    @Nested
    @DisplayName("equals(Object obj) Tests")
    class EqualsTests {
        // @ensures \result == (obj instanceof MutableBoolean && ((MutableBoolean)obj).value == this.value);

        @Test
        @DisplayName("equals() returns true for same object")
        void testEqualsSameObject() {
            MutableBoolean mb = createMutableBoolean(true);
            assertTrue(mb.equals(mb));
        }

        @Test
        @DisplayName("equals() returns true for two true MutableBoolean objects")
        void testEqualsTrueTrue() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            assertTrue(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns true for two false MutableBoolean objects")
        void testEqualsFalseFalse() {
            MutableBoolean mb1 = createMutableBoolean(false);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertTrue(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns false for true and false MutableBoolean objects")
        void testEqualsTrueFalse() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(false);
            assertFalse(mb1.equals(mb2));
        }

        @Test
        @DisplayName("equals() returns false for false and true MutableBoolean objects")
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
        @DisplayName("equals() returns false for object of different type")
        void testEqualsDifferentType() {
            MutableBoolean mb = createMutableBoolean(true);
            assertFalse(mb.equals("a string"));
            assertFalse(mb.equals(Boolean.TRUE)); // Boolean is not MutableBoolean
        }

        @Test
        @DisplayName("equals() is symmetric")
        void testEqualsSymmetric() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            MutableBoolean mb3 = createMutableBoolean(false);

            assertTrue(mb1.equals(mb2) && mb2.equals(mb1));
            assertFalse(mb1.equals(mb3) || mb3.equals(mb1));
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
            assertTrue(mb1.equals(mb2)); // Calling multiple times should yield same result
        }
    }

    @Nested
    @DisplayName("getValue() Tests")
    class GetValueTests {
        // @ensures \result == Boolean.valueOf(this.value);
        @Test
        @DisplayName("getValue() returns Boolean.TRUE when internal value is true")
        void testGetValueTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE, mb.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE when internal value is false")
        void testGetValueFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals(Boolean.FALSE, mb.getValue());
        }

        @Test
        @DisplayName("getValue() reflects changes after setValue(boolean)")
        void testGetValueAfterSetValueBoolean() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertEquals(Boolean.FALSE, mb.getValue());
            mb.setValue(true);
            assertEquals(Boolean.TRUE, mb.getValue());
        }

        @Test
        @DisplayName("getValue() reflects changes after setValue(Boolean)")
        void testGetValueAfterSetValueBooleanObject() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(Boolean.FALSE);
            assertEquals(Boolean.FALSE, mb.getValue());
            mb.setValue(Boolean.TRUE);
            assertEquals(Boolean.TRUE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {
        // @ensures \result == (this.value ? Boolean.TRUE.hashCode() : Boolean.FALSE.hashCode());

        @Test
        @DisplayName("hashCode() returns Boolean.TRUE.hashCode() when internal value is true")
        void testHashCodeTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE.hashCode(), mb.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns Boolean.FALSE.hashCode() when internal value is false")
        void testHashCodeFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals(Boolean.FALSE.hashCode(), mb.hashCode());
        }

        @Test
        @DisplayName("hashCode() is consistent with equals for equal objects")
        void testHashCodeConsistentWithEquals() {
            MutableBoolean mb1 = createMutableBoolean(true);
            MutableBoolean mb2 = createMutableBoolean(true);
            MutableBoolean mb3 = createMutableBoolean(false);

            assertTrue(mb1.equals(mb2));
            assertEquals(mb1.hashCode(), mb2.hashCode());

            assertFalse(mb1.equals(mb3));
            // Hash codes are not required to be different for unequal objects,
            // but for Boolean, they are.
            assertNotEquals(mb1.hashCode(), mb3.hashCode());
        }

        @Test
        @DisplayName("hashCode() remains consistent after value change")
        void testHashCodeAfterValueChange() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE.hashCode(), mb.hashCode());
            mb.setValue(false);
            assertEquals(Boolean.FALSE.hashCode(), mb.hashCode());
        }
    }

    @Nested
    @DisplayName("isFalse() Tests")
    class IsFalseTests {
        // @ensures \result == !this.value;
        @Test
        @DisplayName("isFalse() returns true when internal value is false")
        void testIsFalseWhenFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertTrue(mb.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns false when internal value is true")
        void testIsFalseWhenTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertFalse(mb.isFalse());
        }

        @Test
        @DisplayName("isFalse() reflects changes after setValue")
        void testIsFalseAfterSetValue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertFalse(mb.isFalse());
            mb.setValue(false);
            assertTrue(mb.isFalse());
        }
    }

    @Nested
    @DisplayName("isTrue() Tests")
    class IsTrueTests {
        // @ensures \result == this.value;
        @Test
        @DisplayName("isTrue() returns true when internal value is true")
        void testIsTrueWhenTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertTrue(mb.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false when internal value is false")
        void testIsTrueWhenFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertFalse(mb.isTrue());
        }

        @Test
        @DisplayName("isTrue() reflects changes after setValue")
        void testIsTrueAfterSetValue() {
            MutableBoolean mb = createMutableBoolean(false);
            assertFalse(mb.isTrue());
            mb.setValue(true);
            assertTrue(mb.isTrue());
        }
    }

    @Nested
    @DisplayName("setFalse() Tests")
    class SetFalseTests {
        // @ensures this.value == false;
        @Test
        @DisplayName("setFalse() sets value to false when it was true")
        void testSetFalseFromTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setFalse();
            assertFalse(mb.booleanValue());
            assertFalse(mb.isTrue());
            assertTrue(mb.isFalse());
            assertEquals(Boolean.FALSE, mb.getValue());
        }

        @Test
        @DisplayName("setFalse() keeps value false when it was already false")
        void testSetFalseFromFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setFalse();
            assertFalse(mb.booleanValue());
            assertFalse(mb.isTrue());
            assertTrue(mb.isFalse());
            assertEquals(Boolean.FALSE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("setTrue() Tests")
    class SetTrueTests {
        // @ensures this.value == true;
        @Test
        @DisplayName("setTrue() sets value to true when it was false")
        void testSetTrueFromFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setTrue();
            assertTrue(mb.booleanValue());
            assertTrue(mb.isTrue());
            assertFalse(mb.isFalse());
            assertEquals(Boolean.TRUE, mb.getValue());
        }

        @Test
        @DisplayName("setTrue() keeps value true when it was already true")
        void testSetTrueFromTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setTrue();
            assertTrue(mb.booleanValue());
            assertTrue(mb.isTrue());
            assertFalse(mb.isFalse());
            assertEquals(Boolean.TRUE, mb.getValue());
        }
    }

    @Nested
    @DisplayName("setValue(boolean value) Tests")
    class SetValueBooleanTests {
        // @ensures this.value == value;
        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("setValue(boolean) correctly sets the value")
        void testSetValueBoolean(boolean value) {
            MutableBoolean mb = createMutableBoolean(!value); // Initialize to opposite
            mb.setValue(value);
            assertEquals(value, mb.booleanValue());
            assertEquals(Boolean.valueOf(value), mb.getValue());
        }

        @Test
        @DisplayName("setValue(boolean) from true to false")
        void testSetValueBooleanTrueToFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(false);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("setValue(boolean) from false to true")
        void testSetValueBooleanFalseToTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(true);
            assertTrue(mb.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(Boolean value) Tests")
    class SetValueBooleanObjectTests {
        // @ensures this.value == (value != null ? value.booleanValue() : false);

        @Test
        @DisplayName("setValue(Boolean) with Boolean.TRUE")
        void testSetValueBooleanObjectTrue() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(Boolean.TRUE);
            assertTrue(mb.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean) with Boolean.FALSE")
        void testSetValueBooleanObjectFalse() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(Boolean.FALSE);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean) with null should set to false")
        void testSetValueBooleanObjectNull() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(null);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean) from true to null")
        void testSetValueBooleanObjectTrueToNull() {
            MutableBoolean mb = createMutableBoolean(true);
            mb.setValue(null);
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean) from false to null")
        void testSetValueBooleanObjectFalseToNull() {
            MutableBoolean mb = createMutableBoolean(false);
            mb.setValue(null);
            assertFalse(mb.booleanValue());
        }
    }

    @Nested
    @DisplayName("toBoolean() Tests")
    class ToBooleanTests {
        // @ensures \result == Boolean.valueOf(this.value);
        @Test
        @DisplayName("toBoolean() returns Boolean.TRUE when internal value is true")
        void testToBooleanTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE, mb.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE when internal value is false")
        void testToBooleanFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals(Boolean.FALSE, mb.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() reflects changes after setValue")
        void testToBooleanAfterSetValue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals(Boolean.TRUE, mb.toBoolean());
            mb.setValue(false);
            assertEquals(Boolean.FALSE, mb.toBoolean());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {
        // @ensures \result == String.valueOf(this.value);
        @Test
        @DisplayName("toString() returns 'true' when internal value is true")
        void testToStringTrue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals("true", mb.toString());
        }

        @Test
        @DisplayName("toString() returns 'false' when internal value is false")
        void testToStringFalse() {
            MutableBoolean mb = createMutableBoolean(false);
            assertEquals("false", mb.toString());
        }

        @Test
        @DisplayName("toString() reflects changes after setValue")
        void testToStringAfterSetValue() {
            MutableBoolean mb = createMutableBoolean(true);
            assertEquals("true", mb.toString());
            mb.setValue(false);
            assertEquals("false", mb.toString());
        }
    }

    @Nested
    @DisplayName("Combined Operations Tests")
    class CombinedOperationsTests {

        @ParameterizedTest
        @CsvSource({
                "true, true, 0",
                "true, false, 1",
                "false, true, -1",
                "false, false, 0"
        })
        @DisplayName("Comprehensive compareTo and equals scenarios")
        void testCompareToAndEquals(boolean value1, boolean value2, int expectedCompareResult) {
            MutableBoolean mb1 = createMutableBoolean(value1);
            MutableBoolean mb2 = createMutableBoolean(value2);

            assertEquals(expectedCompareResult, mb1.compareTo(mb2));
            assertEquals(value1 == value2, mb1.equals(mb2));
            assertEquals(value1 == value2, mb1.hashCode() == mb2.hashCode());
        }

        @Test
        @DisplayName("Chaining setTrue and setFalse")
        void testChainingSetMethods() {
            MutableBoolean mb = new MutableBoolean(); // false
            assertFalse(mb.booleanValue());

            mb.setTrue();
            assertTrue(mb.booleanValue());

            mb.setFalse();
            assertFalse(mb.booleanValue());

            mb.setTrue();
            mb.setTrue(); // Redundant set
            assertTrue(mb.booleanValue());

            mb.setFalse();
            mb.setFalse(); // Redundant set
            assertFalse(mb.booleanValue());
        }

        @Test
        @DisplayName("Interaction between setValue and booleanValue/getValue")
        void testSetValueInteraction() {
            MutableBoolean mb = new MutableBoolean(true);
            assertTrue(mb.booleanValue());
            assertEquals(Boolean.TRUE, mb.getValue());
            assertTrue(mb.isTrue());
            assertFalse(mb.isFalse());
            assertEquals("true", mb.toString());
            assertEquals(Boolean.TRUE, mb.toBoolean());

            mb.setValue(false);
            assertFalse(mb.booleanValue());
            assertEquals(Boolean.FALSE, mb.getValue());
            assertFalse(mb.isTrue());
            assertTrue(mb.isFalse());
            assertEquals("false", mb.toString());
            assertEquals(Boolean.FALSE, mb.toBoolean());

            mb.setValue(Boolean.TRUE);
            assertTrue(mb.booleanValue());
            assertEquals(Boolean.TRUE, mb.getValue());

            mb.setValue((Boolean) null);
            assertFalse(mb.booleanValue());
            assertEquals(Boolean.FALSE, mb.getValue());
        }
    }
}