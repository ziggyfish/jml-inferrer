package org.apache.commons.lang3.mutable.p3;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("MutableBoolean Unit Tests")
class MutableBooleanTestP3P3 {

    private MutableBoolean mutableBoolean;

    @BeforeEach
    void setUp() {
        mutableBoolean = new MutableBoolean();
    }

    @Nested
    @DisplayName("Constructor Tests")
    class ConstructorTests {

        @Test
        @DisplayName("Default constructor initializes to false")
        void testDefaultConstructor() {
            MutableBoolean mb = new MutableBoolean();
            assertFalse(mb.booleanValue(), "Default constructor should initialize to false");
        }

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("Constructor with boolean value")
        void testConstructorWithBoolean(boolean value) {
            MutableBoolean mb = new MutableBoolean(value);
            assertEquals(value, mb.booleanValue(), "Constructor with boolean should set the correct value");
        }

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("Constructor with Boolean object")
        void testConstructorWithBooleanObject(boolean value) {
            MutableBoolean mb = new MutableBoolean(Boolean.valueOf(value));
            assertEquals(value, mb.booleanValue(), "Constructor with Boolean object should set the correct value");
        }

        @Test
        @DisplayName("Constructor with null Boolean object should initialize to false")
        void testConstructorWithNullBooleanObject() {
            MutableBoolean mb = new MutableBoolean((Boolean) null);
            assertFalse(mb.booleanValue(), "Constructor with null Boolean should initialize to false");
        }
    }

    @Nested
    @DisplayName("booleanValue() Tests")
    class BooleanValueTests {

        @Test
        @DisplayName("booleanValue() returns true when value is true")
        void testBooleanValueWhenTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false when value is false")
        void testBooleanValueWhenFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("compareTo(MutableBoolean other) Tests")
    class CompareToTests {

        @Test
        @DisplayName("compareTo returns 0 when values are equal (true vs true)")
        void testCompareToEqualTrue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertEquals(0, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo returns 0 when values are equal (false vs false)")
        void testCompareToEqualFalse() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertEquals(0, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo returns positive when this is true and other is false")
        void testCompareToThisTrueOtherFalse() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertTrue(mutableBoolean.compareTo(other) > 0);
        }

        @Test
        @DisplayName("compareTo returns negative when this is false and other is true")
        void testCompareToThisFalseOtherTrue() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(true);
            assertTrue(mutableBoolean.compareTo(other) < 0);
        }

        @Test
        @DisplayName("compareTo throws NullPointerException for null argument")
        void testCompareToNull() {
            assertThrows(NullPointerException.class, () -> mutableBoolean.compareTo(null));
        }
    }

    @Nested
    @DisplayName("equals(Object obj) Tests")
    class EqualsTests {

        @Test
        @DisplayName("equals returns true for same object")
        void testEqualsSameObject() {
            assertTrue(mutableBoolean.equals(mutableBoolean));
        }

        @Test
        @DisplayName("equals returns true for equal MutableBoolean objects (true vs true)")
        void testEqualsMutableBooleanTrue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals returns true for equal MutableBoolean objects (false vs false)")
        void testEqualsMutableBooleanFalse() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals returns false for different MutableBoolean objects (true vs false)")
        void testEqualsMutableBooleanDifferentValues() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals returns false for different MutableBoolean objects (false vs true)")
        void testEqualsMutableBooleanDifferentValues2() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(true);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals returns false for null object")
        void testEqualsNull() {
            assertFalse(mutableBoolean.equals(null));
        }

        @Test
        @DisplayName("equals returns false for different class object")
        void testEqualsDifferentClass() {
            assertFalse(mutableBoolean.equals("a string"));
        }

        @Test
        @DisplayName("equals returns false for Boolean object with different value")
        void testEqualsBooleanObjectDifferentValue() {
            mutableBoolean.setValue(true);
            assertFalse(mutableBoolean.equals(Boolean.FALSE));
        }

        @Test
        @DisplayName("equals returns false for Boolean object with same value (not directly comparable)")
        void testEqualsBooleanObjectSameValue() {
            // JML spec doesn't explicitly state how it interacts with Boolean objects,
            // but typical equals implementations for custom types don't equate to wrapper types.
            // The current implementation of MutableBoolean.equals does not consider Boolean objects equal.
            mutableBoolean.setValue(true);
            assertFalse(mutableBoolean.equals(Boolean.TRUE));
        }
    }

    @Nested
    @DisplayName("getValue() Tests")
    class GetValueTests {

        @Test
        @DisplayName("getValue() returns Boolean.TRUE when value is true")
        void testGetValueWhenTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE when value is false")
        void testGetValueWhenFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {

        @Test
        @DisplayName("hashCode is consistent for true value")
        void testHashCodeTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE.hashCode(), mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode is consistent for false value")
        void testHashCodeFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE.hashCode(), mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode is equal for equal objects")
        void testHashCodeEqualsContract() {
            MutableBoolean mb1 = new MutableBoolean(true);
            MutableBoolean mb2 = new MutableBoolean(true);
            assertEquals(mb1.hashCode(), mb2.hashCode());

            MutableBoolean mb3 = new MutableBoolean(false);
            MutableBoolean mb4 = new MutableBoolean(false);
            assertEquals(mb3.hashCode(), mb4.hashCode());
        }

        @Test
        @DisplayName("hashCode is different for unequal objects (likely)")
        void testHashCodeDifferentObjects() {
            MutableBoolean mb1 = new MutableBoolean(true);
            MutableBoolean mb2 = new MutableBoolean(false);
            assertNotEquals(mb1.hashCode(), mb2.hashCode());
        }
    }

    @Nested
    @DisplayName("isFalse() Tests")
    class IsFalseTests {

        @Test
        @DisplayName("isFalse() returns true when value is false")
        void testIsFalseWhenFalse() {
            mutableBoolean.setValue(false);
            assertTrue(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns false when value is true")
        void testIsFalseWhenTrue() {
            mutableBoolean.setValue(true);
            assertFalse(mutableBoolean.isFalse());
        }
    }

    @Nested
    @DisplayName("isTrue() Tests")
    class IsTrueTests {

        @Test
        @DisplayName("isTrue() returns true when value is true")
        void testIsTrueWhenTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false when value is false")
        void testIsTrueWhenFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.isTrue());
        }
    }

    @Nested
    @DisplayName("setFalse() Tests")
    class SetFalseTests {

        @Test
        @DisplayName("setFalse() sets value to false when initially true")
        void testSetFalseFromTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setFalse() keeps value false when initially false")
        void testSetFalseFromFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setTrue() Tests")
    class SetTrueTests {

        @Test
        @DisplayName("setTrue() sets value to true when initially false")
        void testSetTrueFromFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setTrue() keeps value true when initially true")
        void testSetTrueFromTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(boolean value) Tests")
    class SetValueBooleanTests {

        @Test
        @DisplayName("setValue(true) sets value to true")
        void testSetValueToTrue() {
            mutableBoolean.setValue(false); // Ensure it's initially false
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(false) sets value to false")
        void testSetValueToFalse() {
            mutableBoolean.setValue(true); // Ensure it's initially true
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(Boolean value) Tests")
    class SetValueBooleanObjectTests {

        @Test
        @DisplayName("setValue(Boolean.TRUE) sets value to true")
        void testSetValueToBooleanTrue() {
            mutableBoolean.setValue(false); // Ensure it's initially false
            mutableBoolean.setValue(Boolean.TRUE);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean.FALSE) sets value to false")
        void testSetValueToBooleanFalse() {
            mutableBoolean.setValue(true); // Ensure it's initially true
            mutableBoolean.setValue(Boolean.FALSE);
            assertFalse(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(null) sets value to false")
        void testSetValueToNull() {
            mutableBoolean.setValue(true); // Ensure it's initially true
            mutableBoolean.setValue((Boolean) null);
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("toBoolean() Tests")
    class ToBooleanTests {

        @Test
        @DisplayName("toBoolean() returns Boolean.TRUE when value is true")
        void testToBooleanWhenTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE when value is false")
        void testToBooleanWhenFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.toBoolean());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {

        @Test
        @DisplayName("toString() returns 'true' when value is true")
        void testToStringWhenTrue() {
            mutableBoolean.setValue(true);
            assertEquals("true", mutableBoolean.toString());
        }

        @Test
        @DisplayName("toString() returns 'false' when value is false")
        void testToStringWhenFalse() {
            mutableBoolean.setValue(false);
            assertEquals("false", mutableBoolean.toString());
        }
    }

    @Nested
    @DisplayName("Combined Behavior Tests")
    class CombinedBehaviorTests {

        @ParameterizedTest
        @CsvSource({
                "true, true, true",
                "true, false, false",
                "false, true, true",
                "false, false, false"
        })
        @DisplayName("Chained operations and state changes")
        void testChainedOperations(boolean initialValue, boolean setValue, boolean expectedFinalValue) {
            mutableBoolean = new MutableBoolean(initialValue);
            assertEquals(initialValue, mutableBoolean.booleanValue(), "Initial value check failed");

            mutableBoolean.setValue(setValue);
            assertEquals(expectedFinalValue, mutableBoolean.booleanValue(), "setValue check failed");
            assertEquals(expectedFinalValue, mutableBoolean.getValue().booleanValue(), "getValue check failed");
            assertEquals(String.valueOf(expectedFinalValue), mutableBoolean.toString(), "toString check failed");
            assertEquals(expectedFinalValue, mutableBoolean.isTrue(), "isTrue check failed");
            assertEquals(!expectedFinalValue, mutableBoolean.isFalse(), "isFalse check failed");
        }

        @Test
        @DisplayName("Verify immutability of returned Boolean object from getValue/toBoolean")
        void testReturnedBooleanImmutability() {
            mutableBoolean.setValue(true);
            Boolean b1 = mutableBoolean.getValue();
            Boolean b2 = mutableBoolean.toBoolean();

            mutableBoolean.setValue(false); // Change the internal state

            // The returned Boolean objects should still reflect the value at the time of retrieval
            assertTrue(b1);
            assertTrue(b2);
            assertFalse(mutableBoolean.booleanValue()); // Internal state should be false
        }
    }
}