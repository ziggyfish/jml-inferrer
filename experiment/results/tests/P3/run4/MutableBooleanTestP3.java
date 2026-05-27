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
        mutableBoolean = new MutableBoolean();
    }

    @Nested
    @DisplayName("booleanValue() Tests")
    class BooleanValueTests {

        @Test
        @DisplayName("booleanValue() returns true when value is true")
        void booleanValue_whenTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false when value is false")
        void booleanValue_whenFalse_returnsFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns false by default constructor")
        void booleanValue_defaultConstructor_returnsFalse() {
            assertFalse(new MutableBoolean().booleanValue());
        }

        @Test
        @DisplayName("booleanValue() returns initial value from constructor")
        void booleanValue_constructorWithValue_returnsCorrectValue() {
            assertTrue(new MutableBoolean(true).booleanValue());
            assertFalse(new MutableBoolean(false).booleanValue());
        }
    }

    @Nested
    @DisplayName("compareTo(MutableBoolean other) Tests")
    class CompareToTests {

        @Test
        @DisplayName("compareTo() returns 0 when values are equal (true vs true)")
        void compareTo_trueVsTrue_returnsZero() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertEquals(0, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo() returns 0 when values are equal (false vs false)")
        void compareTo_falseVsFalse_returnsZero() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertEquals(0, mutableBoolean.compareTo(other));
        }

        @Test
        @DisplayName("compareTo() returns positive when this is true and other is false")
        void compareTo_trueVsFalse_returnsPositive() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertTrue(mutableBoolean.compareTo(other) > 0);
        }

        @Test
        @DisplayName("compareTo() returns negative when this is false and other is true")
        void compareTo_falseVsTrue_returnsNegative() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(true);
            assertTrue(mutableBoolean.compareTo(other) < 0);
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

        @Test
        @DisplayName("equals() returns true for same object")
        void equals_sameObject_returnsTrue() {
            assertTrue(mutableBoolean.equals(mutableBoolean));
        }

        @Test
        @DisplayName("equals() returns true for equal MutableBoolean objects (true vs true)")
        void equals_equalMutableBoolean_trueVsTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns true for equal MutableBoolean objects (false vs false)")
        void equals_equalMutableBoolean_falseVsFalse_returnsTrue() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for different MutableBoolean values (true vs false)")
        void equals_differentMutableBoolean_trueVsFalse_returnsFalse() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for different MutableBoolean values (false vs true)")
        void equals_differentMutableBoolean_falseVsTrue_returnsFalse() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(true);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for null object")
        void equals_nullObject_returnsFalse() {
            assertFalse(mutableBoolean.equals(null));
        }

        @Test
        @DisplayName("equals() returns false for different class type")
        void equals_differentClass_returnsFalse() {
            assertFalse(mutableBoolean.equals("a string"));
            assertFalse(mutableBoolean.equals(Boolean.TRUE)); // Even though it's a Boolean
        }

        @Test
        @DisplayName("equals() symmetry property")
        void equals_symmetry() {
            MutableBoolean mb1 = new MutableBoolean(true);
            MutableBoolean mb2 = new MutableBoolean(true);
            assertTrue(mb1.equals(mb2) && mb2.equals(mb1));

            MutableBoolean mb3 = new MutableBoolean(false);
            MutableBoolean mb4 = new MutableBoolean(false);
            assertTrue(mb3.equals(mb4) && mb4.equals(mb3));

            MutableBoolean mb5 = new MutableBoolean(true);
            MutableBoolean mb6 = new MutableBoolean(false);
            assertFalse(mb5.equals(mb6));
            assertFalse(mb6.equals(mb5));
        }

        @Test
        @DisplayName("equals() transitivity property")
        void equals_transitivity() {
            MutableBoolean mb1 = new MutableBoolean(true);
            MutableBoolean mb2 = new MutableBoolean(true);
            MutableBoolean mb3 = new MutableBoolean(true);
            assertTrue(mb1.equals(mb2));
            assertTrue(mb2.equals(mb3));
            assertTrue(mb1.equals(mb3));
        }
    }

    @Nested
    @DisplayName("getValue() Tests")
    class GetValueTests {

        @Test
        @DisplayName("getValue() returns Boolean.TRUE when value is true")
        void getValue_whenTrue_returnsBooleanTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE when value is false")
        void getValue_whenFalse_returnsBooleanFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE by default constructor")
        void getValue_defaultConstructor_returnsBooleanFalse() {
            assertEquals(Boolean.FALSE, new MutableBoolean().getValue());
        }

        @Test
        @DisplayName("getValue() returns initial Boolean value from constructor")
        void getValue_constructorWithValue_returnsCorrectBooleanValue() {
            assertEquals(Boolean.TRUE, new MutableBoolean(true).getValue());
            assertEquals(Boolean.FALSE, new MutableBoolean(false).getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {

        @Test
        @DisplayName("hashCode() returns same value for equal objects (true)")
        void hashCode_equalObjects_true_returnsSameHashCode() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertEquals(mutableBoolean.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns same value for equal objects (false)")
        void hashCode_equalObjects_false_returnsSameHashCode() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertEquals(mutableBoolean.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns different values for different objects (true vs false)")
        void hashCode_differentObjects_returnsDifferentHashCode() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertNotEquals(mutableBoolean.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("hashCode() consistency after value change")
        void hashCode_consistencyAfterChange() {
            int initialHashCode = mutableBoolean.hashCode();
            mutableBoolean.setValue(true);
            assertNotEquals(initialHashCode, mutableBoolean.hashCode());
            mutableBoolean.setValue(false);
            assertEquals(initialHashCode, mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode() matches Boolean.hashCode() for true")
        void hashCode_matchesBooleanHashCode_true() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE.hashCode(), mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode() matches Boolean.hashCode() for false")
        void hashCode_matchesBooleanHashCode_false() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE.hashCode(), mutableBoolean.hashCode());
        }
    }

    @Nested
    @DisplayName("isFalse() Tests")
    class IsFalseTests {

        @Test
        @DisplayName("isFalse() returns true when value is false")
        void isFalse_whenFalse_returnsTrue() {
            mutableBoolean.setValue(false);
            assertTrue(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns false when value is true")
        void isFalse_whenTrue_returnsFalse() {
            mutableBoolean.setValue(true);
            assertFalse(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("isFalse() returns true by default constructor")
        void isFalse_defaultConstructor_returnsTrue() {
            assertTrue(new MutableBoolean().isFalse());
        }
    }

    @Nested
    @DisplayName("isTrue() Tests")
    class IsTrueTests {

        @Test
        @DisplayName("isTrue() returns true when value is true")
        void isTrue_whenTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false when value is false")
        void isTrue_whenFalse_returnsFalse() {
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("isTrue() returns false by default constructor")
        void isTrue_defaultConstructor_returnsFalse() {
            assertFalse(new MutableBoolean().isTrue());
        }
    }

    @Nested
    @DisplayName("setFalse() Tests")
    class SetFalseTests {

        @Test
        @DisplayName("setFalse() sets value to false from true")
        void setFalse_fromTrue_setsToFalse() {
            mutableBoolean.setValue(true);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            assertFalse(mutableBoolean.isTrue());
            assertTrue(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("setFalse() keeps value false from false")
        void setFalse_fromFalse_staysFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            assertFalse(mutableBoolean.isTrue());
            assertTrue(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("setFalse() sets default constructed object to false")
        void setFalse_defaultObject_setsToFalse() {
            mutableBoolean.setFalse(); // Already false, but ensures postcondition
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setTrue() Tests")
    class SetTrueTests {

        @Test
        @DisplayName("setTrue() sets value to true from false")
        void setTrue_fromFalse_setsToTrue() {
            mutableBoolean.setValue(false);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            assertTrue(mutableBoolean.isTrue());
            assertFalse(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("setTrue() keeps value true from true")
        void setTrue_fromTrue_staysTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            assertTrue(mutableBoolean.isTrue());
            assertFalse(mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("setTrue() sets default constructed object to true")
        void setTrue_defaultObject_setsToTrue() {
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(boolean value) Tests")
    class SetValueBooleanTests {

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("setValue(boolean) correctly sets the boolean value")
        void setValueBoolean_setsCorrectValue(boolean value) {
            mutableBoolean.setValue(value);
            assertEquals(value, mutableBoolean.booleanValue());
            assertEquals(value, mutableBoolean.isTrue());
            assertEquals(!value, mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("setValue(true) changes value from false to true")
        void setValueBoolean_true_changesFromFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(false) changes value from true to false")
        void setValueBoolean_false_changesFromTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setValue(false);
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(Boolean value) Tests")
    class SetValueBooleanObjectTests {

        @ParameterizedTest
        @CsvSource({"true, true", "false, false"})
        @DisplayName("setValue(Boolean) correctly sets the boolean value")
        void setValueBooleanObject_setsCorrectValue(Boolean input, boolean expected) {
            mutableBoolean.setValue(input);
            assertEquals(expected, mutableBoolean.booleanValue());
            assertEquals(expected, mutableBoolean.isTrue());
            assertEquals(!expected, mutableBoolean.isFalse());
        }

        @Test
        @DisplayName("setValue(null) throws NullPointerException")
        void setValueBooleanObject_null_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> mutableBoolean.setValue((Boolean) null));
        }

        @Test
        @DisplayName("setValue(Boolean.TRUE) changes value from false to true")
        void setValueBooleanObject_true_changesFromFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setValue(Boolean.TRUE);
            assertTrue(mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean.FALSE) changes value from true to false")
        void setValueBooleanObject_false_changesFromTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setValue(Boolean.FALSE);
            assertFalse(mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("toBoolean() Tests")
    class ToBooleanTests {

        @Test
        @DisplayName("toBoolean() returns Boolean.TRUE when value is true")
        void toBoolean_whenTrue_returnsBooleanTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE when value is false")
        void toBoolean_whenFalse_returnsBooleanFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE by default constructor")
        void toBoolean_defaultConstructor_returnsBooleanFalse() {
            assertEquals(Boolean.FALSE, new MutableBoolean().toBoolean());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {

        @Test
        @DisplayName("toString() returns 'true' when value is true")
        void toString_whenTrue_returnsTrueString() {
            mutableBoolean.setValue(true);
            assertEquals("true", mutableBoolean.toString());
        }

        @Test
        @DisplayName("toString() returns 'false' when value is false")
        void toString_whenFalse_returnsFalseString() {
            mutableBoolean.setValue(false);
            assertEquals("false", mutableBoolean.toString());
        }

        @Test
        @DisplayName("toString() returns 'false' by default constructor")
        void toString_defaultConstructor_returnsFalseString() {
            assertEquals("false", new MutableBoolean().toString());
        }

        @Test
        @DisplayName("toString() consistency after value change")
        void toString_consistencyAfterChange() {
            mutableBoolean.setValue(true);
            assertEquals("true", mutableBoolean.toString());
            mutableBoolean.setValue(false);
            assertEquals("false", mutableBoolean.toString());
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
            assertEquals(Boolean.FALSE, mb.getValue());
            assertEquals("false", mb.toString());
        }

        @Test
        @DisplayName("Constructor with boolean true initializes to true")
        void constructorWithBoolean_true_initializesToTrue() {
            MutableBoolean mb = new MutableBoolean(true);
            assertTrue(mb.booleanValue());
            assertEquals(Boolean.TRUE, mb.getValue());
            assertEquals("true", mb.toString());
        }

        @Test
        @DisplayName("Constructor with boolean false initializes to false")
        void constructorWithBoolean_false_initializesToFalse() {
            MutableBoolean mb = new MutableBoolean(false);
            assertFalse(mb.booleanValue());
            assertEquals(Boolean.FALSE, mb.getValue());
            assertEquals("false", mb.toString());
        }

        @Test
        @DisplayName("Constructor with Boolean.TRUE initializes to true")
        void constructorWithBooleanObject_true_initializesToTrue() {
            MutableBoolean mb = new MutableBoolean(Boolean.TRUE);
            assertTrue(mb.booleanValue());
            assertEquals(Boolean.TRUE, mb.getValue());
            assertEquals("true", mb.toString());
        }

        @Test
        @DisplayName("Constructor with Boolean.FALSE initializes to false")
        void constructorWithBooleanObject_false_initializesToFalse() {
            MutableBoolean mb = new MutableBoolean(Boolean.FALSE);
            assertFalse(mb.booleanValue());
            assertEquals(Boolean.FALSE, mb.getValue());
            assertEquals("false", mb.toString());
        }

        @Test
        @DisplayName("Constructor with null Boolean throws NullPointerException")
        void constructorWithBooleanObject_null_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> new MutableBoolean((Boolean) null));
        }
    }
}