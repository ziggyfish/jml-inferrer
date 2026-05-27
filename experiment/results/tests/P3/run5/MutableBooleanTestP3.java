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
        @DisplayName("booleanValue() returns false by default constructor")
        void booleanValue_defaultConstructor_returnsFalse() {
            assertFalse(mutableBoolean.booleanValue());
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
        @DisplayName("compareTo() with null other throws NullPointerException")
        void compareTo_nullOther_throwsNullPointerException() {
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
        @DisplayName("equals() returns true for equal values (true vs true)")
        void equals_trueVsTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns true for equal values (false vs false)")
        void equals_falseVsFalse_returnsTrue() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertTrue(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for different values (true vs false)")
        void equals_trueVsFalse_returnsFalse() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertFalse(mutableBoolean.equals(other));
        }

        @Test
        @DisplayName("equals() returns false for different values (false vs true)")
        void equals_falseVsTrue_returnsFalse() {
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
        }

        @Test
        @DisplayName("equals() returns false for Boolean object with different value")
        void equals_booleanObject_differentValue_returnsFalse() {
            mutableBoolean.setValue(true);
            assertFalse(mutableBoolean.equals(Boolean.FALSE));
        }

        @Test
        @DisplayName("equals() returns true for Boolean object with same value")
        void equals_booleanObject_sameValue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertTrue(mutableBoolean.equals(Boolean.TRUE));
        }
    }

    @Nested
    @DisplayName("getValue() Tests")
    class GetValueTests {

        @Test
        @DisplayName("getValue() returns Boolean.TRUE when internal value is true")
        void getValue_whenTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE when internal value is false")
        void getValue_whenFalse_returnsFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }

        @Test
        @DisplayName("getValue() returns Boolean.FALSE by default constructor")
        void getValue_defaultConstructor_returnsFalse() {
            assertEquals(Boolean.FALSE, mutableBoolean.getValue());
        }
    }

    @Nested
    @DisplayName("hashCode() Tests")
    class HashCodeTests {

        @Test
        @DisplayName("hashCode() returns same value for equal objects (true)")
        void hashCode_true_returnsSameValue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(true);
            assertEquals(mutableBoolean.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns same value for equal objects (false)")
        void hashCode_false_returnsSameValue() {
            mutableBoolean.setValue(false);
            MutableBoolean other = new MutableBoolean(false);
            assertEquals(mutableBoolean.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("hashCode() returns different value for different objects")
        void hashCode_differentValues_returnsDifferentValue() {
            mutableBoolean.setValue(true);
            MutableBoolean other = new MutableBoolean(false);
            assertNotEquals(mutableBoolean.hashCode(), other.hashCode());
        }

        @Test
        @DisplayName("hashCode() for true matches Boolean.TRUE.hashCode()")
        void hashCode_true_matchesBooleanTrueHashCode() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE.hashCode(), mutableBoolean.hashCode());
        }

        @Test
        @DisplayName("hashCode() for false matches Boolean.FALSE.hashCode()")
        void hashCode_false_matchesBooleanFalseHashCode() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE.hashCode(), mutableBoolean.hashCode());
        }
    }

    @Nested
    @DisplayName("isFalse() Tests")
    class IsFalseTests {

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
        @DisplayName("isFalse() returns true by default constructor")
        void isFalse_defaultConstructor_returnsTrue() {
            assertTrue(mutableBoolean.isFalse());
        }
    }

    @Nested
    @DisplayName("isTrue() Tests")
    class IsTrueTests {

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
        @DisplayName("isTrue() returns false by default constructor")
        void isTrue_defaultConstructor_returnsFalse() {
            assertFalse(mutableBoolean.isTrue());
        }
    }

    @Nested
    @DisplayName("setFalse() Tests")
    class SetFalseTests {

        @Test
        @DisplayName("setFalse() sets internal value to false from true")
        void setFalse_fromTrue_setsToFalse() {
            mutableBoolean.setValue(true);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            assertTrue(mutableBoolean.isFalse());
            assertFalse(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("setFalse() sets internal value to false from false")
        void setFalse_fromFalse_staysFalse() {
            mutableBoolean.setValue(false);
            mutableBoolean.setFalse();
            assertFalse(mutableBoolean.booleanValue());
            assertTrue(mutableBoolean.isFalse());
            assertFalse(mutableBoolean.isTrue());
        }
    }

    @Nested
    @DisplayName("setTrue() Tests")
    class SetTrueTests {

        @Test
        @DisplayName("setTrue() sets internal value to true from false")
        void setTrue_fromFalse_setsToTrue() {
            mutableBoolean.setValue(false);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            assertFalse(mutableBoolean.isFalse());
            assertTrue(mutableBoolean.isTrue());
        }

        @Test
        @DisplayName("setTrue() sets internal value to true from true")
        void setTrue_fromTrue_staysTrue() {
            mutableBoolean.setValue(true);
            mutableBoolean.setTrue();
            assertTrue(mutableBoolean.booleanValue());
            assertFalse(mutableBoolean.isFalse());
            assertTrue(mutableBoolean.isTrue());
        }
    }

    @Nested
    @DisplayName("setValue(boolean value) Tests")
    class SetValueBooleanTests {

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("setValue(boolean) sets the internal boolean value correctly")
        void setValueBoolean_setsValueCorrectly(boolean value) {
            mutableBoolean.setValue(value);
            assertEquals(value, mutableBoolean.booleanValue());
        }
    }

    @Nested
    @DisplayName("setValue(Boolean value) Tests")
    class SetValueBooleanObjectTests {

        @ParameterizedTest
        @CsvSource({"true, true", "false, false"})
        @DisplayName("setValue(Boolean) sets the internal boolean value correctly")
        void setValueBooleanObject_setsValueCorrectly(Boolean input, boolean expected) {
            mutableBoolean.setValue(input);
            assertEquals(expected, mutableBoolean.booleanValue());
        }

        @Test
        @DisplayName("setValue(Boolean) with null value throws NullPointerException")
        void setValueBooleanObject_nullValue_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> mutableBoolean.setValue((Boolean) null));
        }
    }

    @Nested
    @DisplayName("toBoolean() Tests")
    class ToBooleanTests {

        @Test
        @DisplayName("toBoolean() returns Boolean.TRUE when internal value is true")
        void toBoolean_whenTrue_returnsTrue() {
            mutableBoolean.setValue(true);
            assertEquals(Boolean.TRUE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE when internal value is false")
        void toBoolean_whenFalse_returnsFalse() {
            mutableBoolean.setValue(false);
            assertEquals(Boolean.FALSE, mutableBoolean.toBoolean());
        }

        @Test
        @DisplayName("toBoolean() returns Boolean.FALSE by default constructor")
        void toBoolean_defaultConstructor_returnsFalse() {
            assertEquals(Boolean.FALSE, mutableBoolean.toBoolean());
        }
    }

    @Nested
    @DisplayName("toString() Tests")
    class ToStringTests {

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
        @DisplayName("toString() returns 'false' by default constructor")
        void toString_defaultConstructor_returnsFalseString() {
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
        }

        @ParameterizedTest
        @ValueSource(booleans = {true, false})
        @DisplayName("Constructor with boolean initializes correctly")
        void constructor_withBoolean_initializesCorrectly(boolean value) {
            MutableBoolean mb = new MutableBoolean(value);
            assertEquals(value, mb.booleanValue());
        }

        @ParameterizedTest
        @CsvSource({"true, true", "false, false"})
        @DisplayName("Constructor with Boolean initializes correctly")
        void constructor_withBooleanObject_initializesCorrectly(Boolean value, boolean expected) {
            MutableBoolean mb = new MutableBoolean(value);
            assertEquals(expected, mb.booleanValue());
        }

        @Test
        @DisplayName("Constructor with null Boolean throws NullPointerException")
        void constructor_withNullBoolean_throwsNullPointerException() {
            assertThrows(NullPointerException.class, () -> new MutableBoolean((Boolean) null));
        }
    }
}