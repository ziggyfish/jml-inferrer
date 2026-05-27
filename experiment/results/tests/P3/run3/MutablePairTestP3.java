package org.apache.commons.lang3.tuple.p3;

import org.apache.commons.lang3.tuple.MutablePair;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

@DisplayName("MutablePair Unit Tests (P3)")
class MutablePairTestP3P3 {

    // --- emptyArray() tests ---

    @Test
    @DisplayName("emptyArray() should return an empty array")
    void emptyArray_shouldReturnEmptyArray() {
        MutablePair<String, Integer>[] emptyArray = MutablePair.emptyArray();
        assertNotNull(emptyArray, "emptyArray() should not return null");
        assertEquals(0, emptyArray.length, "emptyArray() should return an array of length 0");
    }

    @Test
    @DisplayName("emptyArray() should return a new array each time")
    void emptyArray_shouldReturnNewArrayEachTime() {
        MutablePair<String, Integer>[] array1 = MutablePair.emptyArray();
        MutablePair<String, Integer>[] array2 = MutablePair.emptyArray();
        assertNotSame(array1, array2, "emptyArray() should return different array instances");
    }

    // --- of(L left, R right) tests ---

    @Test
    @DisplayName("of(L, R) should create a pair with non-null values")
    void of_nonNullValues_shouldCreatePair() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", 123);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Hello", pair.getLeft(), "Left value should match");
        assertEquals(123, pair.getRight(), "Right value should match");
    }

    @Test
    @DisplayName("of(L, R) should create a pair with null left value")
    void of_nullLeftValue_shouldCreatePair() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 123);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(123, pair.getRight(), "Right value should match");
    }

    @Test
    @DisplayName("of(L, R) should create a pair with null right value")
    void of_nullRightValue_shouldCreatePair() {
        MutablePair<String, Integer> pair = MutablePair.of("Hello", null);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Hello", pair.getLeft(), "Left value should match");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    @DisplayName("of(L, R) should create a pair with both null values")
    void of_bothNullValues_shouldCreatePair() {
        MutablePair<String, Integer> pair = MutablePair.of(null, null);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    @DisplayName("of(L, R) should handle different types")
    void of_differentTypes_shouldCreatePair() {
        MutablePair<Double, Boolean> pair = MutablePair.of(3.14, true);
        assertNotNull(pair);
        assertEquals(3.14, pair.getLeft());
        assertTrue(pair.getRight());
    }

    // --- of(Map.Entry<L, R> pair) tests ---

    @Test
    @DisplayName("of(Map.Entry) should create a pair from a non-null entry")
    void of_mapEntry_nonNullEntry_shouldCreatePair() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertEquals(456, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a pair from an entry with null key")
    void of_mapEntry_nullKeyEntry_shouldCreatePair() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 456);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left value should be null");
        assertEquals(456, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a pair from an entry with null value")
    void of_mapEntry_nullValueEntry_shouldCreatePair() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Key", null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Key", pair.getLeft(), "Left value should match entry's key");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    @DisplayName("of(Map.Entry) should create a pair from an entry with both nulls")
    void of_mapEntry_bothNullsEntry_shouldCreatePair() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        MutablePair<String, Integer> pair = MutablePair.of(entry);
        assertNotNull(pair, "Pair should not be null");
        assertNull(pair.getLeft(), "Left value should be null");
        assertNull(pair.getRight(), "Right value should be null");
    }

    @Test
    @DisplayName("of(Map.Entry) should throw NullPointerException for null entry")
    void of_mapEntry_nullEntry_shouldThrowNPE() {
        Map.Entry<String, Integer> nullEntry = null;
        assertThrows(NullPointerException.class, () -> MutablePair.of(nullEntry),
                "of(Map.Entry) should throw NullPointerException for null entry");
    }

    // --- ofNonNull(L left, R right) tests ---

    @Test
    @DisplayName("ofNonNull(L, R) should create a pair with non-null values")
    void ofNonNull_nonNullValues_shouldCreatePair() {
        MutablePair<String, Integer> pair = MutablePair.ofNonNull("Alpha", 789);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Alpha", pair.getLeft(), "Left value should match");
        assertEquals(789, pair.getRight(), "Right value should match");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for null left value")
    void ofNonNull_nullLeftValue_shouldThrowNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, 789),
                "ofNonNull(L, R) should throw NullPointerException for null left value");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for null right value")
    void ofNonNull_nullRightValue_shouldThrowNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull("Alpha", null),
                "ofNonNull(L, R) should throw NullPointerException for null right value");
    }

    @Test
    @DisplayName("ofNonNull(L, R) should throw NullPointerException for both null values")
    void ofNonNull_bothNullValues_shouldThrowNPE() {
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(null, null),
                "ofNonNull(L, R) should throw NullPointerException for both null values");
    }

    // --- ofNonNull(Map.Entry<L, R> pair) tests ---

    @Test
    @DisplayName("ofNonNull(Map.Entry) should create a pair from a non-null entry with non-null key/value")
    void ofNonNull_mapEntry_nonNullEntryAndValues_shouldCreatePair() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Beta", 101);
        MutablePair<String, Integer> pair = MutablePair.ofNonNull(entry);
        assertNotNull(pair, "Pair should not be null");
        assertEquals("Beta", pair.getLeft(), "Left value should match entry's key");
        assertEquals(101, pair.getRight(), "Right value should match entry's value");
    }

    @Test
    @DisplayName("ofNonNull(Map.Entry) should throw NullPointerException for null entry")
    void ofNonNull_mapEntry_nullEntry_shouldThrowNPE() {
        Map.Entry<String, Integer> nullEntry = null;
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(nullEntry),
                "ofNonNull(Map.Entry) should throw NullPointerException for null entry");
    }

    @Test
    @DisplayName("ofNonNull(Map.Entry) should throw NullPointerException for entry with null key")
    void ofNonNull_mapEntry_nullKeyEntry_shouldThrowNPE() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, 101);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null key");
    }

    @Test
    @DisplayName("ofNonNull(Map.Entry) should throw NullPointerException for entry with null value")
    void ofNonNull_mapEntry_nullValueEntry_shouldThrowNPE() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>("Beta", null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with null value");
    }

    @Test
    @DisplayName("ofNonNull(Map.Entry) should throw NullPointerException for entry with both nulls")
    void ofNonNull_mapEntry_bothNullsEntry_shouldThrowNPE() {
        Map.Entry<String, Integer> entry = new AbstractMap.SimpleEntry<>(null, null);
        assertThrows(NullPointerException.class, () -> MutablePair.ofNonNull(entry),
                "ofNonNull(Map.Entry) should throw NullPointerException for entry with both nulls");
    }

    // --- getLeft() tests ---

    @Test
    @DisplayName("getLeft() should return the correct left value")
    void getLeft_shouldReturnCorrectValue() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals("LeftValue", pair.getLeft());
    }

    @Test
    @DisplayName("getLeft() should return null if left value is null")
    void getLeft_nullValue_shouldReturnNull() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        assertNull(pair.getLeft());
    }

    // --- getRight() tests ---

    @Test
    @DisplayName("getRight() should return the correct right value")
    void getRight_shouldReturnCorrectValue() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", 1);
        assertEquals(1, pair.getRight());
    }

    @Test
    @DisplayName("getRight() should return null if right value is null")
    void getRight_nullValue_shouldReturnNull() {
        MutablePair<String, Integer> pair = MutablePair.of("LeftValue", null);
        assertNull(pair.getRight());
    }

    // --- setLeft(L left) tests ---

    @Test
    @DisplayName("setLeft() should update the left value to a non-null value")
    void setLeft_nonNullValue_shouldUpdate() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft("NewLeft");
        assertEquals("NewLeft", pair.getLeft());
        assertEquals(1, pair.getRight()); // Ensure right value is unchanged
    }

    @Test
    @DisplayName("setLeft() should update the left value to null")
    void setLeft_nullValue_shouldUpdate() {
        MutablePair<String, Integer> pair = MutablePair.of("OldLeft", 1);
        pair.setLeft(null);
        assertNull(pair.getLeft());
        assertEquals(1, pair.getRight()); // Ensure right value is unchanged
    }

    @Test
    @DisplayName("setLeft() should update the left value from null to non-null")
    void setLeft_fromNullToNonNull_shouldUpdate() {
        MutablePair<String, Integer> pair = MutablePair.of(null, 1);
        pair.setLeft("NonNullLeft");
        assertEquals("NonNullLeft", pair.getLeft());
    }

    // --- setRight(R right) tests ---

    @Test
    @DisplayName("setRight() should update the right value to a non-null value")
    void setRight_nonNullValue_shouldUpdate() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(20);
        assertEquals("Left", pair.getLeft()); // Ensure left value is unchanged
        assertEquals(20, pair.getRight());
    }

    @Test
    @DisplayName("setRight() should update the right value to null")
    void setRight_nullValue_shouldUpdate() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 10);
        pair.setRight(null);
        assertEquals("Left", pair.getLeft()); // Ensure left value is unchanged
        assertNull(pair.getRight());
    }

    @Test
    @DisplayName("setRight() should update the right value from null to non-null")
    void setRight_fromNullToNonNull_shouldUpdate() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        pair.setRight(30);
        assertEquals(30, pair.getRight());
    }

    // --- setValue(R value) tests ---

    @Test
    @DisplayName("setValue() should update the right value and return the old value (non-null to non-null)")
    void setValue_nonNullToNonNull_shouldUpdateAndReturnOld() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 100);
        Integer oldValue = pair.setValue(200);
        assertEquals(200, pair.getRight());
        assertEquals(100, oldValue);
        assertEquals("Left", pair.getLeft()); // Ensure left value is unchanged
    }

    @Test
    @DisplayName("setValue() should update the right value and return the old value (non-null to null)")
    void setValue_nonNullToNull_shouldUpdateAndReturnOld() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", 100);
        Integer oldValue = pair.setValue(null);
        assertNull(pair.getRight());
        assertEquals(100, oldValue);
    }

    @Test
    @DisplayName("setValue() should update the right value and return the old value (null to non-null)")
    void setValue_nullToNonNull_shouldUpdateAndReturnOld() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        Integer oldValue = pair.setValue(200);
        assertEquals(200, pair.getRight());
        assertNull(oldValue);
    }

    @Test
    @DisplayName("setValue() should update the right value and return the old value (null to null)")
    void setValue_nullToNull_shouldUpdateAndReturnOld() {
        MutablePair<String, Integer> pair = MutablePair.of("Left", null);
        Integer oldValue = pair.setValue(null);
        assertNull(pair.getRight());
        assertNull(oldValue);
    }

    // --- General behavior tests (e.g., toString, equals, hashCode) ---
    // Although not explicitly specified in JML, these are standard contract methods.

    @Test
    @DisplayName("toString() should return a correct string representation")
    void toString_shouldReturnCorrectString() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        assertEquals("(A,1)", pair.toString());

        MutablePair<String, Integer> nullLeft = MutablePair.of(null, 1);
        assertEquals("(null,1)", nullLeft.toString());

        MutablePair<String, Integer> nullRight = MutablePair.of("A", null);
        assertEquals("(A,null)", nullRight.toString());

        MutablePair<String, Integer> bothNull = MutablePair.of(null, null);
        assertEquals("(null,null)", bothNull.toString());
    }

    @Test
    @DisplayName("equals() should return true for identical pairs")
    void equals_identicalPairs_shouldBeTrue() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);
        assertEquals(pair1, pair2);
        assertEquals(pair1, pair1); // Self-equality
    }

    @Test
    @DisplayName("equals() should return false for different left values")
    void equals_differentLeft_shouldBeFalse() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("B", 1);
        assertNotEquals(pair1, pair2);
    }

    @Test
    @DisplayName("equals() should return false for different right values")
    void equals_differentRight_shouldBeFalse() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 2);
        assertNotEquals(pair1, pair2);
    }

    @Test
    @DisplayName("equals() should handle null values correctly")
    void equals_nullValues_shouldBeCorrect() {
        MutablePair<String, Integer> pair1 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair2 = MutablePair.of(null, 1);
        assertEquals(pair1, pair2);

        MutablePair<String, Integer> pair3 = MutablePair.of("A", null);
        MutablePair<String, Integer> pair4 = MutablePair.of("A", null);
        assertEquals(pair3, pair4);

        MutablePair<String, Integer> pair5 = MutablePair.of(null, null);
        MutablePair<String, Integer> pair6 = MutablePair.of(null, null);
        assertEquals(pair5, pair6);

        assertNotEquals(MutablePair.of(null, 1), MutablePair.of("A", 1));
        assertNotEquals(MutablePair.of("A", null), MutablePair.of("A", 1));
    }

    @Test
    @DisplayName("equals() should return false for different object types")
    void equals_differentType_shouldBeFalse() {
        MutablePair<String, Integer> pair = MutablePair.of("A", 1);
        assertNotEquals(pair, "A string");
        assertNotEquals(pair, null);
    }

    @Test
    @DisplayName("hashCode() should be consistent with equals()")
    void hashCode_consistentWithEquals() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("A", 1);
        assertEquals(pair1.hashCode(), pair2.hashCode());

        MutablePair<String, Integer> pair3 = MutablePair.of(null, 1);
        MutablePair<String, Integer> pair4 = MutablePair.of(null, 1);
        assertEquals(pair3.hashCode(), pair4.hashCode());

        MutablePair<String, Integer> pair5 = MutablePair.of("A", null);
        MutablePair<String, Integer> pair6 = MutablePair.of("A", null);
        assertEquals(pair5.hashCode(), pair6.hashCode());

        MutablePair<String, Integer> pair7 = MutablePair.of(null, null);
        MutablePair<String, Integer> pair8 = MutablePair.of(null, null);
        assertEquals(pair7.hashCode(), pair8.hashCode());
    }

    @Test
    @DisplayName("hashCode() should differ for different pairs")
    void hashCode_differentPairs_shouldDiffer() {
        MutablePair<String, Integer> pair1 = MutablePair.of("A", 1);
        MutablePair<String, Integer> pair2 = MutablePair.of("B", 1);
        MutablePair<String, Integer> pair3 = MutablePair.of("A", 2);

        assertNotEquals(pair1.hashCode(), pair2.hashCode());
        assertNotEquals(pair1.hashCode(), pair3.hashCode());
    }
}