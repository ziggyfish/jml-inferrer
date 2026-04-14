package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for purity analysis, assignable clauses, and field
 * modification tracking: pure methods, observer methods, mutators,
 * and complex assignable specifications.
 */
class PurityFieldModVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Pure computation methods (no side effects)
    // =========================================================================

    @Test
    @DisplayName("Pure: arithmetic with parameters only")
    void pureArithmetic() throws IOException {
        String source = """
                public class PureCalc1 {
                    public int add(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureCalc1", "add"));
    }

    @Test
    @DisplayName("Pure: boolean comparison")
    void pureBooleanComparison() throws IOException {
        String source = """
                public class PureCalc2 {
                    public boolean isGreater(int a, int b) {
                        return a > b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureCalc2", "isGreater"));
    }

    @Test
    @DisplayName("Pure: complex expression with locals only")
    void pureComplexExpression() throws IOException {
        String source = """
                public class PureCalc3 {
                    public double hypotenuse(double a, double b) {
                        double sumSquares = a * a + b * b;
                        return Math.sqrt(sumSquares);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureCalc3", "hypotenuse"));
    }

    @Test
    @DisplayName("Pure: ternary with no side effects")
    void pureTernary() throws IOException {
        String source = """
                public class PureCalc4 {
                    public int abs(int n) {
                        return n >= 0 ? n : -n;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureCalc4", "abs"));
    }

    @Test
    @DisplayName("Pure: multi-branch conditional return")
    void pureMultiBranch() throws IOException {
        String source = """
                public class PureCalc5 {
                    public int classify(int n) {
                        if (n > 0) return 1;
                        if (n < 0) return -1;
                        return 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureCalc5", "classify"));
    }

    // =========================================================================
    // Observer methods (read fields, no writes)
    // =========================================================================

    @Test
    @DisplayName("Observer: return single field")
    void observerSingleField() throws IOException {
        String source = """
                public class Observer1 {
                    private int count;
                    public int getCount() {
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Observer1", "getCount"));
    }

    @Test
    @DisplayName("Observer: return computed from two fields")
    void observerTwoFields() throws IOException {
        String source = """
                public class Observer2 {
                    private int width;
                    private int height;
                    public int area() {
                        return width * height;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Observer2", "area"));
    }

    @Test
    @DisplayName("Observer: compare field to parameter")
    void observerCompare() throws IOException {
        String source = """
                public class Observer3 {
                    private int threshold;
                    public boolean isAbove(int value) {
                        return value > threshold;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Observer3", "isAbove"));
    }

    @Test
    @DisplayName("Observer: read array field element")
    void observerArrayRead() throws IOException {
        String source = """
                public class Observer4 {
                    private int[] data;
                    private int size;
                    public int get(int index) {
                        if (index < 0 || index >= size) throw new IndexOutOfBoundsException();
                        return data[index];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Observer4", "get"));
    }

    @Test
    @DisplayName("Observer: loop over field array without modification")
    void observerLoopRead() throws IOException {
        String source = """
                public class Observer5 {
                    private int[] data;
                    private int size;
                    public int sum() {
                        int total = 0;
                        for (int i = 0; i < size; i++) {
                            total += data[i];
                        }
                        return total;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Observer5", "sum"));
    }

    // =========================================================================
    // Mutator methods (single field write)
    // =========================================================================

    @Test
    @DisplayName("Mutator: simple field assignment")
    void mutatorSimpleAssign() throws IOException {
        String source = """
                public class Mutator1 {
                    private int value;
                    public void set(int v) {
                        this.value = v;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Mutator1", "set"));
    }

    @Test
    @DisplayName("Mutator: field increment")
    void mutatorIncrement() throws IOException {
        String source = """
                public class Mutator2 {
                    private int counter;
                    public void increment() {
                        counter++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Mutator2", "increment"));
    }

    @Test
    @DisplayName("Mutator: field compound assignment")
    void mutatorCompound() throws IOException {
        String source = """
                public class Mutator3 {
                    private int total;
                    public void addTo(int amount) {
                        total += amount;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Mutator3", "addTo"));
    }

    @Test
    @DisplayName("Mutator: boolean field toggle")
    void mutatorToggle() throws IOException {
        String source = """
                public class Mutator4 {
                    private boolean active;
                    public void toggle() {
                        active = !active;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Mutator4", "toggle"));
    }

    @Test
    @DisplayName("Mutator: conditional field update")
    void mutatorConditional() throws IOException {
        String source = """
                public class Mutator5 {
                    private int maxSeen;
                    public void update(int value) {
                        if (value > maxSeen) {
                            maxSeen = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Mutator5", "update"));
    }

    // =========================================================================
    // Multi-field mutations with assignable
    // =========================================================================

    @Test
    @DisplayName("MultiMutator: set x and y coordinates")
    void multiMutatorSetCoords() throws IOException {
        String source = """
                public class MultiMut1 {
                    private int x;
                    private int y;
                    public void setPosition(int x, int y) {
                        this.x = x;
                        this.y = y;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiMut1", "setPosition"));
    }

    @Test
    @DisplayName("MultiMutator: reset all fields to default")
    void multiMutatorResetAll() throws IOException {
        String source = """
                public class MultiMut2 {
                    private int a;
                    private int b;
                    private boolean flag;
                    public void reset() {
                        a = 0;
                        b = 0;
                        flag = false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiMut2", "reset"));
    }

    @Test
    @DisplayName("MultiMutator: swap two fields")
    void multiMutatorSwap() throws IOException {
        String source = """
                public class MultiMut3 {
                    private int first;
                    private int second;
                    public void swap() {
                        int tmp = first;
                        first = second;
                        second = tmp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiMut3", "swap"));
    }

    // =========================================================================
    // Array element mutations
    // =========================================================================

    @Test
    @DisplayName("ArrayMutator: set single element")
    void arrayMutatorSetElement() throws IOException {
        String source = """
                public class ArrMut1 {
                    private int[] data;
                    public void setElement(int index, int value) {
                        if (index < 0 || index >= data.length) throw new IndexOutOfBoundsException();
                        data[index] = value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrMut1", "setElement"));
    }

    @Test
    @DisplayName("ArrayMutator: fill all elements with value")
    void arrayMutatorFillAll() throws IOException {
        String source = """
                public class ArrMut2 {
                    private int[] data;
                    public void fill(int value) {
                        for (int i = 0; i < data.length; i++) {
                            data[i] = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrMut2", "fill"));
    }

    @Test
    @DisplayName("ArrayMutator: increment all elements")
    void arrayMutatorIncrementAll() throws IOException {
        String source = """
                public class ArrMut3 {
                    public void incrementAll(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            arr[i]++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrMut3", "incrementAll"));
    }

    // =========================================================================
    // Field delta tracking (precise postconditions)
    // =========================================================================

    @Test
    @DisplayName("FieldDelta: increment by specific amount")
    void fieldDeltaIncrementByAmount() throws IOException {
        String source = """
                public class Delta1 {
                    private int score;
                    public void addPoints(int points) {
                        if (points < 0) throw new IllegalArgumentException();
                        score += points;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delta1", "addPoints"));
    }

    @Test
    @DisplayName("FieldDelta: decrement by one")
    void fieldDeltaDecrementByOne() throws IOException {
        String source = """
                public class Delta2 {
                    private int lives;
                    public void loseLife() {
                        if (lives <= 0) throw new IllegalStateException();
                        lives--;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delta2", "loseLife"));
    }

    @Test
    @DisplayName("FieldDelta: multiply field by factor")
    void fieldDeltaMultiply() throws IOException {
        String source = """
                public class Delta3 {
                    private int value;
                    public void scale(int factor) {
                        value *= factor;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delta3", "scale"));
    }

    @Test
    @DisplayName("FieldDelta: conditional increment")
    void fieldDeltaConditionalIncrement() throws IOException {
        String source = """
                public class Delta4 {
                    private int hits;
                    private int misses;
                    public void record(boolean success) {
                        if (success) {
                            hits++;
                        } else {
                            misses++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Delta4", "record"));
    }
}
