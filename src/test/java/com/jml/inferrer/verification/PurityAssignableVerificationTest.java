package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Tier 1 formal verification tests for purity and assignable clause specifications.
 * Each test writes JML comment syntax directly and invokes OpenJML ESC.
 */
class PurityAssignableVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Pure methods
    // =========================================================================

    @Test
    @DisplayName("Pure method: simple addition")
    void pureMethod() throws IOException {
        String source = """
                public class PureMethod {
                    public int add(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureMethod", "add"));
    }

    @Test
    @DisplayName("Pure method: multiplication")
    void pureMultiplication() throws IOException {
        String source = """
                public class PureMultiplication {
                    public int multiply(int a, int b) {
                        return a * b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureMultiplication", "multiply"));
    }

    @Test
    @DisplayName("Pure method: boolean comparison")
    void pureBooleanComparison() throws IOException {
        String source = """
                public class PureBooleanComparison {
                    public boolean isPositive(int n) {
                        return n > 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureBooleanComparison", "isPositive"));
    }

    @Test
    @DisplayName("Pure method: ternary expression")
    void pureTernary() throws IOException {
        String source = """
                public class PureTernary {
                    public int max(int a, int b) {
                        return a >= b ? a : b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureTernary", "max"));
    }

    @Test
    @DisplayName("Pure method: multi-branch conditional")
    void pureMultiBranch() throws IOException {
        String source = """
                public class PureMultiBranch {
                    public int sign(int x) {
                        if (x > 0) return 1;
                        if (x < 0) return -1;
                        return 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureMultiBranch", "sign"));
    }

    @Test
    @DisplayName("Pure method: reading field without modifying")
    void pureFieldRead() throws IOException {
        String source = """
                public class PureFieldRead {
                    int value;
                    public int getValue() {
                        return this.value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureFieldRead", "getValue"));
    }

    @Test
    @DisplayName("Pure method: reading two fields")
    void pureTwoFieldReads() throws IOException {
        String source = """
                public class PureTwoFieldReads {
                    int x;
                    int y;
                    public int sum() {
                        return this.x + this.y;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureTwoFieldReads", "sum"));
    }

    @Test
    @DisplayName("Pure method: reading array element")
    void pureArrayRead() throws IOException {
        String source = """
                public class PureArrayRead {
                    int[] data;
                    public int getAt(int idx) {
                        return this.data[idx];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureArrayRead", "getAt"));
    }

    @Test
    @DisplayName("Pure method: compound expression with locals")
    void pureCompoundWithLocals() throws IOException {
        String source = """
                public class PureCompoundWithLocals {
                    public int distSquared(int x1, int y1, int x2, int y2) {
                        int dx = x2 - x1;
                        int dy = y2 - y1;
                        return dx * dx + dy * dy;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureCompoundWithLocals", "distSquared"));
    }

    @Test
    @DisplayName("Pure method: string length accessor")
    void pureStringLength() throws IOException {
        String source = """
                public class PureStringLength {
                    public int len(String s) {
                        return s.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureStringLength", "len"));
    }

    // =========================================================================
    // Assignable nothing
    // =========================================================================

    @Test
    @DisplayName("Assignable nothing: pure computation returns value")
    void assignableNothing() throws IOException {
        String source = """
                public class AssignableNothing {
                    public int add(int a, int b) {
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableNothing", "add"));
    }

    @Test
    @DisplayName("Assignable nothing: comparison returns boolean")
    void assignableNothingBoolean() throws IOException {
        String source = """
                public class AssignableNothingBoolean {
                    public boolean isEqual(int a, int b) {
                        return a == b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableNothingBoolean", "isEqual"));
    }

    @Test
    @DisplayName("Assignable nothing: local variables only")
    void assignableNothingLocals() throws IOException {
        String source = """
                public class AssignableNothingLocals {
                    public int absDiff(int a, int b) {
                        int diff = a - b;
                        if (diff < 0) diff = -diff;
                        return diff;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableNothingLocals", "absDiff"));
    }

    // =========================================================================
    // Assignable single field
    // =========================================================================

    @Test
    @DisplayName("Assignable single field: simple setter")
    void assignableField() throws IOException {
        String source = """
                public class AssignableField {
                    int value;
                    public void setValue(int v) {
                        this.value = v;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableField", "setValue"));
    }

    @Test
    @DisplayName("Assignable single field: increment")
    void assignableFieldIncrement() throws IOException {
        String source = """
                public class AssignableFieldIncrement {
                    int count;
                    public void increment() {
                        this.count++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableFieldIncrement", "increment"));
    }

    @Test
    @DisplayName("Assignable single field: conditional update")
    void assignableFieldConditional() throws IOException {
        String source = """
                public class AssignableFieldConditional {
                    int max;
                    public void updateMax(int value) {
                        if (value > this.max) {
                            this.max = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableFieldConditional", "updateMax"));
    }

    @Test
    @DisplayName("Assignable single boolean field: toggle")
    void assignableBooleanToggle() throws IOException {
        String source = """
                public class AssignableBooleanToggle {
                    boolean active;
                    public void toggle() {
                        this.active = !this.active;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableBooleanToggle", "toggle"));
    }

    // =========================================================================
    // Assignable multiple fields
    // =========================================================================

    @Test
    @DisplayName("Assignable multiple fields: set x and y")
    void assignableMultipleFields() throws IOException {
        String source = """
                public class AssignableMultipleFields {
                    int x;
                    int y;
                    public void setCoords(int a, int b) {
                        this.x = a;
                        this.y = b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableMultipleFields", "setCoords"));
    }

    @Test
    @DisplayName("Assignable three fields: set color")
    void assignableThreeFields() throws IOException {
        String source = """
                public class AssignableThreeFields {
                    int r;
                    int g;
                    int b;
                    public void setColor(int red, int green, int blue) {
                        this.r = red;
                        this.g = green;
                        this.b = blue;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableThreeFields", "setColor"));
    }

    @Test
    @DisplayName("Assignable two fields: swap")
    void assignableSwapFields() throws IOException {
        String source = """
                public class AssignableSwapFields {
                    int a;
                    int b;
                    public void swap() {
                        int tmp = this.a;
                        this.a = this.b;
                        this.b = tmp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableSwapFields", "swap"));
    }

    @Test
    @DisplayName("Assignable size + data: stack push")
    void assignableStackPush() throws IOException {
        String source = """
                public class AssignableStackPush {
                    int[] data;
                    int size;
                    public void push(int value) {
                        this.data[this.size] = value;
                        this.size++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableStackPush", "push"));
    }

    // =========================================================================
    // Assignable array elements
    // =========================================================================

    @Test
    @DisplayName("Assignable array elements: zero fill")
    void assignableArrayElements() throws IOException {
        String source = """
                public class AssignableArrayElements {
                    public void zeroFill(int[] arr) {
                        for (int i = 0; i < arr.length; i++) {
                            arr[i] = 0;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableArrayElements", "zeroFill"));
    }

    @Test
    @DisplayName("Assignable array: fill with constant value")
    void assignableArrayFillConstant() throws IOException {
        String source = """
                public class AssignableArrayFillConstant {
                    public void fill(int[] arr, int val) {
                        for (int i = 0; i < arr.length; i++) {
                            arr[i] = val;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableArrayFillConstant", "fill"));
    }

    @Test
    @DisplayName("Assignable array: copy into parameter array")
    void assignableArrayCopy() throws IOException {
        String source = """
                public class AssignableArrayCopy {
                    public void copy(int[] src, int[] dst) {
                        for (int i = 0; i < src.length; i++) {
                            dst[i] = src[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableArrayCopy", "copy"));
    }

    @Test
    @DisplayName("Assignable array: negate all elements")
    void assignableArrayNegate() throws IOException {
        String source = """
                public class AssignableArrayNegate {
                    public void negate(int[] arr) {
                        for (int i = 0; i < arr.length; i++) {
                            arr[i] = -arr[i];
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableArrayNegate", "negate"));
    }

    @Test
    @DisplayName("Assignable single array element by index")
    void assignableSingleArrayElement() throws IOException {
        String source = """
                public class AssignableSingleArrayElement {
                    public void setAt(int[] arr, int idx, int val) {
                        arr[idx] = val;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableSingleArrayElement", "setAt"));
    }

    // =========================================================================
    // Complex: assignable + pre + post + loops
    // =========================================================================

    @Test
    @DisplayName("Assignable field via loop: decrement to zero")
    void assignableFieldViaLoop() throws IOException {
        String source = """
                public class AssignableFieldViaLoop {
                    int count;
                    public void drainToZero() {
                        while (this.count > 0) {
                            this.count--;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableFieldViaLoop", "drainToZero"));
    }

    @Test
    @DisplayName("Pure with loop: search array without modifying")
    void pureWithLoop() throws IOException {
        String source = """
                public class PureWithLoop {
                    public int indexOf(int[] arr, int target) {
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] == target) return i;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PureWithLoop", "indexOf"));
    }

    @Test
    @DisplayName("Assignable field + array: populate and track size")
    void assignableFieldAndArray() throws IOException {
        String source = """
                public class AssignableFieldAndArray {
                    int[] data;
                    int size;
                    public void addMany(int value, int count) {
                        for (int i = 0; i < count; i++) {
                            this.data[this.size] = value;
                            this.size++;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableFieldAndArray", "addMany"));
    }

    @Test
    @DisplayName("Assignable everything: reset object state")
    void assignableEverythingReset() throws IOException {
        String source = """
                public class AssignableEverythingReset {
                    int x;
                    int y;
                    int z;
                    boolean active;
                    public void reset() {
                        this.x = 0;
                        this.y = 0;
                        this.z = 0;
                        this.active = false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableEverythingReset", "reset"));
    }

    @Test
    @DisplayName("Assignable with conditional: set field only if condition met")
    void assignableConditionalWrite() throws IOException {
        String source = """
                public class AssignableConditionalWrite {
                    int bestScore;
                    public void submitScore(int score) {
                        if (score > this.bestScore) {
                            this.bestScore = score;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableConditionalWrite", "submitScore"));
    }

    @Test
    @DisplayName("Assignable array + return: extract and replace")
    void assignableArrayExtractReplace() throws IOException {
        String source = """
                public class AssignableArrayExtractReplace {
                    public int getAndSet(int[] arr, int idx, int newVal) {
                        int old = arr[idx];
                        arr[idx] = newVal;
                        return old;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AssignableArrayExtractReplace", "getAndSet"));
    }
}
