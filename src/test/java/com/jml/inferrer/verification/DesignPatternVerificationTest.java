package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for common design patterns: builders, factories,
 * iterators, observers, and fluent APIs.
 */
class DesignPatternVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Builder pattern
    // =========================================================================

    @Test
    @DisplayName("Builder: set name returns this")
    void builderSetName() throws IOException {
        String source = """
                public class PersonBuilder {
                    private String name;
                    private int age;
                    public PersonBuilder setName(String name) {
                        if (name == null) throw new IllegalArgumentException();
                        this.name = name;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PersonBuilder", "setName"));
    }

    @Test
    @DisplayName("Builder: set age with validation returns this")
    void builderSetAge() throws IOException {
        String source = """
                public class PersonBuilder2 {
                    private String name;
                    private int age;
                    public PersonBuilder2 setAge(int age) {
                        if (age < 0) throw new IllegalArgumentException();
                        this.age = age;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "PersonBuilder2", "setAge"));
    }

    @Test
    @DisplayName("Builder: set multiple fields in one method")
    void builderSetMultipleFields() throws IOException {
        String source = """
                public class RectBuilder {
                    private int x;
                    private int y;
                    private int width;
                    private int height;
                    public RectBuilder setBounds(int x, int y, int w, int h) {
                        if (w < 0 || h < 0) throw new IllegalArgumentException();
                        this.x = x;
                        this.y = y;
                        this.width = w;
                        this.height = h;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RectBuilder", "setBounds"));
    }

    // =========================================================================
    // Factory / creation patterns
    // =========================================================================

    @Test
    @DisplayName("Factory method: create with default values")
    void factoryDefault() throws IOException {
        String source = """
                public class Config {
                    private int timeout;
                    private int retries;
                    private boolean verbose;
                    public static Config createDefault() {
                        Config c = new Config();
                        c.timeout = 30;
                        c.retries = 3;
                        c.verbose = false;
                        return c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Config", "createDefault"));
    }

    @Test
    @DisplayName("Copy constructor pattern")
    void copyConstructorLike() throws IOException {
        String source = """
                public class Point {
                    private int x;
                    private int y;
                    public Point copy() {
                        Point p = new Point();
                        p.x = this.x;
                        p.y = this.y;
                        return p;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Point", "copy"));
    }

    // =========================================================================
    // Iterator-like patterns
    // =========================================================================

    @Test
    @DisplayName("Manual iterator: hasNext checks index < size")
    void iteratorHasNext() throws IOException {
        String source = """
                public class ArrayIterator {
                    private int[] data;
                    private int index;
                    private int size;
                    public boolean hasNext() {
                        return index < size;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayIterator", "hasNext"));
    }

    @Test
    @DisplayName("Manual iterator: next returns element and advances")
    void iteratorNext() throws IOException {
        String source = """
                public class ArrayIterator2 {
                    private int[] data;
                    private int index;
                    private int size;
                    public int next() {
                        if (index >= size) throw new IllegalStateException();
                        int value = data[index];
                        index++;
                        return value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayIterator2", "next"));
    }

    @Test
    @DisplayName("Cursor: skip n elements")
    void cursorSkip() throws IOException {
        String source = """
                public class Cursor {
                    private int position;
                    private int limit;
                    public void skip(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        int newPos = position + n;
                        if (newPos > limit) {
                            position = limit;
                        } else {
                            position = newPos;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Cursor", "skip"));
    }

    @Test
    @DisplayName("Cursor: remaining elements count")
    void cursorRemaining() throws IOException {
        String source = """
                public class Cursor2 {
                    private int position;
                    private int limit;
                    public int remaining() {
                        return limit - position;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Cursor2", "remaining"));
    }

    // =========================================================================
    // Observable / event patterns
    // =========================================================================

    @Test
    @DisplayName("Counter with listener notification via field")
    void counterWithNotification() throws IOException {
        String source = """
                public class ObservableCounter {
                    private int count;
                    private int lastNotifiedValue;
                    public void increment() {
                        count++;
                        lastNotifiedValue = count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ObservableCounter", "increment"));
    }

    @Test
    @DisplayName("Event counter: record event and update stats")
    void eventCounter() throws IOException {
        String source = """
                public class EventStats {
                    private int totalEvents;
                    private int maxValue;
                    public void recordEvent(int value) {
                        totalEvents++;
                        if (value > maxValue) {
                            maxValue = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "EventStats", "recordEvent"));
    }

    // =========================================================================
    // Strategy / computation patterns
    // =========================================================================

    @Test
    @DisplayName("Dispatch compute based on operation code")
    void computeDispatch() throws IOException {
        String source = """
                public class Calculator {
                    public int compute(int a, int b, int op) {
                        if (op == 0) return a + b;
                        if (op == 1) return a - b;
                        if (op == 2) return a * b;
                        if (op == 3) {
                            if (b == 0) throw new ArithmeticException();
                            return a / b;
                        }
                        throw new IllegalArgumentException();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Calculator", "compute"));
    }

    @Test
    @DisplayName("Apply function: scale all elements")
    void scaleArray() throws IOException {
        String source = """
                public class ArrayOps {
                    public void scale(int[] arr, int factor) {
                        if (arr == null) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            arr[i] *= factor;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayOps", "scale"));
    }

    @Test
    @DisplayName("Apply function: clamp all elements to range")
    void clampArray() throws IOException {
        String source = """
                public class ArrayOps2 {
                    public void clampAll(int[] arr, int min, int max) {
                        if (arr == null) throw new IllegalArgumentException();
                        if (min > max) throw new IllegalArgumentException();
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < min) arr[i] = min;
                            else if (arr[i] > max) arr[i] = max;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ArrayOps2", "clampAll"));
    }

    // =========================================================================
    // Fluent API / chaining patterns
    // =========================================================================

    @Test
    @DisplayName("Fluent: add to accumulator returns this")
    void fluentAdd() throws IOException {
        String source = """
                public class Accumulator {
                    private int total;
                    public Accumulator add(int value) {
                        total += value;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Accumulator", "add"));
    }

    @Test
    @DisplayName("Fluent: reset and return this")
    void fluentReset() throws IOException {
        String source = """
                public class Accumulator2 {
                    private int total;
                    public Accumulator2 reset() {
                        total = 0;
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Accumulator2", "reset"));
    }

    @Test
    @DisplayName("Fluent: conditional multiply")
    void fluentConditionalMultiply() throws IOException {
        String source = """
                public class Accumulator3 {
                    private int total;
                    public Accumulator3 multiplyIf(int factor, boolean condition) {
                        if (condition) {
                            total *= factor;
                        }
                        return this;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Accumulator3", "multiplyIf"));
    }

    // =========================================================================
    // Immutable value objects
    // =========================================================================

    @Test
    @DisplayName("Immutable: translate point returns new object")
    void translatePoint() throws IOException {
        String source = """
                public class ImmutablePoint {
                    private final int x;
                    private final int y;
                    public ImmutablePoint(int x, int y) { this.x = x; this.y = y; }
                    public int getX() { return x; }
                    public int getY() { return y; }
                    public int distFromOrigin() {
                        return x * x + y * y;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ImmutablePoint", "distFromOrigin"));
    }

    @Test
    @DisplayName("Immutable: negate value")
    void negateValue() throws IOException {
        String source = """
                public class Amount {
                    private final int value;
                    public Amount(int value) { this.value = value; }
                    public int getValue() { return value; }
                    public int negated() {
                        return -value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Amount", "negated"));
    }

    // =========================================================================
    // Pooling / resource management
    // =========================================================================

    @Test
    @DisplayName("Pool: acquire decrements available count")
    void poolAcquire() throws IOException {
        String source = """
                public class ResourcePool {
                    private int available;
                    public boolean acquire() {
                        if (available <= 0) return false;
                        available--;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ResourcePool", "acquire"));
    }

    @Test
    @DisplayName("Pool: release increments available count")
    void poolRelease() throws IOException {
        String source = """
                public class ResourcePool2 {
                    private int available;
                    private int maxSize;
                    public boolean release() {
                        if (available >= maxSize) return false;
                        available++;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ResourcePool2", "release"));
    }

    @Test
    @DisplayName("Rate limiter: check and decrement tokens")
    void rateLimiter() throws IOException {
        String source = """
                public class RateLimiter {
                    private int tokens;
                    public boolean tryAcquire() {
                        if (tokens <= 0) return false;
                        tokens--;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RateLimiter", "tryAcquire"));
    }
}
