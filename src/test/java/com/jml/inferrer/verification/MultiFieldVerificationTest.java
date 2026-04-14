package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for methods that read/write multiple fields,
 * maintain invariants across fields, and coordinate field updates.
 */
class MultiFieldVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Coordinate / geometry updates
    // =========================================================================

    @Test
    @DisplayName("Move point by delta x and delta y")
    void movePointByDelta() throws IOException {
        String source = """
                public class Point2D {
                    private int x;
                    private int y;
                    public void translate(int dx, int dy) {
                        x += dx;
                        y += dy;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Point2D", "translate"));
    }

    @Test
    @DisplayName("Scale point coordinates by factor")
    void scalePoint() throws IOException {
        String source = """
                public class Point2D2 {
                    private int x;
                    private int y;
                    public void scale(int factor) {
                        x *= factor;
                        y *= factor;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Point2D2", "scale"));
    }

    @Test
    @DisplayName("Set rectangle dimensions with validation")
    void setRectDimensions() throws IOException {
        String source = """
                public class Rectangle {
                    private int width;
                    private int height;
                    public void setDimensions(int w, int h) {
                        if (w < 0 || h < 0) throw new IllegalArgumentException();
                        this.width = w;
                        this.height = h;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Rectangle", "setDimensions"));
    }

    @Test
    @DisplayName("Compute area from width and height fields")
    void computeArea() throws IOException {
        String source = """
                public class Rectangle2 {
                    private int width;
                    private int height;
                    public int area() {
                        return width * height;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Rectangle2", "area"));
    }

    @Test
    @DisplayName("Compute perimeter from width and height")
    void computePerimeter() throws IOException {
        String source = """
                public class Rectangle3 {
                    private int width;
                    private int height;
                    public int perimeter() {
                        return 2 * (width + height);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Rectangle3", "perimeter"));
    }

    // =========================================================================
    // Range / interval updates
    // =========================================================================

    @Test
    @DisplayName("Set range with min <= max invariant")
    void setRange() throws IOException {
        String source = """
                public class Range {
                    private int min;
                    private int max;
                    public void setRange(int min, int max) {
                        if (min > max) throw new IllegalArgumentException();
                        this.min = min;
                        this.max = max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Range", "setRange"));
    }

    @Test
    @DisplayName("Expand range to include a value")
    void expandRange() throws IOException {
        String source = """
                public class Range2 {
                    private int min;
                    private int max;
                    public void include(int value) {
                        if (value < min) min = value;
                        if (value > max) max = value;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Range2", "include"));
    }

    @Test
    @DisplayName("Range: contains check")
    void rangeContains() throws IOException {
        String source = """
                public class Range3 {
                    private int min;
                    private int max;
                    public boolean contains(int value) {
                        return value >= min && value <= max;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Range3", "contains"));
    }

    @Test
    @DisplayName("Range: compute span")
    void rangeSpan() throws IOException {
        String source = """
                public class Range4 {
                    private int min;
                    private int max;
                    public int span() {
                        return max - min;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Range4", "span"));
    }

    // =========================================================================
    // Financial / ledger patterns
    // =========================================================================

    @Test
    @DisplayName("Account: deposit updates balance and transaction count")
    void accountDeposit() throws IOException {
        String source = """
                public class Account {
                    private int balance;
                    private int transactionCount;
                    public void deposit(int amount) {
                        if (amount <= 0) throw new IllegalArgumentException();
                        balance += amount;
                        transactionCount++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Account", "deposit"));
    }

    @Test
    @DisplayName("Account: withdraw with balance check")
    void accountWithdraw() throws IOException {
        String source = """
                public class Account2 {
                    private int balance;
                    private int transactionCount;
                    public void withdraw(int amount) {
                        if (amount <= 0) throw new IllegalArgumentException();
                        if (amount > balance) throw new IllegalStateException();
                        balance -= amount;
                        transactionCount++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Account2", "withdraw"));
    }

    @Test
    @DisplayName("Account: transfer between balance and savings")
    void accountTransfer() throws IOException {
        String source = """
                public class Account3 {
                    private int balance;
                    private int savings;
                    public void transferToSavings(int amount) {
                        if (amount <= 0) throw new IllegalArgumentException();
                        if (amount > balance) throw new IllegalStateException();
                        balance -= amount;
                        savings += amount;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Account3", "transferToSavings"));
    }

    // =========================================================================
    // Statistics / running computations
    // =========================================================================

    @Test
    @DisplayName("Running stats: add value updates sum and count")
    void runningStatsAdd() throws IOException {
        String source = """
                public class RunningStats {
                    private double sum;
                    private int count;
                    public void add(double value) {
                        sum += value;
                        count++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RunningStats", "add"));
    }

    @Test
    @DisplayName("Running stats: compute mean from sum and count")
    void runningStatsMean() throws IOException {
        String source = """
                public class RunningStats2 {
                    private double sum;
                    private int count;
                    public double mean() {
                        if (count == 0) throw new ArithmeticException();
                        return sum / count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "RunningStats2", "mean"));
    }

    @Test
    @DisplayName("Running min/max: update both on each new value")
    void runningMinMax() throws IOException {
        String source = """
                public class MinMaxTracker {
                    private int min;
                    private int max;
                    private boolean initialized;
                    public void observe(int value) {
                        if (!initialized) {
                            min = value;
                            max = value;
                            initialized = true;
                        } else {
                            if (value < min) min = value;
                            if (value > max) max = value;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MinMaxTracker", "observe"));
    }

    // =========================================================================
    // Timer / counter coordination
    // =========================================================================

    @Test
    @DisplayName("Timer: tick advances elapsed, checks deadline")
    void timerTick() throws IOException {
        String source = """
                public class Timer {
                    private int elapsed;
                    private int deadline;
                    private boolean expired;
                    public void tick(int delta) {
                        if (delta < 0) throw new IllegalArgumentException();
                        elapsed += delta;
                        if (elapsed >= deadline) {
                            expired = true;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Timer", "tick"));
    }

    @Test
    @DisplayName("Timer: reset clears all state")
    void timerReset() throws IOException {
        String source = """
                public class Timer2 {
                    private int elapsed;
                    private boolean expired;
                    public void reset() {
                        elapsed = 0;
                        expired = false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Timer2", "reset"));
    }

    @Test
    @DisplayName("Countdown: decrement and check if done")
    void countdown() throws IOException {
        String source = """
                public class Countdown {
                    private int remaining;
                    private boolean done;
                    public void tick() {
                        if (remaining > 0) {
                            remaining--;
                            if (remaining == 0) {
                                done = true;
                            }
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Countdown", "tick"));
    }

    // =========================================================================
    // Capacity / buffer management
    // =========================================================================

    @Test
    @DisplayName("Buffer: write byte updates position")
    void bufferWriteByte() throws IOException {
        String source = """
                public class ByteBuffer {
                    private byte[] data;
                    private int position;
                    public void writeByte(byte b) {
                        if (position >= data.length) throw new IllegalStateException();
                        data[position] = b;
                        position++;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ByteBuffer", "writeByte"));
    }

    @Test
    @DisplayName("Buffer: clear resets position")
    void bufferClear() throws IOException {
        String source = """
                public class ByteBuffer2 {
                    private int position;
                    private int limit;
                    public void clear() {
                        position = 0;
                        limit = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ByteBuffer2", "clear"));
    }

    @Test
    @DisplayName("Buffer: flip sets limit to position, resets position")
    void bufferFlip() throws IOException {
        String source = """
                public class ByteBuffer3 {
                    private int position;
                    private int limit;
                    public void flip() {
                        limit = position;
                        position = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ByteBuffer3", "flip"));
    }

    // =========================================================================
    // Complex multi-field interactions
    // =========================================================================

    @Test
    @DisplayName("Swap two fields atomically")
    void swapFields() throws IOException {
        String source = """
                public class FieldSwap {
                    private int a;
                    private int b;
                    public void swap() {
                        int temp = a;
                        a = b;
                        b = temp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldSwap", "swap"));
    }

    @Test
    @DisplayName("Rotate three fields: a->b, b->c, c->a")
    void rotateThreeFields() throws IOException {
        String source = """
                public class FieldRotate {
                    private int a;
                    private int b;
                    private int c;
                    public void rotate() {
                        int temp = a;
                        a = b;
                        b = c;
                        c = temp;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "FieldRotate", "rotate"));
    }

    @Test
    @DisplayName("Normalize: ensure x <= y by swapping if needed")
    void normalizeOrder() throws IOException {
        String source = """
                public class OrderedPair {
                    private int x;
                    private int y;
                    public void normalize() {
                        if (x > y) {
                            int temp = x;
                            x = y;
                            y = temp;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "OrderedPair", "normalize"));
    }
}
