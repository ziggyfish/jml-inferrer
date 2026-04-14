package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for real-world-like patterns: configuration objects,
 * validators, parsers, encoders, state machines, and business logic.
 */
class RealWorldPatternVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Configuration / settings
    // =========================================================================

    @Test
    @DisplayName("Config: set timeout with range validation")
    void configSetTimeout() throws IOException {
        String source = """
                public class AppConfig {
                    private int timeout;
                    private int maxRetries;
                    public void setTimeout(int millis) {
                        if (millis < 100) throw new IllegalArgumentException();
                        if (millis > 60000) throw new IllegalArgumentException();
                        this.timeout = millis;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AppConfig", "setTimeout"));
    }

    @Test
    @DisplayName("Config: set retries with bounds")
    void configSetRetries() throws IOException {
        String source = """
                public class AppConfig2 {
                    private int maxRetries;
                    public void setMaxRetries(int retries) {
                        if (retries < 0 || retries > 10) throw new IllegalArgumentException();
                        this.maxRetries = retries;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AppConfig2", "setMaxRetries"));
    }

    // =========================================================================
    // Validators
    // =========================================================================

    @Test
    @DisplayName("Validator: email basic structure check")
    void validateEmailBasic() throws IOException {
        String source = """
                public class Validator1 {
                    public boolean isValidEmail(String email) {
                        if (email == null) return false;
                        int atIndex = email.indexOf('@');
                        if (atIndex <= 0) return false;
                        int dotIndex = email.lastIndexOf('.');
                        if (dotIndex <= atIndex + 1) return false;
                        if (dotIndex >= email.length() - 1) return false;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Validator1", "isValidEmail"));
    }

    @Test
    @DisplayName("Validator: password strength check")
    void validatePasswordStrength() throws IOException {
        String source = """
                public class Validator2 {
                    public boolean isStrongPassword(String password) {
                        if (password == null) return false;
                        if (password.length() < 8) return false;
                        boolean hasUpper = false;
                        boolean hasLower = false;
                        boolean hasDigit = false;
                        for (int i = 0; i < password.length(); i++) {
                            char c = password.charAt(i);
                            if (Character.isUpperCase(c)) hasUpper = true;
                            if (Character.isLowerCase(c)) hasLower = true;
                            if (Character.isDigit(c)) hasDigit = true;
                        }
                        return hasUpper && hasLower && hasDigit;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Validator2", "isStrongPassword"));
    }

    @Test
    @DisplayName("Validator: IP address octets")
    void validateIPOctets() throws IOException {
        String source = """
                public class Validator3 {
                    public boolean isValidOctet(int value) {
                        return value >= 0 && value <= 255;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Validator3", "isValidOctet"));
    }

    @Test
    @DisplayName("Validator: credit card Luhn checksum")
    void luhnCheck() throws IOException {
        String source = """
                public class Validator4 {
                    public boolean luhnCheck(int[] digits) {
                        if (digits == null || digits.length == 0) throw new IllegalArgumentException();
                        int sum = 0;
                        boolean alternate = false;
                        for (int i = digits.length - 1; i >= 0; i--) {
                            int d = digits[i];
                            if (alternate) {
                                d *= 2;
                                if (d > 9) d -= 9;
                            }
                            sum += d;
                            alternate = !alternate;
                        }
                        return sum % 10 == 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Validator4", "luhnCheck"));
    }

    // =========================================================================
    // Encoders / decoders
    // =========================================================================

    @Test
    @DisplayName("Encoder: run-length encode count")
    void runLengthCount() throws IOException {
        String source = """
                public class Encoder1 {
                    public int countRuns(int[] data) {
                        if (data == null || data.length == 0) throw new IllegalArgumentException();
                        int runs = 1;
                        for (int i = 1; i < data.length; i++) {
                            if (data[i] != data[i - 1]) runs++;
                        }
                        return runs;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Encoder1", "countRuns"));
    }

    @Test
    @DisplayName("Encoder: hex digit to int")
    void hexDigitToInt() throws IOException {
        String source = """
                public class Encoder2 {
                    public int hexToInt(char c) {
                        if (c >= '0' && c <= '9') return c - '0';
                        if (c >= 'a' && c <= 'f') return c - 'a' + 10;
                        if (c >= 'A' && c <= 'F') return c - 'A' + 10;
                        throw new IllegalArgumentException();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Encoder2", "hexToInt"));
    }

    @Test
    @DisplayName("Encoder: int to hex char")
    void intToHexChar() throws IOException {
        String source = """
                public class Encoder3 {
                    public char intToHex(int value) {
                        if (value < 0 || value > 15) throw new IllegalArgumentException();
                        if (value < 10) return (char) ('0' + value);
                        return (char) ('a' + value - 10);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Encoder3", "intToHex"));
    }

    @Test
    @DisplayName("Encoder: Caesar cipher shift")
    void caesarCipher() throws IOException {
        String source = """
                public class Encoder4 {
                    public char shiftChar(char c, int shift) {
                        if (c >= 'a' && c <= 'z') {
                            return (char) ('a' + (c - 'a' + shift) % 26);
                        }
                        if (c >= 'A' && c <= 'Z') {
                            return (char) ('A' + (c - 'A' + shift) % 26);
                        }
                        return c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Encoder4", "shiftChar"));
    }

    // =========================================================================
    // Business logic patterns
    // =========================================================================

    @Test
    @DisplayName("Business: calculate tax based on income brackets")
    void calculateTax() throws IOException {
        String source = """
                public class TaxCalc {
                    public double calculateTax(double income) {
                        if (income < 0) throw new IllegalArgumentException();
                        if (income <= 10000) return income * 0.10;
                        if (income <= 40000) return 1000 + (income - 10000) * 0.20;
                        return 7000 + (income - 40000) * 0.30;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TaxCalc", "calculateTax"));
    }

    @Test
    @DisplayName("Business: shipping cost by weight tiers")
    void shippingCost() throws IOException {
        String source = """
                public class Shipping {
                    public double calculateShipping(double weight) {
                        if (weight <= 0) throw new IllegalArgumentException();
                        if (weight <= 1.0) return 5.0;
                        if (weight <= 5.0) return 10.0;
                        if (weight <= 20.0) return 20.0;
                        return 20.0 + (weight - 20.0) * 1.5;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Shipping", "calculateShipping"));
    }

    @Test
    @DisplayName("Business: apply bulk discount")
    void bulkDiscount() throws IOException {
        String source = """
                public class Pricing {
                    public double pricePerUnit(int quantity, double basePrice) {
                        if (quantity <= 0) throw new IllegalArgumentException();
                        if (basePrice < 0) throw new IllegalArgumentException();
                        if (quantity >= 100) return basePrice * 0.7;
                        if (quantity >= 50) return basePrice * 0.8;
                        if (quantity >= 10) return basePrice * 0.9;
                        return basePrice;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Pricing", "pricePerUnit"));
    }

    @Test
    @DisplayName("Business: inventory check and reserve")
    void inventoryReserve() throws IOException {
        String source = """
                public class Inventory {
                    private int stock;
                    private int reserved;
                    public boolean reserve(int quantity) {
                        if (quantity <= 0) throw new IllegalArgumentException();
                        int available = stock - reserved;
                        if (quantity > available) return false;
                        reserved += quantity;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Inventory", "reserve"));
    }

    // =========================================================================
    // Coordinate systems and geometry
    // =========================================================================

    @Test
    @DisplayName("Geometry: point inside rectangle check")
    void pointInsideRect() throws IOException {
        String source = """
                public class Geometry1 {
                    public boolean isInside(int px, int py, int rx, int ry, int rw, int rh) {
                        return px >= rx && px <= rx + rw && py >= ry && py <= ry + rh;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Geometry1", "isInside"));
    }

    @Test
    @DisplayName("Geometry: compute midpoint of two points")
    void midpoint() throws IOException {
        String source = """
                public class Geometry2 {
                    private int x;
                    private int y;
                    public void setToMidpoint(int x1, int y1, int x2, int y2) {
                        this.x = (x1 + x2) / 2;
                        this.y = (y1 + y2) / 2;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Geometry2", "setToMidpoint"));
    }

    @Test
    @DisplayName("Geometry: rectangle overlap check")
    void rectOverlap() throws IOException {
        String source = """
                public class Geometry3 {
                    public boolean overlaps(int x1, int y1, int w1, int h1,
                                           int x2, int y2, int w2, int h2) {
                        if (x1 + w1 <= x2) return false;
                        if (x2 + w2 <= x1) return false;
                        if (y1 + h1 <= y2) return false;
                        if (y2 + h2 <= y1) return false;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Geometry3", "overlaps"));
    }

    // =========================================================================
    // State machine / lifecycle
    // =========================================================================

    @Test
    @DisplayName("Lifecycle: open -> read -> close")
    void lifecycleOpenClose() throws IOException {
        String source = """
                public class Resource {
                    private boolean open;
                    private int readCount;
                    public void open() {
                        if (open) throw new IllegalStateException();
                        open = true;
                        readCount = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Resource", "open"));
    }

    @Test
    @DisplayName("Lifecycle: read requires open state")
    void lifecycleRead() throws IOException {
        String source = """
                public class Resource2 {
                    private boolean open;
                    private int readCount;
                    public int read(int[] buffer, int offset) {
                        if (!open) throw new IllegalStateException();
                        if (buffer == null) throw new IllegalArgumentException();
                        if (offset < 0 || offset >= buffer.length) throw new IndexOutOfBoundsException();
                        readCount++;
                        return buffer[offset];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Resource2", "read"));
    }

    @Test
    @DisplayName("Lifecycle: close sets state to closed")
    void lifecycleClose() throws IOException {
        String source = """
                public class Resource3 {
                    private boolean open;
                    public void close() {
                        open = false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Resource3", "close"));
    }

    // =========================================================================
    // Caching / memoization
    // =========================================================================

    @Test
    @DisplayName("Cache: get or compute pattern")
    void cacheGetOrCompute() throws IOException {
        String source = """
                public class Cache1 {
                    private int cachedValue;
                    private boolean cached;
                    public int getOrCompute(int input) {
                        if (cached) return cachedValue;
                        cachedValue = input * input + input;
                        cached = true;
                        return cachedValue;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Cache1", "getOrCompute"));
    }

    @Test
    @DisplayName("Cache: invalidate cache")
    void cacheInvalidate() throws IOException {
        String source = """
                public class Cache2 {
                    private int cachedValue;
                    private boolean cached;
                    public void invalidate() {
                        cached = false;
                        cachedValue = 0;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Cache2", "invalidate"));
    }

    // =========================================================================
    // Retry / attempt patterns
    // =========================================================================

    @Test
    @DisplayName("Retry: attempt counter with limit")
    void retryCounter() throws IOException {
        String source = """
                public class Retry1 {
                    private int attempts;
                    private int maxAttempts;
                    public boolean canRetry() {
                        return attempts < maxAttempts;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Retry1", "canRetry"));
    }

    @Test
    @DisplayName("Retry: record attempt and check exhaustion")
    void retryRecordAttempt() throws IOException {
        String source = """
                public class Retry2 {
                    private int attempts;
                    private int maxAttempts;
                    public boolean recordAttempt() {
                        attempts++;
                        return attempts < maxAttempts;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Retry2", "recordAttempt"));
    }
}
