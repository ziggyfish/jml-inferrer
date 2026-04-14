package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for string operations: length constraints, transformations,
 * concatenation, substring, and string-returning methods.
 */
class StringOperationVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // String null checks and basic operations
    // =========================================================================

    @Test
    @DisplayName("String: null guard before length()")
    void stringNullGuardLength() throws IOException {
        String source = """
                public class StrOps1 {
                    public int getLength(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        return s.length();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrOps1", "getLength"));
    }

    @Test
    @DisplayName("String: null guard before charAt()")
    void stringNullGuardCharAt() throws IOException {
        String source = """
                public class StrOps2 {
                    public char firstChar(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        if (s.isEmpty()) throw new IllegalArgumentException();
                        return s.charAt(0);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrOps2", "firstChar"));
    }

    @Test
    @DisplayName("String: null guard before isEmpty()")
    void stringNullGuardIsEmpty() throws IOException {
        String source = """
                public class StrOps3 {
                    public boolean isBlank(String s) {
                        if (s == null) return true;
                        return s.isEmpty();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrOps3", "isBlank"));
    }

    // =========================================================================
    // String transformation methods
    // =========================================================================

    @Test
    @DisplayName("String: toUpperCase preserves length")
    void toUpperCaseLength() throws IOException {
        String source = """
                public class StrTransform1 {
                    public String toUpper(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        return s.toUpperCase();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrTransform1", "toUpper"));
    }

    @Test
    @DisplayName("String: toLowerCase preserves length")
    void toLowerCaseLength() throws IOException {
        String source = """
                public class StrTransform2 {
                    public String toLower(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        return s.toLowerCase();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrTransform2", "toLower"));
    }

    @Test
    @DisplayName("String: trim reduces or keeps length")
    void trimLength() throws IOException {
        String source = """
                public class StrTransform3 {
                    public String trimmed(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        return s.trim();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrTransform3", "trimmed"));
    }

    @Test
    @DisplayName("String: strip reduces or keeps length")
    void stripLength() throws IOException {
        String source = """
                public class StrTransform4 {
                    public String stripped(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        return s.strip();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrTransform4", "stripped"));
    }

    // =========================================================================
    // String concatenation
    // =========================================================================

    @Test
    @DisplayName("String: concat two strings")
    void concatTwoStrings() throws IOException {
        String source = """
                public class StrConcat1 {
                    public String join(String a, String b) {
                        if (a == null || b == null) throw new IllegalArgumentException();
                        return a + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrConcat1", "join"));
    }

    @Test
    @DisplayName("String: concat with separator")
    void concatWithSeparator() throws IOException {
        String source = """
                public class StrConcat2 {
                    public String joinWithSep(String a, String b, String sep) {
                        if (a == null || b == null || sep == null) throw new IllegalArgumentException();
                        return a + sep + b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrConcat2", "joinWithSep"));
    }

    @Test
    @DisplayName("String: prefix a string with constant")
    void prefixString() throws IOException {
        String source = """
                public class StrConcat3 {
                    public String prefix(String s) {
                        if (s == null) throw new IllegalArgumentException();
                        return "PREFIX_" + s;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrConcat3", "prefix"));
    }

    // =========================================================================
    // Substring and slicing
    // =========================================================================

    @Test
    @DisplayName("String: substring with bounds check")
    void substringBounds() throws IOException {
        String source = """
                public class StrSlice1 {
                    public String firstN(String s, int n) {
                        if (s == null) throw new IllegalArgumentException();
                        if (n < 0 || n > s.length()) throw new IndexOutOfBoundsException();
                        return s.substring(0, n);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrSlice1", "firstN"));
    }

    @Test
    @DisplayName("String: last character extraction")
    void lastCharExtraction() throws IOException {
        String source = """
                public class StrSlice2 {
                    public char lastChar(String s) {
                        if (s == null || s.isEmpty()) throw new IllegalArgumentException();
                        return s.charAt(s.length() - 1);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrSlice2", "lastChar"));
    }

    @Test
    @DisplayName("String: extract middle portion")
    void extractMiddle() throws IOException {
        String source = """
                public class StrSlice3 {
                    public String middle(String s, int start, int end) {
                        if (s == null) throw new IllegalArgumentException();
                        if (start < 0 || end > s.length() || start > end) throw new IndexOutOfBoundsException();
                        return s.substring(start, end);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrSlice3", "middle"));
    }

    // =========================================================================
    // String comparison and search
    // =========================================================================

    @Test
    @DisplayName("String: equals comparison")
    void stringEquals() throws IOException {
        String source = """
                public class StrCmp1 {
                    public boolean isHello(String s) {
                        if (s == null) return false;
                        return s.equals("hello");
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrCmp1", "isHello"));
    }

    @Test
    @DisplayName("String: contains check")
    void stringContains() throws IOException {
        String source = """
                public class StrCmp2 {
                    public boolean hasAt(String email) {
                        if (email == null) throw new IllegalArgumentException();
                        return email.contains("@");
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrCmp2", "hasAt"));
    }

    @Test
    @DisplayName("String: startsWith check")
    void stringStartsWith() throws IOException {
        String source = """
                public class StrCmp3 {
                    public boolean isHttps(String url) {
                        if (url == null) throw new IllegalArgumentException();
                        return url.startsWith("https://");
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrCmp3", "isHttps"));
    }

    @Test
    @DisplayName("String: indexOf with result check")
    void stringIndexOf() throws IOException {
        String source = """
                public class StrSearch1 {
                    public int findChar(String s, char c) {
                        if (s == null) throw new IllegalArgumentException();
                        return s.indexOf(c);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrSearch1", "findChar"));
    }

    // =========================================================================
    // String building with loops
    // =========================================================================

    @Test
    @DisplayName("String: repeat character n times")
    void repeatChar() throws IOException {
        String source = """
                public class StrBuild1 {
                    public String repeatChar(char c, int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        StringBuilder sb = new StringBuilder();
                        for (int i = 0; i < n; i++) {
                            sb.append(c);
                        }
                        return sb.toString();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrBuild1", "repeatChar"));
    }

    @Test
    @DisplayName("String: join array elements with delimiter")
    void joinArrayElements() throws IOException {
        String source = """
                public class StrBuild2 {
                    public String join(String[] parts, String delim) {
                        if (parts == null || delim == null) throw new IllegalArgumentException();
                        if (parts.length == 0) return "";
                        StringBuilder sb = new StringBuilder();
                        sb.append(parts[0]);
                        for (int i = 1; i < parts.length; i++) {
                            sb.append(delim);
                            sb.append(parts[i]);
                        }
                        return sb.toString();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrBuild2", "join"));
    }

    // =========================================================================
    // String with field interaction
    // =========================================================================

    @Test
    @DisplayName("String: setter with null validation")
    void stringFieldSetter() throws IOException {
        String source = """
                public class StrField1 {
                    private String name;
                    public void setName(String name) {
                        if (name == null) throw new IllegalArgumentException();
                        this.name = name;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrField1", "setName"));
    }

    @Test
    @DisplayName("String: getter returns field")
    void stringFieldGetter() throws IOException {
        String source = """
                public class StrField2 {
                    private String name;
                    public String getName() {
                        return name;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrField2", "getName"));
    }

    @Test
    @DisplayName("String: append to field")
    void stringFieldAppend() throws IOException {
        String source = """
                public class StrField3 {
                    private String log;
                    public void appendLog(String entry) {
                        if (entry == null) throw new IllegalArgumentException();
                        if (log == null) {
                            log = entry;
                        } else {
                            log = log + "\\n" + entry;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrField3", "appendLog"));
    }

    // =========================================================================
    // String literal returns
    // =========================================================================

    @Test
    @DisplayName("String: return constant based on condition")
    void stringLiteralReturn() throws IOException {
        String source = """
                public class StrLiteral1 {
                    public String boolToString(boolean b) {
                        if (b) return "true";
                        return "false";
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrLiteral1", "boolToString"));
    }

    @Test
    @DisplayName("String: return one of several fixed strings")
    void stringMultipleLiterals() throws IOException {
        String source = """
                public class StrLiteral2 {
                    public String dayType(int day) {
                        if (day < 1 || day > 7) throw new IllegalArgumentException();
                        if (day <= 5) return "weekday";
                        return "weekend";
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrLiteral2", "dayType"));
    }

    @Test
    @DisplayName("String: format number as padded string")
    void stringFormatNumber() throws IOException {
        String source = """
                public class StrFormat1 {
                    public String padLeft(int n, int width) {
                        if (width < 0) throw new IllegalArgumentException();
                        String s = Integer.toString(n);
                        StringBuilder sb = new StringBuilder();
                        for (int i = s.length(); i < width; i++) {
                            sb.append('0');
                        }
                        sb.append(s);
                        return sb.toString();
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StrFormat1", "padLeft"));
    }
}
