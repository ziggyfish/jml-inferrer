package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for postcondition inference: return types, values, string ops, collections, patterns.
 */
@DisplayName("Postcondition Inference")
class PostconditionInferenceTest extends InferrerTestBase {

    // ---- Non-null returns ----

    @Test
    @DisplayName("Non-null return type when never returning null")
    void nonNullReturn() {
        MethodSpecification spec = infer("""
            class T {
                String greet(String name) {
                    return "Hello " + name;
                }
            }
            """, "greet");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null");
    }

    @Test
    @DisplayName("Method that sometimes returns null -> no non-null guarantee")
    void sometimesNull() {
        MethodSpecification spec = infer("""
            class T {
                String maybe(boolean flag) {
                    if (flag) return "yes";
                    return null;
                }
            }
            """, "maybe");
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.equals("\\result != null")),
                "Should not guarantee non-null when null is possible");
    }

    // ---- Numeric results ----

    @Test
    @DisplayName("Result >= 0 for abs")
    void resultNonNegativeAbs() {
        MethodSpecification spec = infer("""
            class T {
                int absVal(int x) {
                    return Math.abs(x);
                }
            }
            """, "absVal");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "Expected \\result >= 0");
    }

    @Test
    @DisplayName("Self-multiplication: x * x is non-negative")
    void selfMultiplication() {
        MethodSpecification spec = infer("""
            class T {
                int square(int x) {
                    return x * x;
                }
            }
            """, "square");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "Expected \\result >= 0 for x*x");
    }

    @Test
    @DisplayName("Return a + b generates result == a + b")
    void paramAdditionReturn() {
        MethodSpecification spec = infer("""
            class T {
                int add(int a, int b) {
                    return a + b;
                }
            }
            """, "add");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == a + b")),
                "Expected \\result == a + b");
    }

    @Test
    @DisplayName("Return a * b generates result == a * b")
    void paramMultiplication() {
        MethodSpecification spec = infer("""
            class T {
                int multiply(int a, int b) {
                    return a * b;
                }
            }
            """, "multiply");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == a * b")),
                "Expected \\result == a * b");
    }

    @Test
    @DisplayName("Return a - b generates result == a - b")
    void paramSubtraction() {
        MethodSpecification spec = infer("""
            class T {
                int subtract(int a, int b) {
                    return a - b;
                }
            }
            """, "subtract");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == a - b")),
                "Expected \\result == a - b");
    }

    @Test
    @DisplayName("Return a / b generates result == a / b")
    void paramDivision() {
        MethodSpecification spec = infer("""
            class T {
                int divide(int a, int b) {
                    return a / b;
                }
            }
            """, "divide");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == a / b")),
                "Expected \\result == a / b");
    }

    @Test
    @DisplayName("param + positive literal -> result > param")
    void paramPlusLiteral() {
        MethodSpecification spec = infer("""
            class T {
                int increment(int n) {
                    return n + 5;
                }
            }
            """, "increment");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result > n")),
                "Expected \\result > n");
    }

    @Test
    @DisplayName("All returns are positive literals -> result >= 1")
    void allPositiveLiterals() {
        MethodSpecification spec = infer("""
            class T {
                int classify(int x) {
                    if (x > 0) return 2;
                    return 3;
                }
            }
            """, "classify");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result >= 1") || p.contains("\\result > 0")),
                "Expected positive return bound");
    }

    // ---- Conditional returns ----

    @Test
    @DisplayName("Conditional returns with literals -> disjunctive postcondition")
    void conditionalLiteralReturns() {
        MethodSpecification spec = infer("""
            class T {
                int sign(int x) {
                    if (x > 0) {
                        return 1;
                    } else {
                        return -1;
                    }
                }
            }
            """, "sign");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == 1 || \\result == -1")),
                "Expected disjunctive postcondition");
    }

    @Test
    @DisplayName("Null check conditional return")
    void nullCheckConditionalReturn() {
        MethodSpecification spec = infer("""
            class T {
                String safe(String s) {
                    if (s == null) {
                        return "default";
                    } else {
                        return s.toUpperCase();
                    }
                }
            }
            """, "safe");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected \\result != null");
    }

    @Test
    @DisplayName("Ternary with null check")
    void ternaryNullCheck() {
        MethodSpecification spec = infer("""
            class T {
                String upper(String s) {
                    return s != null ? s.toUpperCase() : null;
                }
            }
            """, "upper");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("s != null ==> \\result != null")),
                "Expected conditional non-null");
    }

    // ---- Builder pattern ----

    @Test
    @DisplayName("Builder pattern: returns this")
    void builderReturnsThis() {
        MethodSpecification spec = infer("""
            class Builder {
                private int value;
                Builder setValue(int v) {
                    this.value = v;
                    return this;
                }
            }
            """, "setValue");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == this")),
                "Expected \\result == this");
    }

    // ---- String return analysis ----

    @Test
    @DisplayName("toUpperCase preserves length")
    void toUpperCaseLength() {
        MethodSpecification spec = infer("""
            class T {
                String upper(String s) {
                    return s.toUpperCase();
                }
            }
            """, "upper");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() == s.length()")),
                "Expected length preservation");
    }

    @Test
    @DisplayName("toLowerCase preserves length")
    void toLowerCaseLength() {
        MethodSpecification spec = infer("""
            class T {
                String lower(String s) {
                    return s.toLowerCase();
                }
            }
            """, "lower");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() == s.length()")),
                "Expected length preservation");
    }

    @Test
    @DisplayName("trim: result length <= original")
    void trimLength() {
        MethodSpecification spec = infer("""
            class T {
                String cleaned(String s) {
                    return s.trim();
                }
            }
            """, "cleaned");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() <= s.length()")),
                "Expected trim constraint");
    }

    @Test
    @DisplayName("substring with literal indices")
    void substringLiteral() {
        MethodSpecification spec = infer("""
            class T {
                String sub(String s) {
                    return s.substring(1, 4);
                }
            }
            """, "sub");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() == 3")),
                "Expected length == 3");
    }

    @Test
    @DisplayName("concat with literal")
    void concatLiteral() {
        MethodSpecification spec = infer("""
            class T {
                String append(String s) {
                    return s.concat("xyz");
                }
            }
            """, "append");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() == s.length() + 3")),
                "Expected concat length");
    }

    @Test
    @DisplayName("String + operator concatenation")
    void stringPlusOperator() {
        MethodSpecification spec = infer("""
            class T {
                String combine(String a, String b) {
                    return a + b;
                }
            }
            """, "combine");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("a.length() + b.length()")),
                "Expected length sum");
    }

    @Test
    @DisplayName("repeat method postcondition")
    void stringRepeat() {
        MethodSpecification spec = infer("""
            class T {
                String rep(String s) {
                    return s.repeat(3);
                }
            }
            """, "rep");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() == s.length() * 3")),
                "Expected repeat length");
    }

    @Test
    @DisplayName("String literal return: known length")
    void stringLiteralReturn() {
        MethodSpecification spec = infer("""
            class T {
                String hello() {
                    return "hello";
                }
            }
            """, "hello");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() == 5")),
                "Expected length == 5");
    }

    @Test
    @DisplayName("Empty string literal return")
    void emptyStringReturn() {
        MethodSpecification spec = infer("""
            class T {
                String empty() {
                    return "";
                }
            }
            """, "empty");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result.isEmpty()")),
                "Expected isEmpty()");
    }

    @Test
    @DisplayName("strip method: length <= original")
    void stripLength() {
        MethodSpecification spec = infer("""
            class T {
                String cleaned(String s) {
                    return s.strip();
                }
            }
            """, "cleaned");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.length() <= s.length()")),
                "Expected strip constraint");
    }

    @Test
    @DisplayName("intern method: equals original")
    void internEquals() {
        MethodSpecification spec = infer("""
            class T {
                String interned(String s) {
                    return s.intern();
                }
            }
            """, "interned");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result.equals(s)")),
                "Expected equals constraint for intern");
    }

    // ---- Collection returns ----

    @Test
    @DisplayName("New ArrayList return -> non-null")
    void newArrayListReturn() {
        MethodSpecification spec = infer("""
            import java.util.ArrayList;
            import java.util.List;
            class T {
                List<String> create() {
                    return new ArrayList<>();
                }
            }
            """, "create");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null");
    }

    @Test
    @DisplayName("Array creation with param size -> length == param")
    void arrayCreationParamSize() {
        MethodSpecification spec = infer("""
            class T {
                int[] create(int n) {
                    return new int[n];
                }
            }
            """, "create");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result.length == n")),
                "Expected length == n");
    }

    // ---- Getter pattern ----

    @Test
    @DisplayName("Getter returns field via this.field")
    void getterReturnsField() {
        MethodSpecification spec = infer("""
            class T {
                private int name;
                int getName() {
                    return this.name;
                }
            }
            """, "getName");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == this.name")),
                "Expected getter postcondition");
    }

    // ---- Factory pattern ----

    @Test
    @DisplayName("Factory method returning new instance")
    void factoryMethod() {
        MethodSpecification spec = infer("""
            class Widget {
                static Widget create() {
                    return new Widget();
                }
            }
            """, "create");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result != null")),
                "Expected non-null from factory");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result instanceof Widget")),
                "Expected instanceof Widget");
    }

    // ---- Comparison patterns ----

    @Test
    @DisplayName("equals method -> reflexive property")
    void equalsReflexive() {
        MethodSpecification spec = infer("""
            class T {
                private int value;
                public boolean equals(Object obj) {
                    if (obj == null) return false;
                    return this.value == ((T) obj).value;
                }
            }
            """, "equals");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("equals")),
                "Expected reflexive equals postcondition");
    }

    // ---- Field modifications ----

    @Test
    @DisplayName("Field increment: this.count++")
    void fieldIncrement() {
        MethodSpecification spec = infer("""
            class Counter {
                private int count;
                void increment() {
                    this.count++;
                }
            }
            """, "increment");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("this.count == \\old(this.count) + 1")),
                "Expected increment postcondition");
    }

    @Test
    @DisplayName("Field decrement: this.count--")
    void fieldDecrement() {
        MethodSpecification spec = infer("""
            class Counter {
                private int count;
                void decrement() {
                    this.count--;
                }
            }
            """, "decrement");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("this.count == \\old(this.count) - 1")),
                "Expected decrement postcondition");
    }

    @Test
    @DisplayName("Field assignment to parameter")
    void fieldAssignParam() {
        MethodSpecification spec = infer("""
            class T {
                private int value;
                void setValue(int v) {
                    this.value = v;
                }
            }
            """, "setValue");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("this.value == v")),
                "Expected this.value == v");
    }

    @Test
    @DisplayName("Field compound: this.balance += amount")
    void fieldCompoundAdd() {
        MethodSpecification spec = infer("""
            class Account {
                private int balance;
                void deposit(int amount) {
                    this.balance += amount;
                }
            }
            """, "deposit");
        assertTrue(anyContainsAll(spec.getPostconditions(), "this.balance", "\\old(this.balance)", "+ amount"),
                "Expected compound assignment postcondition");
    }

    // ---- Parameter modifications ----

    @Test
    @DisplayName("Collection add -> size increase")
    void collectionAdd() {
        MethodSpecification spec = infer("""
            import java.util.List;
            class T {
                void addItem(List<String> items, String item) {
                    items.add(item);
                }
            }
            """, "addItem");
        assertTrue(anyContainsAll(spec.getPostconditions(), "items.size()", "\\old"),
                "Expected size postcondition");
    }

    @Test
    @DisplayName("Collection clear -> isEmpty")
    void collectionClear() {
        MethodSpecification spec = infer("""
            import java.util.List;
            class T {
                void clearAll(List<String> items) {
                    items.clear();
                }
            }
            """, "clearAll");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("items.isEmpty()")),
                "Expected isEmpty postcondition");
    }

    @Test
    @DisplayName("Array element write -> array is modified")
    void arrayModification() {
        MethodSpecification spec = infer("""
            class T {
                void setFirst(int[] arr, int val) {
                    arr[0] = val;
                }
            }
            """, "setFirst");
        assertTrue(anyContainsAll(spec.getPostconditions(), "arr", "modified"),
                "Expected array modified postcondition");
    }

    // ---- Exception guarantees ----

    @Test
    @DisplayName("throws IOException -> may throw postcondition")
    void throwsDeclaration() {
        MethodSpecification spec = infer("""
            class T {
                void read() throws java.io.IOException {
                }
            }
            """, "read");
        assertTrue(anyContainsAll(spec.getPostconditions(), "may throw", "IOException"),
                "Expected throws postcondition");
    }

    // ---- Resolved local variable in return ----

    @Test
    @DisplayName("Return local assigned from param binary expr")
    void resolvedLocalBinaryReturn() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int result = a + b;
                    return result;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == a + b")),
                "Expected resolved return expression");
    }
}
