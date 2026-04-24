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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   String greet(String name) {
        //       return "Hello " + name;
        //   }
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
        // Expected annotated method after inference:
        //   (no @Ensures for \\result != null -- method can return null)
        //   String maybe(boolean flag) { ... }
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.equals("\\result != null")),
                "Should not guarantee non-null when null is possible");
    }

    // ---- Numeric results ----

    @Test
    @DisplayName("int abs: no \\result >= 0 (Math.abs(Integer.MIN_VALUE) is negative)")
    void intAbsCanOverflow() {
        MethodSpecification spec = infer("""
            class T {
                int absVal(int x) {
                    return Math.abs(x);
                }
            }
            """, "absVal");
        // Math.abs(Integer.MIN_VALUE) returns Integer.MIN_VALUE (negative),
        // so \result >= 0 is unsound for int
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "int abs can overflow; should not infer \\result >= 0, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("double abs: \\result >= 0 is valid (no overflow to negative)")
    void doubleAbsIsNonNegative() {
        MethodSpecification spec = infer("""
            class T {
                double absVal(double x) {
                    return Math.abs(x);
                }
            }
            """, "absVal");
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "double abs is non-negative; expected \\result >= 0, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Self-multiplication: int x * x can overflow, double x * x is non-negative")
    void selfMultiplication() {
        // int x * x can overflow to negative, so \result >= 0 should NOT be inferred
        MethodSpecification spec = infer("""
            class T {
                int square(int x) {
                    return x * x;
                }
            }
            """, "square");
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "int x * x can overflow; should not infer \\result >= 0, got: " + spec.getPostconditions());
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == x * x")),
                "Expected \\result == x * x");

        // double x * x cannot overflow to negative — \result >= 0 is valid
        MethodSpecification specDouble = infer("""
            class T {
                double square(double x) {
                    return x * x;
                }
            }
            """, "square");
        assertTrue(specDouble.getPostconditions().stream().anyMatch(p -> p.contains("\\result >= 0")),
                "double x * x is non-negative; expected \\result >= 0, got: " + specDouble.getPostconditions());
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == a + b")
        //   int add(int a, int b) {
        //       return a + b;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == a * b")
        //   int multiply(int a, int b) {
        //       return a * b;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == a - b")
        //   int subtract(int a, int b) {
        //       return a - b;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == a / b")
        //   int divide(int a, int b) {
        //       return a / b;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result > n")
        //   int increment(int n) {
        //       return n + 5;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result >= 1")     (or "\\result > 0")
        //   int classify(int x) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == 1 || \\result == -1")
        //   int sign(int x) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   String safe(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("s != null ==> \\result != null")
        //   String upper(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == this")
        //   @Ensures("this.value == v")
        //   @Assignable("this.value")
        //   Builder setValue(int v) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() == s.length()")
        //   String upper(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() == s.length()")
        //   String lower(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() <= s.length()")
        //   String cleaned(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() == 3")
        //   String sub(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() == s.length() + 3")
        //   String append(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("a != null")
        //   @Requires("b != null")
        //   @Ensures("\\result != null")
        //   @Ensures("(\\bigint)\\result.length() == (\\bigint)a.length() + (\\bigint)b.length()")
        //   String combine(String a, String b) { ... }
        // Length sum is expressed in bigint so it doesn't falsely overflow
        // when the individual lengths approach Integer.MAX_VALUE.
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("a.length()") && p.contains("b.length()")
                        && p.contains("\\result.length()")),
                "Expected length sum postcondition");
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() == s.length() * 3")
        //   String rep(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() == 5")
        //   String hello() {
        //       return "hello";
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.isEmpty()")
        //   String empty() {
        //       return "";
        //   }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length() <= s.length()")
        //   String cleaned(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Requires("s != null")
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.equals(s)")
        //   String interned(String s) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   List<String> create() {
        //       return new ArrayList<>();
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Ensures("\\result.length == n")
        //   int[] create(int n) {
        //       return new int[n];
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == this.name")
        //   @Observer
        //   int getName() {
        //       return this.name;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("\\result != null")
        //   @Ensures("\\result instanceof Widget")
        //   static Widget create() {
        //       return new Widget();
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("...equals...")      (reflexive property of equals)
        //   public boolean equals(Object obj) { ... }
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
        // Expected annotated method after inference:
        //   @Ensures("this.count == \\old(this.count) + 1")
        //   @Assignable("this.count")
        //   @Mutator
        //   void increment() {
        //       this.count++;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("this.count == \\old(this.count) - 1")
        //   @Assignable("this.count")
        //   @Mutator
        //   void decrement() {
        //       this.count--;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("this.value == v")
        //   @Assignable("this.value")
        //   @Mutator
        //   void setValue(int v) {
        //       this.value = v;
        //   }
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
        // Expected annotated method after inference:
        //   @Ensures("this.balance == \\old(this.balance) + amount")
        //   @Assignable("this.balance")
        //   @Mutator
        //   void deposit(int amount) {
        //       this.balance += amount;
        //   }
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
        // Expected annotated method after inference:
        //   @Requires("items != null")
        //   @Ensures("items.size() == \\old(items.size()) + 1")
        //   void addItem(List<String> items, String item) {
        //       items.add(item);
        //   }
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
        // Expected annotated method after inference:
        //   @Requires("items != null")
        //   @Ensures("items.isEmpty()")
        //   void clearAll(List<String> items) {
        //       items.clear();
        //   }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("items.isEmpty()")),
                "Expected isEmpty postcondition");
    }

    @Test
    @DisplayName("Array element write -> assignable clause captures modification")
    void arrayModification() {
        MethodSpecification spec = infer("""
            class T {
                void setFirst(int[] arr, int val) {
                    arr[0] = val;
                }
            }
            """, "setFirst");
        // Array writes are captured by assignable clauses, not postconditions
        // (natural language "arr modified" is not valid JML)
        assertTrue(spec.getAssignableClauses().stream().anyMatch(a -> a.contains("arr")),
                "Expected assignable clause for arr, got: " + spec.getAssignableClauses());
    }

    // ---- Exception guarantees ----

    @Test
    @DisplayName("throws IOException -> signals specification")
    void throwsDeclaration() {
        MethodSpecification spec = infer("""
            class T {
                void read() throws java.io.IOException {
                }
            }
            """, "read");
        // Throws declarations are captured by @Signals, not postconditions
        // (natural language "may throw IOException" is not valid JML)
        assertTrue(spec.getExceptionSpecifications().stream()
                        .anyMatch(e -> e.contains("IOException")),
                "Expected IOException in exception specifications, got: " + spec.getExceptionSpecifications());
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
        // Expected annotated method after inference:
        //   @Ensures("\\result == a + b")
        //   @Pure
        //   int compute(int a, int b) {
        //       int result = a + b;
        //       return result;
        //   }
        assertTrue(spec.getPostconditions().stream().anyMatch(p -> p.contains("\\result == a + b")),
                "Expected resolved return expression");
    }

    // ---- Ternary conditional implications ----

    @Test
    @DisplayName("Ternary max: infers same implications as if/else")
    void ternaryMaxImplications() {
        MethodSpecification ternarySpec = infer("""
            class T {
                int max(int a, int b) {
                    return a >= b ? a : b;
                }
            }
            """, "max");
        MethodSpecification ifElseSpec = infer("""
            class T {
                int max(int a, int b) {
                    if (a >= b) return a;
                    else return b;
                }
            }
            """, "max");
        // Both forms should produce the same conditional postconditions
        assertTrue(ternarySpec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("a >= b") && p.contains("\\result == a")),
                "Ternary should infer a >= b ==> \\result == a, got: " + ternarySpec.getPostconditions());
        assertTrue(ternarySpec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("a < b") && p.contains("\\result == b")),
                "Ternary should infer a < b ==> \\result == b, got: " + ternarySpec.getPostconditions());
        // Verify parity with if/else form
        assertEquals(ifElseSpec.getPostconditions(), ternarySpec.getPostconditions(),
                "Ternary and if/else should produce identical postconditions");
    }

    @Test
    @DisplayName("Ternary abs: infers conditional implications")
    void ternaryAbsImplications() {
        MethodSpecification spec = infer("""
            class T {
                int abs(int x) {
                    return x >= 0 ? x : -x;
                }
            }
            """, "abs");
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("x >= 0") && p.contains("\\result == x")),
                "Expected x >= 0 ==> \\result == x, got: " + spec.getPostconditions());
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("x < 0") && p.contains("\\result == -x")),
                "Expected x < 0 ==> \\result == -x, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Multi-branch if-chain: path conditions are simplified")
    void multiBranchIfChainSimplified() {
        MethodSpecification spec = infer("""
            class T {
                int sign(int x) {
                    if (x > 0) return 1;
                    if (x < 0) return -1;
                    return 0;
                }
            }
            """, "sign");
        // Should produce simplified conditions, not redundant conjunctions
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.equals("x > 0 ==> \\result == 1")),
                "Expected x > 0 ==> \\result == 1, got: " + spec.getPostconditions());
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.equals("x < 0 ==> \\result == -1")),
                "Expected x < 0 ==> \\result == -1 (simplified), got: " + spec.getPostconditions());
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.equals("x == 0 ==> \\result == 0")),
                "Expected x == 0 ==> \\result == 0 (simplified), got: " + spec.getPostconditions());
        // Verify no redundant conjunctions leak through
        assertFalse(spec.getPostconditions().stream().anyMatch(p -> p.contains("&&")),
                "Should not contain redundant conjunctions, got: " + spec.getPostconditions());
    }

    // ---- Loop invariant promotion to ensures ----

    @Test
    @DisplayName("Array fill: loop invariant promoted to ensures with exit value")
    void loopInvariantPromotedToEnsures() {
        MethodSpecification spec = infer("""
            class T {
                void fill(int[] arr, int val) {
                    for (int i = 0; i < arr.length; i++) {
                        arr[i] = val;
                    }
                }
            }
            """, "fill");
        // Loop invariant should exist with counter variable
        assertTrue(spec.getLoopInvariants().stream()
                        .anyMatch(inv -> inv.contains("\\forall") && inv.contains("< i")),
                "Expected loop invariant with counter i, got: " + spec.getLoopInvariants());
        // Postcondition should have the invariant with counter replaced by exit value
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\forall") && p.contains("< arr.length") && p.contains("arr[k] == val")),
                "Expected ensures with i replaced by arr.length, got: " + spec.getPostconditions());
    }
}
