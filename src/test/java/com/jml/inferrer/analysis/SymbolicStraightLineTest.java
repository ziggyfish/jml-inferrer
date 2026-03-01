package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for straight-line symbolic expression propagation through local variables.
 */
@DisplayName("Symbolic Propagation - Straight-line Code")
class SymbolicStraightLineTest extends InferrerTestBase {

    @Test
    @DisplayName("Simple variable substitution: return local var assigned from params")
    void simpleSubstitution() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int x = a + b;
                    return x;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == a + b")),
                "Expected \\result == a + b, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Chained substitution: a=a*a, b=a+c, b=b*b")
    void chainedSubstitution() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int c) {
                    a = a * a;
                    int b = a + c;
                    b = b * b;
                    return b;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == ((a * a) + c) * ((a * a) + c)")),
                "Expected chained substitution, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Compound assignment: x += y expands to x + y")
    void compoundAssignment() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int x = a;
                    x += b;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a", "b", "+"),
                "Expected \\result == a + b, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Compound multiply assignment: x *= 2")
    void compoundMultiplyAssignment() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    x *= 2;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a + 1", "* 2"),
                "Expected \\result == (a + 1) * 2, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Multiple local variables chained")
    void multipleLocals() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int x) {
                    int a = x + 1;
                    int b = a * 2;
                    int c = b - x;
                    return c;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "x + 1", "* 2", "- x"),
                "Expected \\result == ((x + 1) * 2) - x, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Parameter reassignment then use")
    void paramReassignment() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    n = n * n;
                    int result = n + 1;
                    return result;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "n * n", "+ 1"),
                "Expected \\result == (n * n) + 1, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("No substitution needed - returns parameter directly")
    void directParamReturn() {
        MethodSpecification spec = infer("""
            class T {
                int identity(int x) {
                    return x;
                }
            }
            """, "identity");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == x")),
                "Expected \\result == x, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Compound subtraction: x -= b")
    void compoundSubtraction() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int x = a;
                    x -= b;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a", "-", "b"),
                "Expected \\result == a - b, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Compound division: x /= 2")
    void compoundDivision() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 10;
                    x /= 2;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a * 10", "/ 2"),
                "Expected \\result involving division, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Compound remainder: x %= 3")
    void compoundRemainder() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 5;
                    x %= 3;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a + 5", "% 3"),
                "Expected remainder expression, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Multiple reassignments of the same variable")
    void multipleReassignments() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int x) {
                    int a = x;
                    a = a + 1;
                    a = a * 2;
                    a = a - 3;
                    return a;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result =="),
                "Expected symbolic result, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Three params combined in chain")
    void threeParamChain() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b, int c) {
                    int x = a + b;
                    int y = x * c;
                    return y;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a + b", "* c"),
                "Expected (a + b) * c, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Variable used but not assigned in env -> left as-is")
    void uninitializedVarLeftAsIs() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a + 1"),
                "Expected \\result == a + 1, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Two independent locals, return one")
    void twoIndependentLocals() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int x = a * 2;
                    int y = b * 3;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a * 2"),
                "Expected \\result == a * 2, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Bitwise compound: x |= mask")
    void bitwiseCompound() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int flags, int mask) {
                    int x = flags;
                    x |= mask;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "flags", "|", "mask"),
                "Expected bitwise or expression, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Variable declared without initializer then assigned")
    void declaredThenAssigned() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x;
                    x = a * 3;
                    return x;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a * 3"),
                "Expected \\result == a * 3, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Deep chain of four variables")
    void deepChainFourVars() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    int a = n + 1;
                    int b = a + 2;
                    int c = b + 3;
                    int d = c + 4;
                    return d;
                }
            }
            """, "compute");
        // n+1+2+3+4 = n + 10 but represented as nested
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "n + 1"),
                "Expected chain starting with n+1, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Parameter multiplied by itself: n * n")
    void selfSquare() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    int sq = n * n;
                    return sq;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "n * n"),
                "Expected \\result == n * n, got: " + spec.getPostconditions());
    }
}
