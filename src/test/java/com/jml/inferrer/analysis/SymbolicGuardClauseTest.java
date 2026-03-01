package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for guard clause detection and symbolic propagation past guard returns.
 */
@DisplayName("Symbolic Propagation - Guard Clauses")
class SymbolicGuardClauseTest extends InferrerTestBase {

    @Test
    @DisplayName("Simple guard clause: if (bad) return early, then normal path")
    void simpleGuardClause() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    if (a < 0) {
                        return -1;
                    }
                    int x = a * a;
                    return x + 1;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "a >= 0", "(a * a) + 1"),
                "Expected a >= 0 ==> \\result == (a * a) + 1, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Multiple guard clauses stacked")
    void multipleGuardClauses() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    if (a < 0) {
                        return -1;
                    }
                    if (a == 0) {
                        return 0;
                    }
                    int x = a * a;
                    return x + a;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "a >= 0", "(a * a) + a"),
                "Expected guard-aware result, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard clause with throw instead of return")
    void guardClauseWithThrow() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    if (a < 0) {
                        throw new IllegalArgumentException("negative");
                    }
                    int x = a * 2;
                    return x + 1;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("(a * 2) + 1")),
                "Expected \\result involving (a * 2) + 1, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard clause where then-returns, has else that doesn't return")
    void guardThenReturnsWithElse() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x;
                    if (a < 0) {
                        return -1;
                    } else {
                        x = a * 2;
                    }
                    return x + 1;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("(a * 2) + 1")),
                "Expected result involving (a * 2) + 1, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard clause with > operator")
    void guardGreaterThan() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n > 100) {
                        return 100;
                    }
                    int result = n * n;
                    return result;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "n <= 100", "n * n"),
                "Expected n <= 100 ==> \\result == n * n, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard clause with equality check")
    void guardEquality() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    if (n == 0) {
                        return 0;
                    }
                    int result = n * 2 + 1;
                    return result;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "n != 0", "n * 2"),
                "Expected n != 0 ==> result involving n * 2, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Three stacked guards with computation after")
    void threeStackedGuards() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    if (a < 0) return -1;
                    if (a == 0) return 0;
                    if (a > 1000) return 1000;
                    int x = a * a;
                    return x;
                }
            }
            """, "compute");
        // After all guards: a >= 0 && a != 0 && a <= 1000
        assertTrue(anyContainsAll(spec.getPostconditions(), "a * a"),
                "Expected result involving a * a, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard with else-if pattern")
    void guardElseIf() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    if (a < 0) {
                        return -1;
                    } else if (a == 0) {
                        return 0;
                    }
                    int x = a + 10;
                    return x;
                }
            }
            """, "compute");
        assertNotNull(spec);
        assertFalse(spec.getPostconditions().isEmpty(), "Expected postconditions");
    }

    @Test
    @DisplayName("Guard returns literal, rest returns complex expression")
    void guardLiteralRestComplex() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    if (a == b) {
                        return 0;
                    }
                    int diff = a - b;
                    int result = diff * diff;
                    return result;
                }
            }
            """, "compute");
        assertTrue(anyContainsAll(spec.getPostconditions(), "a != b", "a - b"),
                "Expected guard-aware with diff expression, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Guard clause followed by if/else branches")
    void guardFollowedByBranch() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    if (a < 0) {
                        return -1;
                    }
                    int x = a * 2;
                    if (a > 10) {
                        return x + 100;
                    } else {
                        return x + 1;
                    }
                }
            }
            """, "compute");
        List<String> posts = spec.getPostconditions();
        // After guard: a >= 0, then branch on a > 10
        assertTrue(anyContainsAll(posts, "a > 10", "(a * 2) + 100"),
                "Expected conditional after guard for a > 10, got: " + posts);
        assertTrue(anyContainsAll(posts, "a <= 10", "(a * 2) + 1"),
                "Expected conditional after guard for a <= 10, got: " + posts);
    }

    @Test
    @DisplayName("Guard with throw then complex straight-line")
    void guardThrowThenStraightLine() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    if (b == 0) {
                        throw new ArithmeticException("div by zero");
                    }
                    int quotient = a / b;
                    int result = quotient * b + a % b;
                    return result;
                }
            }
            """, "compute");
        assertNotNull(spec);
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result =="),
                "Expected symbolic postcondition, got: " + spec.getPostconditions());
    }
}
