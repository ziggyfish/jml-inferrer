package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for variables assigned differently in if/else branches then returned later.
 */
@DisplayName("Symbolic Propagation - Branch Assign then Return")
class SymbolicBranchAssignTest extends InferrerTestBase {

    @Test
    @DisplayName("If/else assign to same variable, then return it")
    void branchAssignThenReturn() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int r;
                    if (a > 0) {
                        r = a + 1;
                    } else {
                        r = a - 1;
                    }
                    return r;
                }
            }
            """, "compute");
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 0", "a + 1"),
                "Expected a > 0 ==> \\result == a + 1, got: " + posts);
        assertTrue(anyContainsAll(posts, "a <= 0", "a - 1"),
                "Expected a <= 0 ==> \\result == a - 1, got: " + posts);
    }

    @Test
    @DisplayName("Branch assign with complex expressions")
    void branchAssignComplexExpr() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int x = a + b;
                    int r;
                    if (a > b) {
                        r = x * 2;
                    } else {
                        r = x * 3;
                    }
                    return r;
                }
            }
            """, "compute");
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > b", "(a + b) * 2"),
                "Expected a > b ==> \\result == (a + b) * 2, got: " + posts);
        assertTrue(anyContainsAll(posts, "a <= b", "(a + b) * 3"),
                "Expected a <= b ==> \\result == (a + b) * 3, got: " + posts);
    }

    @Test
    @DisplayName("Both branches assign same value -> unconditional")
    void branchAssignSameValue() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    int r;
                    if (a > 0) {
                        r = x;
                    } else {
                        r = x;
                    }
                    return r;
                }
            }
            """, "compute");
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result ==") && p.contains("a * 2")),
                "Expected unconditional \\result == a * 2, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Branch assign with additional computation after merge")
    void branchAssignThenCompute() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int r;
                    if (a > 0) {
                        r = a * 2;
                    } else {
                        r = a * 3;
                    }
                    return r;
                }
            }
            """, "compute");
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 0", "a * 2"),
                "Expected conditional for a > 0, got: " + posts);
        assertTrue(anyContainsAll(posts, "a <= 0", "a * 3"),
                "Expected conditional for a <= 0, got: " + posts);
    }

    @Test
    @DisplayName("Branch assign multiple variables with different values")
    void branchAssignMultipleVars() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x;
                    int y;
                    if (a > 0) {
                        x = a + 1;
                        y = a + 2;
                    } else {
                        x = a - 1;
                        y = a - 2;
                    }
                    return x;
                }
            }
            """, "compute");
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 0", "a + 1") || anyContainsAll(posts, "a <= 0", "a - 1"),
                "Expected branch-dependent result for x, got: " + posts);
    }

    @Test
    @DisplayName("Branch assign with pre-branch local in expression")
    void preBranchLocalInBranchAssign() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int base = a * 10;
                    int r;
                    if (a > 5) {
                        r = base + 1;
                    } else {
                        r = base - 1;
                    }
                    return r;
                }
            }
            """, "compute");
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 5", "a * 10"),
                "Expected base (a*10) resolved in conditional, got: " + posts);
    }

    @Test
    @DisplayName("Nested branch assign: outer if/else, inner if/else")
    void nestedBranchAssign() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int r;
                    if (a > 0) {
                        if (a > 10) {
                            r = a * 3;
                        } else {
                            r = a * 2;
                        }
                    } else {
                        r = a;
                    }
                    return r;
                }
            }
            """, "compute");
        assertNotNull(spec);
        assertFalse(spec.getPostconditions().isEmpty(), "Expected postconditions");
    }

    @Test
    @DisplayName("Branch assign then further computation before return")
    void branchAssignThenFurtherComputation() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int base;
                    if (a > 0) {
                        base = a;
                    } else {
                        base = -a;
                    }
                    int result = base * base;
                    return result;
                }
            }
            """, "compute");
        // base is branch-dependent, result depends on base
        assertNotNull(spec);
    }
}
