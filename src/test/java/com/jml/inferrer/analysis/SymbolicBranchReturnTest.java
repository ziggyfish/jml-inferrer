package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for symbolic propagation through if/else branches that return.
 */
@DisplayName("Symbolic Propagation - Branch Returns")
class SymbolicBranchReturnTest extends InferrerTestBase {

    @Test
    @DisplayName("If/else both return with resolved expressions")
    void ifElseBranchReturns() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    if (a > 0) {
                        return x + 1;
                    } else {
                        return x - 1;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > 0 ==> \\result == (a * 2) + 1")
        //   @Ensures("a <= 0 ==> \\result == (a * 2) - 1")
        //   @Pure
        //   int compute(int a) {
        //       int x = a * 2;       // x -> a * 2
        //       if (a > 0)  return x + 1;   // -> (a * 2) + 1
        //       else        return x - 1;   // -> (a * 2) - 1
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 0", "(a * 2) + 1"),
                "Expected conditional for a > 0 branch, got: " + posts);
        assertTrue(anyContainsAll(posts, "a <= 0", "(a * 2) - 1"),
                "Expected conditional for a <= 0 branch, got: " + posts);
    }

    @Test
    @DisplayName("If/else returning different computations with multiple locals")
    void ifElseComplexExpressions() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int sum = a + b;
                    int diff = a - b;
                    if (a > b) {
                        return sum * 2;
                    } else {
                        return diff * 3;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > b ==> \\result == (a + b) * 2")
        //   @Ensures("a <= b ==> \\result == (a - b) * 3")
        //   @Pure
        //   int compute(int a, int b) {
        //       int sum = a + b;     // sum -> a + b
        //       int diff = a - b;    // diff -> a - b
        //       if (a > b)  return sum * 2;    // -> (a + b) * 2
        //       else        return diff * 3;   // -> (a - b) * 3
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > b", "(a + b) * 2"),
                "Expected a > b ==> \\result == (a + b) * 2, got: " + posts);
        assertTrue(anyContainsAll(posts, "a <= b", "(a - b) * 3"),
                "Expected a <= b ==> \\result == (a - b) * 3, got: " + posts);
    }

    @Test
    @DisplayName("Nested if/else with returns")
    void nestedIfElseReturns() {
        MethodSpecification spec = infer("""
            class T {
                int classify(int x) {
                    int val = x * x;
                    if (x > 0) {
                        if (x > 10) {
                            return val + 100;
                        } else {
                            return val + 10;
                        }
                    } else {
                        return val - 1;
                    }
                }
            }
            """, "classify");
        // Expected annotated method after inference:
        //   @Ensures("x > 10 ==> \\result == (x * x) + 100")
        //   @Ensures("x > 0 && x <= 10 ==> \\result == (x * x) + 10")
        //   @Ensures("x <= 0 ==> \\result == (x * x) - 1")
        //   @Pure
        //   int classify(int x) {
        //       int val = x * x;    // val -> x * x
        //       if (x > 0) {
        //           if (x > 10) return val + 100;   // -> (x * x) + 100
        //           else        return val + 10;    // -> (x * x) + 10
        //       } else {
        //           return val - 1;                 // -> (x * x) - 1
        //       }
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "x > 10", "(x * x) + 100"),
                "Expected nested condition for x > 10, got: " + posts);
        assertTrue(anyContainsAll(posts, "x <= 0", "(x * x) - 1"),
                "Expected condition for x <= 0, got: " + posts);
    }

    @Test
    @DisplayName("If/else both return same expression -> unconditional")
    void bothBranchesSameResult() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    if (a > 0) {
                        return x;
                    } else {
                        return x;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == a * 2")    (unconditional -- both branches return same)
        //   @Pure
        //   int compute(int a) {
        //       int x = a * 2;   // x -> a * 2
        //       if (a > 0) return x;   // -> a * 2
        //       else       return x;   // -> a * 2 (same)
        //   }
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result ==") && p.contains("a * 2") && !p.contains("==>")),
                "Expected unconditional \\result == a * 2, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Three-way branching: if/elseif/else")
    void threeWayBranching() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    if (a > 10) {
                        return x * 3;
                    } else if (a > 0) {
                        return x * 2;
                    } else {
                        return x;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > 10 ==> \\result == (a + 1) * 3")
        //   @Ensures("a > 0 && a <= 10 ==> \\result == (a + 1) * 2")
        //   @Ensures("a <= 0 ==> \\result == a + 1")
        //   @Pure
        //   int compute(int a) {
        //       int x = a + 1;   // x -> a + 1
        //       if (a > 10)      return x * 3;   // -> (a + 1) * 3
        //       else if (a > 0)  return x * 2;   // -> (a + 1) * 2
        //       else             return x;        // -> a + 1
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 10", "(a + 1) * 3"),
                "Expected branch for a > 10, got: " + posts);
    }

    @Test
    @DisplayName("Condition uses local variable resolved through env")
    void conditionUsesLocalVar() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int diff = a - b;
                    if (a > 0) {
                        return diff + 1;
                    } else {
                        return diff - 1;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > 0 ==> \\result == (a - b) + 1")
        //   @Ensures("a <= 0 ==> \\result == (a - b) - 1")
        //   @Pure
        //   int compute(int a, int b) {
        //       int diff = a - b;    // diff -> a - b
        //       if (a > 0)  return diff + 1;   // -> (a - b) + 1
        //       else        return diff - 1;   // -> (a - b) - 1
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 0", "a - b"),
                "Expected resolved diff in branch, got: " + posts);
    }

    @Test
    @DisplayName("If/else with equality condition")
    void equalityCondition() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 3;
                    if (a == 0) {
                        return x;
                    } else {
                        return x + a;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a == 0 ==> \\result == a * 3")
        //   @Ensures("a != 0 ==> \\result == (a * 3) + a")
        //   @Pure
        //   int compute(int a) {
        //       int x = a * 3;   // x -> a * 3
        //       if (a == 0) return x;       // -> a * 3
        //       else        return x + a;   // -> (a * 3) + a
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a == 0") || anyContainsAll(posts, "a != 0"),
                "Expected equality-based condition, got: " + posts);
    }

    @Test
    @DisplayName("If/else where both branches do computation before returning")
    void branchesWithComputation() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int base = a + 10;
                    if (a > 5) {
                        int y = base * 2;
                        return y;
                    } else {
                        int z = base * 3;
                        return z;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > 5 ==> \\result == (a + 10) * 2")
        //   @Ensures("a <= 5 ==> \\result == (a + 10) * 3")
        //   @Pure
        //   int compute(int a) {
        //       int base = a + 10;   // base -> a + 10
        //       if (a > 5) {
        //           int y = base * 2;   // y -> (a + 10) * 2
        //           return y;
        //       } else {
        //           int z = base * 3;   // z -> (a + 10) * 3
        //           return z;
        //       }
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a > 5", "a + 10"),
                "Expected resolved base in conditional, got: " + posts);
    }

    @Test
    @DisplayName("Four-way nested branching")
    void fourWayNesting() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    if (a > 0) {
                        if (a > 100) {
                            return x + 100;
                        } else {
                            return x + 10;
                        }
                    } else {
                        if (a < -100) {
                            return x - 100;
                        } else {
                            return x - 10;
                        }
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > 100 ==> \\result == (a * 2) + 100")
        //   @Ensures("a > 0 && a <= 100 ==> \\result == (a * 2) + 10")
        //   @Ensures("a < -100 ==> \\result == (a * 2) - 100")
        //   @Ensures("a >= -100 && a <= 0 ==> \\result == (a * 2) - 10")
        //   @Pure
        //   int compute(int a) { ... }
        List<String> posts = spec.getPostconditions();
        // Should produce 4 conditional postconditions
        long conditionalCount = posts.stream().filter(p -> p.contains("==>")).count();
        assertTrue(conditionalCount >= 3,
                "Expected at least 3 conditional postconditions, got " + conditionalCount + ": " + posts);
    }

    @Test
    @DisplayName("Else-if chain without final else (last branch is guard)")
    void elseIfChainNoFinalElse() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    if (a > 10) {
                        return x * 3;
                    } else if (a > 0) {
                        return x * 2;
                    }
                    return x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a > 10 ==> \\result == (a + 1) * 3")
        //   @Ensures("a > 0 && a <= 10 ==> \\result == (a + 1) * 2")
        //   @Ensures("a <= 0 ==> \\result == a + 1")
        //   @Pure
        //   int compute(int a) { ... }
        assertNotNull(spec);
        assertFalse(spec.getPostconditions().isEmpty(), "Expected postconditions");
    }

    @Test
    @DisplayName("Condition with >= operator")
    void greaterEqualCondition() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 5;
                    if (a >= 10) {
                        return x + 1;
                    } else {
                        return x - 1;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a >= 10 ==> \\result == (a * 5) + 1")
        //   @Ensures("a < 10 ==> \\result == (a * 5) - 1")
        //   @Pure
        //   int compute(int a) {
        //       int x = a * 5;   // x -> a * 5
        //       if (a >= 10) return x + 1;   // -> (a * 5) + 1
        //       else         return x - 1;   // -> (a * 5) - 1
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a >= 10", "(a * 5) + 1"),
                "Expected a >= 10 condition, got: " + posts);
        assertTrue(anyContainsAll(posts, "a < 10", "(a * 5) - 1"),
                "Expected negated a < 10, got: " + posts);
    }

    @Test
    @DisplayName("Condition with != operator")
    void notEqualCondition() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    if (a != 0) {
                        return x * 2;
                    } else {
                        return x;
                    }
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("a != 0 ==> \\result == (a + 1) * 2")
        //   @Ensures("a == 0 ==> \\result == a + 1")
        //   @Pure
        //   int compute(int a) {
        //       int x = a + 1;   // x -> a + 1
        //       if (a != 0) return x * 2;   // -> (a + 1) * 2
        //       else        return x;       // -> a + 1
        //   }
        List<String> posts = spec.getPostconditions();
        assertTrue(anyContainsAll(posts, "a != 0") || anyContainsAll(posts, "a == 0"),
                "Expected != based conditions, got: " + posts);
    }
}
