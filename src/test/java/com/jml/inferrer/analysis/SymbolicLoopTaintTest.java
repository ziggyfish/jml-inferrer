package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for loop taint: variables modified in loops are removed from the symbolic env.
 */
@DisplayName("Symbolic Propagation - Loop Taint")
class SymbolicLoopTaintTest extends InferrerTestBase {

    @Test
    @DisplayName("Variable assigned before loop, not modified in loop -> preserved")
    void loopPreservesUnmodifiedVar() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int[] arr) {
                    int f = a * 2;
                    int total = 0;
                    for (int i = 0; i < arr.length; i++) {
                        total += arr[i];
                    }
                    return f;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Ensures("\\result == a * 2")   (f is NOT modified in the loop)
        //   int compute(int a, int[] arr) {
        //       int f = a * 2;       // f -> a * 2 (preserved through loop)
        //       int total = 0;       // total is modified in loop (tainted)
        //       for (...) { total += arr[i]; }
        //       return f;            // f still resolves to a * 2
        //   }
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result ==") && p.contains("a * 2")),
                "Expected \\result == a * 2, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Variable modified in loop -> tainted, not resolved")
    void loopTaintsModifiedVar() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    for (int i = 0; i < 10; i++) {
                        x += i;
                    }
                    return x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   (no @Ensures for \\result == a * 2 -- x is tainted by loop modification)
        //   int compute(int a) {
        //       int x = a * 2;   // x -> a * 2 initially
        //       for (...) { x += i; }   // x is TAINTED (modified in loop)
        //       return x;        // cannot resolve x symbolically
        //   }
        assertFalse(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == a * 2")),
                "Should NOT resolve tainted variable, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("While loop taints variable")
    void whileLoopTaints() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    int result = n + 1;
                    int x = 0;
                    while (x < n) {
                        result = result * 2;
                        x++;
                    }
                    return result;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   (no @Ensures for \\result == (n + 1) -- result is tainted by while loop)
        //   int compute(int n) {
        //       int result = n + 1;   // result -> n + 1 initially
        //       int x = 0;
        //       while (x < n) {
        //           result = result * 2;   // result TAINTED
        //           x++;
        //       }
        //       return result;              // cannot resolve
        //   }
        assertFalse(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == (n + 1)")),
                "Should NOT resolve loop-tainted variable, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("For-each loop taints accumulator but not pre-loop var")
    void forEachLoopTaints() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int base, int[] arr) {
                    int pre = base * 3;
                    int sum = 0;
                    for (int val : arr) {
                        sum += val;
                    }
                    return pre;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Requires("arr != null")
        //   @Ensures("\\result == base * 3")   (pre is NOT modified in the loop)
        //   int compute(int base, int[] arr) {
        //       int pre = base * 3;   // pre -> base * 3 (preserved)
        //       int sum = 0;          // sum is tainted by for-each
        //       for (int val : arr) { sum += val; }
        //       return pre;           // pre still resolves to base * 3
        //   }
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result ==") && p.contains("base * 3")),
                "Expected \\result == base * 3, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Do-while loop taints variable")
    void doWhileLoopTaints() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    int safe = n + 5;
                    int x = 1;
                    do {
                        x *= 2;
                    } while (x < n);
                    return safe;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == n + 5")   (safe is NOT modified in the do-while)
        //   int compute(int n) {
        //       int safe = n + 5;   // safe -> n + 5 (preserved)
        //       int x = 1;          // x is tainted by do-while
        //       do { x *= 2; } while (x < n);
        //       return safe;        // safe still resolves to n + 5
        //   }
        assertTrue(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result ==") && p.contains("n + 5")),
                "Expected safe (unmodified) variable result, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("For loop with unary increment in update taints the loop variable")
    void forLoopUpdateTaints() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a * 2;
                    int i = 0;
                    for (i = 0; i < 10; i++) {
                        // empty body
                    }
                    return x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == a * 2")   (x is NOT modified in the loop)
        //   int compute(int a) {
        //       int x = a * 2;   // x -> a * 2 (preserved)
        //       int i = 0;       // i is tainted by for-loop update (i++)
        //       for (i = 0; i < 10; i++) { }
        //       return x;        // x still resolves to a * 2
        //   }
        // x is NOT modified, should still resolve
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a * 2"),
                "Expected \\result == a * 2 (not tainted), got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Two loops: first modifies x, second doesn't touch y")
    void twoLoopsIndependent() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a, int b) {
                    int x = a;
                    int y = b * 3;
                    for (int i = 0; i < 5; i++) {
                        x += i;
                    }
                    for (int j = 0; j < 3; j++) {
                        // don't touch y
                    }
                    return y;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == b * 3")   (y is untouched by both loops)
        //   int compute(int a, int b) {
        //       int x = a;         // x is tainted by first loop
        //       int y = b * 3;     // y -> b * 3 (preserved through both loops)
        //       for (...) { x += i; }   // taints x only
        //       for (...) { }           // no modifications
        //       return y;               // y still resolves to b * 3
        //   }
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "b * 3"),
                "Expected y (b * 3) preserved, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Nested loops taint variables from both levels")
    void nestedLoopsTaint() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    int count = 0;
                    for (int i = 0; i < 10; i++) {
                        for (int j = 0; j < 10; j++) {
                            count++;
                        }
                    }
                    return x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == a + 1")   (x is NOT modified in any loop)
        //   int compute(int a) {
        //       int x = a + 1;     // x -> a + 1 (preserved through nested loops)
        //       int count = 0;     // count is tainted by inner loop (count++)
        //       for (...) { for (...) { count++; } }
        //       return x;          // x still resolves to a + 1
        //   }
        // x is NOT modified in any loop
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a + 1"),
                "Expected x preserved through nested loops, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Variable declared in loop is scoped to loop, doesn't taint outer")
    void loopScopedVariable() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int result = a * 5;
                    for (int i = 0; i < 10; i++) {
                        int temp = i * 2;
                    }
                    return result;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == a * 5")   (result is NOT modified; temp is loop-scoped)
        //   int compute(int a) {
        //       int result = a * 5;   // result -> a * 5 (preserved)
        //       for (...) {
        //           int temp = i * 2;  // temp is loop-scoped, doesn't taint result
        //       }
        //       return result;        // result still resolves to a * 5
        //   }
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "a * 5"),
                "Expected result preserved, got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Loop with decrement operator taints variable")
    void loopDecrementTaints() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int n) {
                    int x = n * 2;
                    int count = n;
                    while (count > 0) {
                        count--;
                    }
                    return x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Ensures("\\result == n * 2")   (x is NOT modified; count is tainted)
        //   int compute(int n) {
        //       int x = n * 2;     // x -> n * 2 (preserved)
        //       int count = n;     // count is tainted by while loop (count--)
        //       while (count > 0) { count--; }
        //       return x;          // x still resolves to n * 2
        //   }
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "n * 2"),
                "Expected x preserved (count tainted), got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Loop modifies variable via assignment, not just compound")
    void loopAssignmentTaints() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int a) {
                    int x = a + 1;
                    for (int i = 0; i < 5; i++) {
                        x = x * 2;
                    }
                    return x;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   (no @Ensures for \\result == (a + 1) -- x is tainted by loop assignment)
        //   int compute(int a) {
        //       int x = a + 1;   // x -> a + 1 initially
        //       for (...) { x = x * 2; }   // x is TAINTED (reassigned in loop)
        //       return x;                   // cannot resolve x symbolically
        //   }
        assertFalse(spec.getPostconditions().stream()
                .anyMatch(p -> p.contains("\\result == (a + 1)")),
                "x should be tainted by loop assignment");
    }

    @Test
    @DisplayName("For-each loop with array parameter preserves pre-loop computation")
    void forEachArrayParam() {
        MethodSpecification spec = infer("""
            class T {
                int compute(int multiplier, int[] values) {
                    int factor = multiplier * multiplier;
                    int total = 0;
                    for (int v : values) {
                        total += v;
                    }
                    return factor;
                }
            }
            """, "compute");
        // Expected annotated method after inference:
        //   @Requires("values != null")
        //   @Ensures("\\result == multiplier * multiplier")
        //   @Ensures("\\result >= 0")
        //   int compute(int multiplier, int[] values) {
        //       int factor = multiplier * multiplier;   // factor -> multiplier * multiplier (preserved)
        //       int total = 0;                          // total is tainted by for-each
        //       for (int v : values) { total += v; }
        //       return factor;                          // factor still resolves
        //   }
        assertTrue(anyContainsAll(spec.getPostconditions(), "\\result ==", "multiplier * multiplier"),
                "Expected factor preserved, got: " + spec.getPostconditions());
    }
}
