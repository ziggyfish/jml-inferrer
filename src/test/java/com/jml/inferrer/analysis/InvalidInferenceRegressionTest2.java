package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Second batch of regression tests for invalid JML specification inference.
 * Covers: natural language in preconditions/postconditions/loop invariants,
 * while-loop conditions as invariants, for-each loop natural language,
 * compound assignment with method call values, and \num_of naive replacement.
 */
@DisplayName("Invalid Inference Regression 2")
class InvalidInferenceRegressionTest2 extends InferrerTestBase {

    // =========================================================================
    // Natural language must not appear in preconditions
    // =========================================================================

    @Test
    @DisplayName("Comparable parameter should generate instanceof, not natural language")
    void comparableGeneratesInstanceof() {
        MethodSpecification spec = infer("""
            class T {
                int compare(Comparable a, Comparable b) {
                    return a.compareTo(b);
                }
            }
            """, "compare");
        for (String pre : spec.getPreconditions()) {
            assertFalse(pre.contains("is Comparable"),
                    "Precondition must not contain natural language 'is Comparable': " + pre);
        }
        // Should generate instanceof Comparable (valid JML)
        assertTrue(spec.getPreconditions().stream()
                        .anyMatch(p -> p.contains("instanceof Comparable")),
                "Expected instanceof Comparable, got: " + spec.getPreconditions());
    }

    // =========================================================================
    // Natural language must not appear in postconditions
    // =========================================================================

    @Test
    @DisplayName("Field assignment with array access should generate valid postcondition")
    void arrayAccessFieldAssignPostcondition() {
        MethodSpecification spec = infer("""
            class T {
                int value;
                void setFromArray(int[] arr, int idx) {
                    this.value = arr[idx];
                }
            }
            """, "setFromArray");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("is modified"),
                    "Postcondition must not contain natural language 'is modified': " + post);
        }
        // Should generate this.value == arr[idx]
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("this.value == arr[idx]")),
                "Expected this.value == arr[idx], got: " + spec.getPostconditions());
    }

    @Test
    @DisplayName("Field assignment with method call should not generate 'is modified' postcondition")
    void noIsModifiedForMethodCallValue() {
        MethodSpecification spec = infer("""
            class T {
                int size;
                void updateSize(java.util.List<String> list) {
                    this.size = list.size();
                }
            }
            """, "updateSize");
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("is modified"),
                    "Postcondition must not contain natural language 'is modified': " + post);
        }
    }

    // =========================================================================
    // While-loop condition should not be added as raw invariant
    // =========================================================================

    @Test
    @DisplayName("While-loop condition should not appear as raw invariant")
    void whileLoopConditionNotRawInvariant() {
        MethodSpecification spec = infer("""
            class T {
                int sumWhile(int[] arr) {
                    int i = 0;
                    int total = 0;
                    while (i < arr.length) {
                        total += arr[i];
                        i++;
                    }
                    return total;
                }
            }
            """, "sumWhile");
        // The while condition "i < arr.length" is NOT a valid invariant because
        // it is false when the loop exits. Only the weakened "i <= arr.length" is valid.
        for (String inv : spec.getLoopInvariants()) {
            if (inv.contains("arr.length") && inv.contains("i")) {
                assertFalse(inv.matches("^i\\s*<\\s*arr\\.length$"),
                        "While-loop condition must not be used as raw invariant: " + inv);
            }
        }
    }

    @Test
    @DisplayName("While-loop with method call condition should generate null check invariant")
    void whileLoopMethodCallConditionGeneratesNullCheck() {
        MethodSpecification spec = infer("""
            class T {
                int countItems(java.util.Iterator<String> iter) {
                    int count = 0;
                    while (iter.hasNext()) {
                        iter.next();
                        count++;
                    }
                    return count;
                }
            }
            """, "countItems");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("has remaining elements") || inv.contains("to process"),
                    "Loop invariant must not contain natural language: " + inv);
        }
        // Should generate iter != null as a valid invariant
        assertTrue(spec.getLoopInvariants().stream().anyMatch(inv -> inv.contains("iter != null")),
                "Expected iter != null invariant, got: " + spec.getLoopInvariants());
    }

    // =========================================================================
    // For-each loop must not generate natural language invariants
    // =========================================================================

    @Test
    @DisplayName("For-each loop should generate iterable null check instead of natural language")
    void forEachGeneratesNullCheck() {
        MethodSpecification spec = infer("""
            class T {
                int sumList(java.util.List<Integer> list) {
                    int total = 0;
                    for (Integer val : list) {
                        total += val;
                    }
                    return total;
                }
            }
            """, "sumList");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("is element of"),
                    "Loop invariant must not contain natural language 'is element of': " + inv);
        }
        // Should generate list != null as a valid invariant
        assertTrue(spec.getLoopInvariants().stream().anyMatch(inv -> inv.contains("list != null")),
                "Expected list != null invariant, got: " + spec.getLoopInvariants());
    }

    @Test
    @DisplayName("For-each loop should not generate 'processed elements' natural language invariant")
    void forEachNoProcessedElements() {
        MethodSpecification spec = infer("""
            class T {
                int sumArray(int[] arr) {
                    int total = 0;
                    for (int val : arr) {
                        total += val;
                    }
                    return total;
                }
            }
            """, "sumArray");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("processed elements") || inv.contains("processed"),
                    "Loop invariant must not contain natural language 'processed elements': " + inv);
        }
    }

    @Test
    @DisplayName("For-each over array should generate arr != null invariant")
    void forEachArrayGeneratesNullCheck() {
        MethodSpecification spec = infer("""
            class T {
                int findMaxForeach(int[] arr) {
                    int max = arr[0];
                    for (int val : arr) {
                        if (val > max) max = val;
                    }
                    return max;
                }
            }
            """, "findMaxForeach");
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("is element of") || inv.contains("processed elements")
                            || inv.contains("processed"),
                    "Loop invariant must not contain natural language: " + inv);
        }
        // Should generate arr != null as a valid invariant
        assertTrue(spec.getLoopInvariants().stream().anyMatch(inv -> inv.contains("arr != null")),
                "Expected arr != null invariant, got: " + spec.getLoopInvariants());
    }

    // =========================================================================
    // Compound assignment value must be validated (no raw toString() of method calls)
    // =========================================================================

    @Test
    @DisplayName("Compound assignment with method call value should not use raw toString in postcondition")
    void compoundAssignMethodCallNotRaw() {
        MethodSpecification spec = infer("""
            class T {
                int total;
                void addSize(java.util.List<String> list) {
                    this.total += list.size();
                }
            }
            """, "addSize");
        // The value "list.size()" is a method call. Postcondition like
        // "this.total == \old(this.total) + list.size()" is actually valid JML
        // if the method is pure, but we should verify no "is modified" appears.
        for (String post : spec.getPostconditions()) {
            assertFalse(post.contains("is modified"),
                    "Postcondition must not contain 'is modified': " + post);
        }
        // Should have a postcondition about the field changing
        assertTrue(spec.getPostconditions().stream()
                        .anyMatch(p -> p.contains("total") && p.contains("\\old")),
                "Expected postcondition with \\old for total, got: " + spec.getPostconditions());
    }

    // =========================================================================
    // \num_of naive string replacement must not corrupt identifiers
    // =========================================================================

    @Test
    @DisplayName("Count pattern with variable name substring of another should not corrupt invariant")
    void numOfNoIdentifierCorruption() {
        MethodSpecification spec = infer("""
            class T {
                int countPositive(int[] items) {
                    int count = 0;
                    for (int i = 0; i < items.length; i++) {
                        if (items[i] > 0) {
                            count++;
                        }
                    }
                    return count;
                }
            }
            """, "countPositive");
        // The naive replacement condition.replace(counter, "k") where counter="i"
        // would corrupt "items" into "ktems". Check no invariant contains "ktems".
        for (String inv : spec.getLoopInvariants()) {
            assertFalse(inv.contains("ktems"),
                    "\\num_of invariant has corrupted identifier (naive string replace): " + inv);
        }
    }

    // =========================================================================
    // All specs must be syntactically valid JML (no natural language anywhere)
    // =========================================================================

    @Test
    @DisplayName("No spec should contain common natural language phrases")
    void noNaturalLanguageInAnySpec() {
        MethodSpecification spec = infer("""
            class T {
                String name;
                int count;
                void process(java.util.List<String> items) {
                    for (String item : items) {
                        this.count++;
                    }
                }
            }
            """, "process");
        String[] naturalLanguagePhrases = {
                "is modified", "is element of", "processed elements",
                "has remaining", "to process", "is Comparable",
                "seen so far", "contains elements"
        };
        for (String pre : spec.getPreconditions()) {
            for (String phrase : naturalLanguagePhrases) {
                assertFalse(pre.contains(phrase),
                        "Precondition contains natural language '" + phrase + "': " + pre);
            }
        }
        for (String post : spec.getPostconditions()) {
            for (String phrase : naturalLanguagePhrases) {
                assertFalse(post.contains(phrase),
                        "Postcondition contains natural language '" + phrase + "': " + post);
            }
        }
        for (String inv : spec.getLoopInvariants()) {
            for (String phrase : naturalLanguagePhrases) {
                assertFalse(inv.contains(phrase),
                        "Loop invariant contains natural language '" + phrase + "': " + inv);
            }
        }
    }

    @Test
    @DisplayName("Wildcard bounded parameter should generate null check instead of natural language")
    void wildcardBoundGeneratesNullCheck() {
        MethodSpecification spec = infer("""
            class T {
                void addAll(java.util.List<? extends Number> src, java.util.List<Number> dst) {
                    for (Number n : src) {
                        dst.add(n);
                    }
                }
            }
            """, "addAll");
        for (String pre : spec.getPreconditions()) {
            assertFalse(pre.contains("contains elements extending") || pre.contains("contains elements"),
                    "Precondition must not contain natural language type constraint: " + pre);
        }
        // Should generate src != null for the wildcard-bounded parameter
        assertTrue(spec.getPreconditions().stream().anyMatch(p -> p.contains("src != null")),
                "Expected src != null for wildcard-bounded parameter, got: " + spec.getPreconditions());
    }
}
