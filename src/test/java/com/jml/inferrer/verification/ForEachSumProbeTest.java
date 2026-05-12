package com.jml.inferrer.verification;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Probe for {@code RegressionVerificationTest#forEachIterableNullCheck} (the
 * 1-remaining regression failure identified in session_2026_05_08).
 *
 * <p><b>Finding (2026-05-12):</b> the for-each accumulator pattern
 * {@code for (int val : arr) total += val} cannot be discharged purely through
 * user-level JML loop invariants under OpenJML's iterator-based for-each
 * translation. The remaining failures are:
 * <ul>
 *   <li>ArithmeticOperationRange (overflow/underflow on {@code total += val})
 *   <li>Postcondition ({@code \result == \sum arr[k]})
 * </ul>
 *
 * <p>Root cause: in OpenJML's for-each translation the loop variable {@code val}
 * is bound from {@code arr[<iter-index>]}, but the relationship
 * {@code val == arr[\count]} is internal to the translation and is not
 * expressible in user JML (probed variants tested below). Loop invariants
 * involving {@code \count} alone verify cleanly (the implicit counter is
 * accessible), but the prover lacks the element-bound link to {@code val}
 * required to discharge the body's per-step overflow check.
 *
 * <p>Generalisability under {@code feedback_ai_probe_workflow.md} step 8:
 * <b>Low</b>. The limit is OpenJML's for-each translation, not a missing
 * inferrer heuristic. Per workflow rule, the inferrer is not extended for
 * Low-generalisability cases.
 *
 * <p>The probe below is left disabled as a research artefact documenting the
 * limit. A future tractable path is to rewrite the for-each source to an
 * indexed for-loop in a pre-inference transformer, which would let the
 * inferrer's existing array-accumulator heuristics apply; that transform is a
 * separate (and larger) piece of work.
 */
class ForEachSumProbeTest extends FormalVerificationTestBase {

    @Test
    @Disabled("Known OpenJML for-each structural limit — see class Javadoc")
    @DisplayName("Probe: ForEachSum.sumArray — disabled, OpenJML for-each limit")
    void forEachSumProbe() throws IOException {
        String source = """
                class ForEachSum {
                    //@ requires arr != null;
                    //@ requires (\\forall int k; 0 <= k && k < arr.length; arr[k] >= -1000 && arr[k] <= 1000);
                    //@ requires arr.length <= 1000000;
                    //@ ensures \\result == (\\sum int k; 0 <= k && k < arr.length; arr[k]);
                    //@ assignable \\nothing;
                    /*@ pure @*/
                    int sumArray(int[] arr) {
                        int total = 0;
                        //@ loop_invariant arr != null;
                        //@ loop_invariant 0 <= \\count && \\count <= arr.length;
                        //@ loop_invariant -1000 * \\count <= total && total <= 1000 * \\count;
                        //@ loop_invariant total == (\\sum int k; 0 <= k && k < \\count; arr[k]);
                        for (int val : arr) {
                            total += val;
                        }
                        return total;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "ForEachSum", "sumArray"));
    }
}
