package com.jml.inferrer.verification;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Probe for {@code DesignPatternVerificationTest#scaleArray}
 * (ArrayOps.scale: {@code arr[i] *= factor} mutating-array loop).
 *
 * <p><b>Finding (2026-05-12, iter 4):</b> the array-mutation overflow check is
 * not dischargeable under OpenJML/Z3 at the inferrer's strictness configuration.
 * Three formulations were probed, each ran into a 240s Z3 broken-pipe timeout:
 * <ol>
 *   <li>forall-loop-invariant carry-over of the product-bound over the
 *       unprocessed range ({@code i <= k < arr.length});
 *   <li>literal-bounded factor + element forall + element-only loop_invariant;
 *   <li>maximally constrained {@code factor in {-1, 0, 1}} + {@code arr.length <= 1000}.
 * </ol>
 *
 * <p>The common factor is {@code assignable arr[*]} combined with any
 * quantified loop invariant: Z3's array theory cannot finish the inductive
 * step within the per-test timeout. This is the same class of limit recorded
 * for the matrix data-structure cases in {@code session_2026_05_08.md}.
 *
 * <p>Generalisability under {@code feedback_ai_probe_workflow.md} step 8:
 * <b>Low</b>. Z3's limit, not a missing inferrer heuristic. Per workflow rule
 * the inferrer is not extended.
 *
 * <p>Tractable future paths: emit a narrower {@code assignable arr[0..i-1]}
 * frame condition (would let the prover preserve the unprocessed-range
 * forall without re-checking it), or rewrite the mutating loop as a fresh-array
 * loop in a pre-inference transformer. Both are larger pieces of work outside
 * this probe-and-extend cycle.
 */
class ScaleArrayProbeTest extends FormalVerificationTestBase {

    @Test
    @Disabled("Known OpenJML/Z3 limit on assignable arr[*] + quantified loop invariant — see class Javadoc")
    @DisplayName("Probe: ArrayOps.scale — disabled, Z3 quantified-mutation limit")
    void scaleArrayProbe() throws IOException {
        String source = """
                public class ArrayOps {
                    //@ requires arr != null;
                    //@ requires (\\forall int k; 0 <= k && k < arr.length; ((\\bigint) arr[k] * (\\bigint) factor) >= Integer.MIN_VALUE);
                    //@ requires (\\forall int k; 0 <= k && k < arr.length; ((\\bigint) arr[k] * (\\bigint) factor) <= Integer.MAX_VALUE);
                    //@ assignable arr[*];
                    public void scale(int[] arr, int factor) {
                        if (arr == null) throw new IllegalArgumentException();
                        //@ loop_invariant 0 <= i && i <= arr.length;
                        //@ loop_invariant (\\forall int k; i <= k && k < arr.length; ((\\bigint) arr[k] * (\\bigint) factor) >= Integer.MIN_VALUE);
                        //@ loop_invariant (\\forall int k; i <= k && k < arr.length; ((\\bigint) arr[k] * (\\bigint) factor) <= Integer.MAX_VALUE);
                        //@ decreases arr.length - i;
                        for (int i = 0; i < arr.length; i++) {
                            arr[i] *= factor;
                        }
                    }
                }
                """;
        assertVerified(verifyMethod(source, "ArrayOps", "scale"));
    }
}
