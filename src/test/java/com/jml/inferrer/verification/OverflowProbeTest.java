package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

class OverflowProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: SumToN with quadratic bound on n")
    void sumToProbe() throws IOException {
        String source = """
                public class SumToN {
                    //@ requires n >= 0;
                    //@ requires (\\bigint)n * (n + 1) / 2 <= Integer.MAX_VALUE;
                    //@ ensures \\result == (\\sum int k; 0 <= k && k < n; k);
                    //@ assignable \\nothing;
                    public int sumTo(int n) {
                        int total = 0;
                        //@ loop_invariant 0 <= i && i <= n;
                        //@ loop_invariant total == (\\sum int k; 0 <= k && k < i; k);
                        //@ loop_invariant total >= 0;
                        //@ loop_invariant (\\bigint)total <= (\\bigint)i * (i - 1) / 2;
                        //@ decreases n - i;
                        for (int i = 0; i < n; i++) {
                            total += i;
                        }
                        return total;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "SumToN", "sumTo"));
    }

    @Test
    @DisplayName("Probe: TripleNestedLoop.countTriple with multiplicative bound")
    void tripleNestedLoopProbe() throws IOException {
        String source = """
                public class TripleNestedLoop {
                    //@ requires 0 <= x && 0 <= y && 0 <= z;
                    //@ requires (\\bigint)x * y * z <= Integer.MAX_VALUE;
                    //@ ensures \\result == x * y * z;
                    //@ assignable \\nothing;
                    public int countTriple(int x, int y, int z) {
                        int count = 0;
                        //@ loop_invariant 0 <= i && i <= x;
                        //@ loop_invariant count == i * y * z;
                        //@ loop_invariant (\\bigint)count <= (\\bigint)i * y * z;
                        //@ decreases x - i;
                        for (int i = 0; i < x; i++) {
                            //@ loop_invariant 0 <= j && j <= y;
                            //@ loop_invariant count == i * y * z + j * z;
                            //@ decreases y - j;
                            for (int j = 0; j < y; j++) {
                                //@ loop_invariant 0 <= k && k <= z;
                                //@ loop_invariant count == i * y * z + j * z + k;
                                //@ decreases z - k;
                                for (int k = 0; k < z; k++) {
                                    count++;
                                }
                            }
                        }
                        return count;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "TripleNestedLoop", "countTriple"));
    }

    // PrefixSum probe was attempted with a per-index linear bound
    // `(\forall int k; 0 <= k < i; -K_HI * (k+1) <= prefix[k] && prefix[k] <= K_HI * (k+1))`
    // which is sound but Z3 times out at 240s — the forall over a quadratically-
    // growing-bound array is the structural blocker. A constant `K_HI * arr.length`
    // bound discharges faster but doesn't preserve under the body's `prefix[i] =
    // prefix[i-1] + arr[i]` (which can push prefix[i] just past the bound).
    // Removed pending a formulation that fits in the solver's budget.
}
