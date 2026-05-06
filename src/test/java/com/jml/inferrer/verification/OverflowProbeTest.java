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

    @Test
    @DisplayName("Probe: PrefixSum with linear element bound + length cap")
    void prefixSumProbe() throws IOException {
        String source = """
                public class PrefixSum {
                    //@ requires arr != null;
                    //@ requires arr.length <= 1000000;
                    //@ requires (\\forall int k; 0 <= k && k < arr.length; arr[k] >= -1000 && arr[k] <= 1000);
                    //@ ensures \\result != null && \\result.length == arr.length;
                    //@ assignable \\nothing;
                    public int[] computePrefixSum(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int[] prefix = new int[arr.length];
                        if (arr.length == 0) return prefix;
                        prefix[0] = arr[0];
                        //@ loop_invariant 1 <= i && i <= arr.length;
                        //@ loop_invariant (\\forall int k; 0 <= k && k < i; -1000 * (k + 1) <= prefix[k] && prefix[k] <= 1000 * (k + 1));
                        //@ decreases arr.length - i;
                        for (int i = 1; i < arr.length; i++) {
                            prefix[i] = prefix[i - 1] + arr[i];
                        }
                        return prefix;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "PrefixSum", "computePrefixSum"));
    }
}
