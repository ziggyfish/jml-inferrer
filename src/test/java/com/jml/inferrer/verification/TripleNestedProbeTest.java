package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

class TripleNestedProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: countTriple with multiplicative invariant")
    void countTripleProbe() throws IOException {
        String source = """
                public class TripleNestedLoop {
                    //@ requires x >= 0 && y >= 0 && z >= 0;
                    //@ requires (\\bigint) x * y * z <= Integer.MAX_VALUE;
                    //@ ensures \\result == (\\bigint) x * y * z;
                    //@ assignable \\nothing;
                    public int countTriple(int x, int y, int z) {
                        int count = 0;
                        //@ loop_invariant 0 <= i && i <= x;
                        //@ loop_invariant count == (\\bigint) i * y * z;
                        //@ decreases x - i;
                        for (int i = 0; i < x; i++) {
                            //@ loop_invariant 0 <= j && j <= y;
                            //@ loop_invariant count == (\\bigint) i * y * z + (\\bigint) j * z;
                            //@ decreases y - j;
                            for (int j = 0; j < y; j++) {
                                //@ loop_invariant 0 <= k && k <= z;
                                //@ loop_invariant count == (\\bigint) i * y * z + (\\bigint) j * z + k;
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
}
