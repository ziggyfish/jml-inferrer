package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

class MatrixTraceProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: matrixTrace with hand-crafted JML")
    void matrixTraceProbe() throws IOException {
        String source = """
                public class Matrix4 {
                    /*@ spec_public @*/ private int[][] data;
                    /*@ spec_public @*/ private int size;

                    //@ requires data != null && size >= 0 && size <= data.length;
                    //@ requires (\\forall int k; 0 <= k && k < size; data[k] != null && k < data[k].length);
                    //@ requires (\\forall int k; 0 <= k && k < size; data[k][k] >= -1000 && data[k][k] <= 1000);
                    //@ requires size <= 1000000;
                    //@ ensures \\result == (\\sum int k; 0 <= k && k < size; data[k][k]);
                    //@ assignable \\nothing;
                    public int trace() {
                        int sum = 0;
                        //@ loop_invariant 0 <= i && i <= size;
                        //@ loop_invariant -1000 * i <= sum && sum <= 1000 * i;
                        //@ loop_invariant sum == (\\sum int k; 0 <= k && k < i; data[k][k]);
                        //@ decreases size - i;
                        for (int i = 0; i < size; i++) {
                            sum += data[i][i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "Matrix4", "trace"));
    }
}
