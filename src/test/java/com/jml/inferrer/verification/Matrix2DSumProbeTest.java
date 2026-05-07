package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

class Matrix2DSumProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: 1D-row-major sumMatrix with hand-crafted JML")
    void sumMatrixProbe() throws IOException {
        String source = """
                public class NestedLoop2DArray {
                    //@ requires matrix != null;
                    //@ requires rows >= 0 && cols >= 0;
                    //@ requires (\\bigint) rows * cols <= matrix.length;
                    //@ requires (\\bigint) rows * cols <= 1000000;
                    //@ requires (\\forall int k; 0 <= k && k < matrix.length; matrix[k] >= -1000 && matrix[k] <= 1000);
                    //@ ensures \\result == (\\sum int k; 0 <= k && k < rows * cols; matrix[k]);
                    //@ assignable \\nothing;
                    public int sumMatrix(int[] matrix, int rows, int cols) {
                        int sum = 0;
                        //@ loop_invariant 0 <= i && i <= rows;
                        //@ loop_invariant (\\bigint) i * cols <= (\\bigint) rows * cols;
                        //@ loop_invariant (\\bigint) i * cols <= matrix.length;
                        //@ loop_invariant -1000 * (\\bigint) i * cols <= sum && sum <= 1000 * (\\bigint) i * cols;
                        //@ loop_invariant sum == (\\sum int k; 0 <= k && k < i * cols; matrix[k]);
                        //@ decreases rows - i;
                        for (int i = 0; i < rows; i++) {
                            //@ loop_invariant 0 <= j && j <= cols;
                            //@ loop_invariant (\\bigint) i * cols + j <= matrix.length;
                            //@ loop_invariant -1000 * ((\\bigint) i * cols + j) <= sum && sum <= 1000 * ((\\bigint) i * cols + j);
                            //@ loop_invariant sum == (\\sum int k; 0 <= k && k < i * cols + j; matrix[k]);
                            //@ decreases cols - j;
                            for (int j = 0; j < cols; j++) {
                                sum += matrix[i * cols + j];
                            }
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "NestedLoop2DArray", "sumMatrix"));
    }
}
