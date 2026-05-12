package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Probe for {@code InterproceduralVerificationTest#delegateToHelper}
 * (Delegator1.sumOfSquares). The inferrer emits correct preconditions for the
 * callee {@code square} but does not propagate them to the caller. The caller
 * also needs an overflow guard for {@code square(a) + square(b)}.
 *
 * <p>This probe writes the verified JML by hand and confirms OpenJML accepts
 * it. The inferrer-extension step then encodes the propagated preconditions as
 * a heuristic.
 */
class SumOfSquaresProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: Delegator1.sumOfSquares — propagated callee preconditions")
    void sumOfSquaresProbe() throws IOException {
        String source = """
                public class Delegator1 {
                    //@ requires ((\\bigint) x * (\\bigint) x) >= Integer.MIN_VALUE;
                    //@ requires ((\\bigint) x * (\\bigint) x) <= Integer.MAX_VALUE;
                    //@ ensures \\result == x * x;
                    //@ assignable \\nothing;
                    /*@ pure @*/
                    /*@ spec_public @*/ private int square(int x) {
                        return x * x;
                    }

                    //@ requires ((\\bigint) a * (\\bigint) a) >= Integer.MIN_VALUE;
                    //@ requires ((\\bigint) a * (\\bigint) a) <= Integer.MAX_VALUE;
                    //@ requires ((\\bigint) b * (\\bigint) b) >= Integer.MIN_VALUE;
                    //@ requires ((\\bigint) b * (\\bigint) b) <= Integer.MAX_VALUE;
                    //@ requires ((\\bigint) a * (\\bigint) a + (\\bigint) b * (\\bigint) b) <= Integer.MAX_VALUE;
                    //@ requires ((\\bigint) a * (\\bigint) a + (\\bigint) b * (\\bigint) b) >= Integer.MIN_VALUE;
                    //@ ensures \\result == square(a) + square(b);
                    //@ assignable \\nothing;
                    /*@ pure @*/
                    public int sumOfSquares(int a, int b) {
                        return square(a) + square(b);
                    }
                }
                """;
        assertVerified(verifyMethod(source, "Delegator1", "sumOfSquares"));
    }
}
