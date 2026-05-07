package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

class FieldAccumProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: FieldAccum.getValue with substituted-runtime preconditions")
    void fieldAccumProbe() throws IOException {
        // The body of getValue:
        //   a = a * a;       // a' = a*a
        //   c += 3;          // c' = c + 3
        //   c += 3;          // c'' = c + 6
        //   int b = a + c;   // b = (a*a) + (c+6)
        //   b = b * b;       // b' = ((a*a) + (c+6))^2
        //   return b;
        // Preconditions need to bound the RUNTIME values (which require substituting
        // forward through assignments), not the syntactic operands.
        String source = """
                public class FieldAccum {
                    //@ public invariant c >= 0;
                    /*@ spec_public @*/ int c;

                    //@ requires ((\\bigint)a * a) >= Integer.MIN_VALUE
                    //@      && ((\\bigint)a * a) <= Integer.MAX_VALUE;
                    //@ requires ((\\bigint)this.c + 6) <= Integer.MAX_VALUE;
                    //@ requires ((\\bigint)((\\bigint)a * a) + ((\\bigint)this.c + 6)) >= Integer.MIN_VALUE
                    //@      && ((\\bigint)((\\bigint)a * a) + ((\\bigint)this.c + 6)) <= Integer.MAX_VALUE;
                    //@ requires ((\\bigint)((\\bigint)a * a + ((\\bigint)this.c + 6)) * ((\\bigint)a * a + ((\\bigint)this.c + 6))) >= Integer.MIN_VALUE
                    //@      && ((\\bigint)((\\bigint)a * a + ((\\bigint)this.c + 6)) * ((\\bigint)a * a + ((\\bigint)this.c + 6))) <= Integer.MAX_VALUE;
                    //@ ensures \\result == (((a * a) + ((\\old(this.c) + 3) + 3)) * ((a * a) + ((\\old(this.c) + 3) + 3)));
                    //@ ensures this.c == \\old(this.c) + 6;
                    //@ assignable this.c;
                    public int getValue(int a) {
                        a = a * a;
                        c += 3;
                        c += 3;
                        int b = a + c;
                        b = b * b;
                        return b;
                    }
                }
                """;
        assertVerified(verifyMethod(source, "FieldAccum", "getValue"));
    }
}
