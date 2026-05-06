package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

class GrowByProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: LoopIncrementsField.growBy with hand-crafted JML")
    void growByProbe() throws IOException {
        String source = """
                public class LoopIncrementsField {
                    //@ public invariant size >= 0;
                    /*@ spec_public @*/ int size;

                    //@ requires n >= 0;
                    //@ requires (\\bigint)this.size + n <= Integer.MAX_VALUE;
                    //@ ensures this.size == \\old(this.size) + n;
                    //@ assignable this.size;
                    public void growBy(int n) {
                        //@ loop_invariant 0 <= i && i <= n;
                        //@ loop_invariant this.size == \\old(this.size) + i;
                        //@ decreases n - i;
                        for (int i = 0; i < n; i++) {
                            this.size++;
                        }
                    }
                }
                """;
        assertVerified(verifyMethod(source, "LoopIncrementsField", "growBy"));
    }
}
