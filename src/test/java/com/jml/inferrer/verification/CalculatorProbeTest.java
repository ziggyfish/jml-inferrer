package com.jml.inferrer.verification;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Probe for {@code DesignPatternVerificationTest#computeDispatch}
 * (Calculator.compute). Baseline timeout ~180s on rich-precondition-set Z3
 * blow-up. This probe tests whether guarded preconditions
 * ({@code op == 0 ==> ...}) reduce Z3's per-branch obligation enough to verify.
 */
class CalculatorProbeTest extends FormalVerificationTestBase {

    @Test
    @DisplayName("Probe: Calculator.compute — branch-guarded overflow preconditions")
    void calculatorGuardedProbe() throws IOException {
        String source = """
                public class Calculator {
                    //@ requires op == 0 || op == 1 || op == 2 || op == 3;
                    //@ requires op == 0 ==> ((\\bigint) a + (\\bigint) b) >= Integer.MIN_VALUE;
                    //@ requires op == 0 ==> ((\\bigint) a + (\\bigint) b) <= Integer.MAX_VALUE;
                    //@ requires op == 1 ==> ((\\bigint) a - (\\bigint) b) >= Integer.MIN_VALUE;
                    //@ requires op == 1 ==> ((\\bigint) a - (\\bigint) b) <= Integer.MAX_VALUE;
                    //@ requires op == 2 ==> ((\\bigint) a * (\\bigint) b) >= Integer.MIN_VALUE;
                    //@ requires op == 2 ==> ((\\bigint) a * (\\bigint) b) <= Integer.MAX_VALUE;
                    //@ requires op == 3 ==> (a != Integer.MIN_VALUE || b != -1);
                    //@ ensures op == 0 ==> \\result == a + b;
                    //@ ensures op == 1 ==> \\result == a - b;
                    //@ ensures op == 2 ==> \\result == a * b;
                    //@ ensures op == 3 && b != 0 ==> \\result == a / b;
                    //@ assignable \\nothing;
                    //@ signals (ArithmeticException e) op == 3 && b == 0;
                    //@ signals (IllegalArgumentException e) true;
                    /*@ pure @*/
                    public int compute(int a, int b, int op) {
                        if (op == 0) return a + b;
                        if (op == 1) return a - b;
                        if (op == 2) return a * b;
                        if (op == 3) {
                            if (b == 0) throw new ArithmeticException();
                            return a / b;
                        }
                        throw new IllegalArgumentException();
                    }
                }
                """;
        assertVerified(verifyMethod(source, "Calculator", "compute"));
    }
}
