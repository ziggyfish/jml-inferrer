package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for complex control flow: nested branches, switch statements,
 * multiple returns, exception paths, and interleaved loops/conditions.
 */
class ComplexControlFlowVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Nested conditionals
    // =========================================================================

    @Test
    @DisplayName("Triple-nested if with field updates at each level")
    void tripleNestedIf() throws IOException {
        String source = """
                public class TripleNested {
                    private int level;
                    public void process(int a, int b, int c) {
                        if (a > 0) {
                            level = 1;
                            if (b > 0) {
                                level = 2;
                                if (c > 0) {
                                    level = 3;
                                }
                            }
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TripleNested", "process"));
    }

    @Test
    @DisplayName("If-else chain with different return types per branch")
    void ifElseChain() throws IOException {
        String source = """
                public class IfElseChain {
                    public String classify(int score) {
                        if (score < 0) throw new IllegalArgumentException();
                        if (score >= 90) return "A";
                        else if (score >= 80) return "B";
                        else if (score >= 70) return "C";
                        else if (score >= 60) return "D";
                        else return "F";
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "IfElseChain", "classify"));
    }

    @Test
    @DisplayName("Nested ternary expressions")
    void nestedTernary() throws IOException {
        String source = """
                public class NestedTernary {
                    public int clamp(int value, int min, int max) {
                        return value < min ? min : (value > max ? max : value);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NestedTernary", "clamp"));
    }

    @Test
    @DisplayName("Guard clause cascade: multiple throws")
    void guardClauseCascade() throws IOException {
        String source = """
                public class GuardCascade {
                    public double divide(double a, double b) {
                        if (Double.isNaN(a)) throw new IllegalArgumentException();
                        if (Double.isNaN(b)) throw new IllegalArgumentException();
                        if (b == 0.0) throw new ArithmeticException();
                        return a / b;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "GuardCascade", "divide"));
    }

    // =========================================================================
    // Switch statements
    // =========================================================================

    @Test
    @DisplayName("Switch with return per case")
    void switchWithReturns() throws IOException {
        String source = """
                public class SwitchReturn {
                    public int daysInMonth(int month) {
                        switch (month) {
                            case 2: return 28;
                            case 4: case 6: case 9: case 11: return 30;
                            default: return 31;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchReturn", "daysInMonth"));
    }

    @Test
    @DisplayName("Switch with field assignment per case")
    void switchWithFieldAssignment() throws IOException {
        String source = """
                public class SwitchField {
                    private int priority;
                    public void setPriority(String level) {
                        if (level == null) throw new IllegalArgumentException();
                        switch (level) {
                            case "HIGH":
                                priority = 3;
                                break;
                            case "MEDIUM":
                                priority = 2;
                                break;
                            case "LOW":
                                priority = 1;
                                break;
                            default:
                                priority = 0;
                                break;
                        }
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchField", "setPriority"));
    }

    @Test
    @DisplayName("Switch expression (Java 14+)")
    void switchExpression() throws IOException {
        String source = """
                public class SwitchExpr {
                    public String toRoman(int digit) {
                        if (digit < 1 || digit > 9) throw new IllegalArgumentException();
                        return switch (digit) {
                            case 1 -> "I";
                            case 2 -> "II";
                            case 3 -> "III";
                            case 4 -> "IV";
                            case 5 -> "V";
                            case 6 -> "VI";
                            case 7 -> "VII";
                            case 8 -> "VIII";
                            case 9 -> "IX";
                            default -> throw new IllegalArgumentException();
                        };
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "SwitchExpr", "toRoman"));
    }

    // =========================================================================
    // Multiple return paths
    // =========================================================================

    @Test
    @DisplayName("Early return with null checks and computation")
    void earlyReturnWithComputation() throws IOException {
        String source = """
                public class EarlyReturn {
                    public int safeArraySum(int[] arr) {
                        if (arr == null) return 0;
                        if (arr.length == 0) return 0;
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "EarlyReturn", "safeArraySum"));
    }

    @Test
    @DisplayName("Multiple return paths with boolean conditions")
    void multipleReturnPaths() throws IOException {
        String source = """
                public class MultiReturn {
                    public boolean isValidAge(int age) {
                        if (age < 0) return false;
                        if (age > 150) return false;
                        return true;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "MultiReturn", "isValidAge"));
    }

    @Test
    @DisplayName("Return from nested loop with flag")
    void returnFromNestedLoop() throws IOException {
        String source = """
                public class NestedLoopReturn {
                    public boolean contains2D(int[][] matrix, int target) {
                        if (matrix == null) throw new IllegalArgumentException();
                        for (int i = 0; i < matrix.length; i++) {
                            if (matrix[i] == null) continue;
                            for (int j = 0; j < matrix[i].length; j++) {
                                if (matrix[i][j] == target) return true;
                            }
                        }
                        return false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "NestedLoopReturn", "contains2D"));
    }

    // =========================================================================
    // Loop with complex conditions
    // =========================================================================

    @Test
    @DisplayName("While loop with compound exit condition")
    void compoundExitCondition() throws IOException {
        String source = """
                public class CompoundExit {
                    public int findOrExhaust(int[] arr, int target, int maxSteps) {
                        if (arr == null) throw new IllegalArgumentException();
                        int i = 0;
                        int steps = 0;
                        while (i < arr.length && steps < maxSteps) {
                            if (arr[i] == target) return i;
                            i++;
                            steps++;
                        }
                        return -1;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CompoundExit", "findOrExhaust"));
    }

    @Test
    @DisplayName("Do-while loop pattern")
    void doWhileLoop() throws IOException {
        String source = """
                public class DoWhilePattern {
                    public int countDigits(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        if (n == 0) return 1;
                        int count = 0;
                        int num = n;
                        while (num > 0) {
                            num /= 10;
                            count++;
                        }
                        return count;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "DoWhilePattern", "countDigits"));
    }

    @Test
    @DisplayName("Loop with break and continue")
    void loopBreakContinue() throws IOException {
        String source = """
                public class BreakContinue {
                    public int sumPositiveUntilNeg(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int sum = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] < 0) break;
                            if (arr[i] == 0) continue;
                            sum += arr[i];
                        }
                        return sum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "BreakContinue", "sumPositiveUntilNeg"));
    }

    // =========================================================================
    // Mixed control flow and state
    // =========================================================================

    @Test
    @DisplayName("State machine with enum-like int states")
    void stateMachine() throws IOException {
        String source = """
                public class StateMachine {
                    private int state;
                    public static final int IDLE = 0;
                    public static final int RUNNING = 1;
                    public static final int STOPPED = 2;
                    public boolean transition(int event) {
                        if (state == IDLE && event == 1) {
                            state = RUNNING;
                            return true;
                        } else if (state == RUNNING && event == 2) {
                            state = STOPPED;
                            return true;
                        } else if (state == STOPPED && event == 0) {
                            state = IDLE;
                            return true;
                        }
                        return false;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "StateMachine", "transition"));
    }

    @Test
    @DisplayName("Validate and transform: guard + loop + field update")
    void validateAndTransform() throws IOException {
        String source = """
                public class ValidateTransform {
                    private int processedCount;
                    public int processAll(int[] data) {
                        if (data == null) throw new IllegalArgumentException();
                        if (data.length == 0) throw new IllegalArgumentException();
                        int total = 0;
                        for (int i = 0; i < data.length; i++) {
                            if (data[i] < 0) {
                                data[i] = 0;
                            }
                            total += data[i];
                        }
                        processedCount += data.length;
                        return total;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "ValidateTransform", "processAll"));
    }

    @Test
    @DisplayName("Two-phase processing: count then allocate")
    void twoPhaseProcessing() throws IOException {
        String source = """
                public class TwoPhase {
                    public int[] filterPositive(int[] arr) {
                        if (arr == null) throw new IllegalArgumentException();
                        int count = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) count++;
                        }
                        int[] result = new int[count];
                        int idx = 0;
                        for (int i = 0; i < arr.length; i++) {
                            if (arr[i] > 0) {
                                result[idx] = arr[i];
                                idx++;
                            }
                        }
                        return result;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TwoPhase", "filterPositive"));
    }

    @Test
    @DisplayName("Accumulator with conditional reset")
    void accumulatorWithReset() throws IOException {
        String source = """
                public class AccReset {
                    public int maxConsecutiveSum(int[] arr) {
                        if (arr == null || arr.length == 0) throw new IllegalArgumentException();
                        int maxSum = arr[0];
                        int currentSum = arr[0];
                        for (int i = 1; i < arr.length; i++) {
                            if (currentSum < 0) {
                                currentSum = arr[i];
                            } else {
                                currentSum += arr[i];
                            }
                            if (currentSum > maxSum) {
                                maxSum = currentSum;
                            }
                        }
                        return maxSum;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "AccReset", "maxConsecutiveSum"));
    }

    // =========================================================================
    // Exception handling patterns
    // =========================================================================

    @Test
    @DisplayName("Try-catch with resource cleanup simulation")
    void tryCatchCleanup() throws IOException {
        String source = """
                public class TryCatch {
                    private boolean resourceOpen;
                    public int safeRead(int[] data, int index) {
                        if (data == null) throw new IllegalArgumentException();
                        if (index < 0 || index >= data.length) throw new IndexOutOfBoundsException();
                        return data[index];
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "TryCatch", "safeRead"));
    }

    @Test
    @DisplayName("Cascaded validation with specific exceptions")
    void cascadedValidation() throws IOException {
        String source = """
                public class CascadedVal {
                    public void validate(String name, int age, String email) {
                        if (name == null) throw new IllegalArgumentException("name null");
                        if (name.isEmpty()) throw new IllegalArgumentException("name empty");
                        if (age < 0) throw new IllegalArgumentException("negative age");
                        if (age > 200) throw new IllegalArgumentException("unrealistic age");
                        if (email == null) throw new IllegalArgumentException("email null");
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "CascadedVal", "validate"));
    }

    // =========================================================================
    // Complex arithmetic with multiple variables
    // =========================================================================

    @Test
    @DisplayName("Polynomial evaluation: ax^2 + bx + c")
    void polynomialEval() throws IOException {
        String source = """
                public class Polynomial {
                    public double evaluate(double a, double b, double c, double x) {
                        return a * x * x + b * x + c;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Polynomial", "evaluate"));
    }

    @Test
    @DisplayName("Weighted average of three values")
    void weightedAverage() throws IOException {
        String source = """
                public class WeightedAvg {
                    public double weightedAverage(double v1, double w1, double v2, double w2, double v3, double w3) {
                        double totalWeight = w1 + w2 + w3;
                        if (totalWeight == 0.0) throw new ArithmeticException();
                        return (v1 * w1 + v2 * w2 + v3 * w3) / totalWeight;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "WeightedAvg", "weightedAverage"));
    }

    @Test
    @DisplayName("Manhattan distance between two points")
    void manhattanDistance() throws IOException {
        String source = """
                public class Manhattan {
                    public int distance(int x1, int y1, int x2, int y2) {
                        int dx = x1 - x2;
                        int dy = y1 - y2;
                        return (dx < 0 ? -dx : dx) + (dy < 0 ? -dy : dy);
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Manhattan", "distance"));
    }

    @Test
    @DisplayName("Interpolation: linear lerp")
    void linearInterpolation() throws IOException {
        String source = """
                public class Lerp {
                    public double lerp(double a, double b, double t) {
                        if (t < 0.0 || t > 1.0) throw new IllegalArgumentException();
                        return a + (b - a) * t;
                    }
                }
                """;
        assertVerified(inferAndVerify(source, "Lerp", "lerp"));
    }
}
