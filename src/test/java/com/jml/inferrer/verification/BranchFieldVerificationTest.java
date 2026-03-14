package com.jml.inferrer.verification;

import com.jml.inferrer.validation.MethodVerificationResult;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * Verification tests for methods where a class field is assigned on only
 * one branch of a conditional. These exercise the full inference pipeline
 * (infer → annotate → convert → OpenJML ESC).
 *
 * Common bugs exposed:
 * - Unconditional postconditions for branch-only field writes
 * - Contradictory postconditions from different branches
 * - Spurious preconditions from branch conditions
 * - Missing conditional guards on field modification postconditions
 */
@DisplayName("Branch Field Assignment Verification")
class BranchFieldVerificationTest extends FormalVerificationTestBase {

    // =========================================================================
    // Field assigned on then-branch only
    // =========================================================================

    @Test
    @DisplayName("Field increment on then-branch only: postcondition must be conditional")
    void fieldIncrementThenBranchOnly() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class MaybeIncrement {
                int count;
                void maybeIncrement(boolean flag) {
                    if (flag) {
                        count++;
                    }
                }
            }
            """, "MaybeIncrement", "maybeIncrement");
        assertVerified(result);
    }

    @Test
    @DisplayName("Field set on then-branch only: postcondition must be conditional")
    void fieldSetThenBranchOnly() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class MaybeSet {
                int value;
                void setIfPositive(int x) {
                    if (x > 0) {
                        value = x;
                    }
                }
            }
            """, "MaybeSet", "setIfPositive");
        assertVerified(result);
    }

    // =========================================================================
    // Field assigned on else-branch only
    // =========================================================================

    @Test
    @DisplayName("Field set on else-branch only: no spurious precondition")
    void fieldSetElseBranchOnly() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class ElseSet {
                int value;
                void setIfNegative(int x) {
                    if (x >= 0) {
                        // do nothing
                    } else {
                        value = -x;
                    }
                }
            }
            """, "ElseSet", "setIfNegative");
        assertVerified(result);
    }

    // =========================================================================
    // Field assigned different values per branch
    // =========================================================================

    @Test
    @DisplayName("Field assigned different values per branch: no contradictory postconditions")
    void fieldDifferentValuesPerBranch() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class StatusUpdate {
                int status;
                void update(boolean success) {
                    if (success) {
                        status = 1;
                    } else {
                        status = -1;
                    }
                }
            }
            """, "StatusUpdate", "update");
        assertVerified(result);
    }

    @Test
    @DisplayName("Field assigned 0 or 1: postconditions must not contradict")
    void fieldZeroOrOne() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Toggle {
                int flag;
                void setFlag(boolean on) {
                    if (on) {
                        flag = 1;
                    } else {
                        flag = 0;
                    }
                }
            }
            """, "Toggle", "setFlag");
        assertVerified(result);
    }

    // =========================================================================
    // Guard clause with field modification and return
    // =========================================================================

    @Test
    @DisplayName("Guard clause with field increment: no spurious precondition from guard")
    void guardClauseFieldIncrement() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class ErrorCounter {
                int errorCount;
                int process(int input) {
                    if (input < 0) {
                        errorCount++;
                        return -1;
                    }
                    return input * 2;
                }
            }
            """, "ErrorCounter", "process");
        assertVerified(result);
    }

    @Test
    @DisplayName("Guard clause with field set and early return")
    void guardClauseFieldSet() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Validator {
                int lastError;
                boolean validate(int code) {
                    if (code < 0) {
                        lastError = code;
                        return false;
                    }
                    return true;
                }
            }
            """, "Validator", "validate");
        assertVerified(result);
    }

    // =========================================================================
    // Null check guarding field assignment
    // =========================================================================

    @Test
    @DisplayName("Null check guarding field set: no spurious non-null precondition")
    void nullCheckGuardFieldSet() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class NameSetter {
                String name;
                void setNameIfNotNull(String n) {
                    if (n != null) {
                        name = n;
                    }
                }
            }
            """, "NameSetter", "setNameIfNotNull");
        assertVerified(result);
    }

    // =========================================================================
    // Nested branches with field assignment
    // =========================================================================

    @Test
    @DisplayName("Nested branches assigning field: no spurious preconditions, conditional postconditions")
    void nestedBranchFieldAssign() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Promoter {
                int level;
                void promote(int score) {
                    if (score > 100) {
                        if (score > 200) {
                            level = 3;
                        } else {
                            level = 2;
                        }
                    }
                }
            }
            """, "Promoter", "promote");
        assertVerified(result);
    }

    // =========================================================================
    // Multiple fields on one branch only
    // =========================================================================

    @Test
    @DisplayName("Multiple fields reset on one branch: postconditions must be conditional")
    void multipleFieldsOneBranch() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class MultiReset {
                int x;
                int y;
                void resetIfZero(int val) {
                    if (val == 0) {
                        x = 0;
                        y = 0;
                    }
                }
            }
            """, "MultiReset", "resetIfZero");
        assertVerified(result);
    }

    // =========================================================================
    // Field increment on one branch, return value from both
    // =========================================================================

    @Test
    @DisplayName("Field increment on one branch with return from both branches")
    void fieldIncrementOneBranchReturnBoth() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Accumulator {
                int total;
                int addIfPositive(int x) {
                    if (x > 0) {
                        total += x;
                        return total;
                    } else {
                        return 0;
                    }
                }
            }
            """, "Accumulator", "addIfPositive");
        assertVerified(result);
    }

    // =========================================================================
    // Boolean field toggled on one branch
    // =========================================================================

    @Test
    @DisplayName("Boolean-like field toggled conditionally")
    void booleanFieldConditionalToggle() throws IOException {
        MethodVerificationResult result = inferAndVerify("""
            class Switch {
                int active;
                void activateIf(boolean condition) {
                    if (condition) {
                        active = 1;
                    }
                }
            }
            """, "Switch", "activateIf");
        assertVerified(result);
    }
}
