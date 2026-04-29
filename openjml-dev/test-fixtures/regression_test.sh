#!/bin/bash
# Regression-test the fixtures against the just-built openjml-smoke image.
# Reports pass/fail and timing for each.  Used by the 2026-04-29 z3 flag
# tuning campaign to confirm the patch_z3_flags.py changes don't regress
# the existing test set.
#
# Usage: bash regression_test.sh [timeout_sec]

TIMEOUT=${1:-90}
FIXTURES=(
    PureCongruenceTest
    PureCongruenceTest2
    ArrayCongruenceTest
    Recursive1
    Recursive2
    Recursive5
    PowerPrecondition
    FactorialPrecondition
    AccumulatorInvariant
    ArraySumStepLemma
    SumToN
    DotProductE2E
    Matrix3
    Matrix4
    ArrFilter2
    CountEvenStepLemma
    CountInRange
    CountNegatives
    CountPos
    GuardLoop1
    LoopConditionalAccumulation
    Encoder1
    Recursive1Real
    PureCompoundWithLocals
    ProductAccumulator
    FactorialStepLemma
)

echo "=== Regression on fixtures (timeout=${TIMEOUT}s) ==="
for f in "${FIXTURES[@]}"; do
    if [ ! -f /test/${f}.java ]; then
        echo "[SKIP] ${f} (no .java)"
        continue
    fi
    START=$(date +%s)
    # Use a 4x shell timeout to give OpenJML time to print the verify msg
    # after z3 returns unknown (some fixtures have multiple proof obligations)
    OUT=$(timeout $((TIMEOUT * 4)) /opt/openjml/openjml --esc --code-math=safe --spec-math=bigint --arithmetic-failure=hard --counterexample --timeout=${TIMEOUT} /test/${f}.java 2>&1)
    EC=$?
    END=$(date +%s)
    ELAPSED=$((END - START))
    ERRS=$(echo "$OUT" | grep -cE "verify:|^error:|^[0-9]+ error")
    SU=$(echo "$OUT" | grep -cE "Validity is unknown|reason for an unknown|esc.resourceout|jml.internal.notsobad")
    REAL=$(echo "$OUT" | grep -cE "underflow|overflow|null|out of range|cannot establish|COUNTEREXAMPLE")
    if [ $EC -eq 124 ]; then
        echo "[SHELL_KILL ${ELAPSED}s] ${f} (probably solver_unknown but truncated)"
    elif [ ${ERRS} -eq 0 ]; then
        echo "[PASS ${ELAPSED}s] ${f}"
    elif [ ${SU} -gt 0 ]; then
        echo "[SOLVER_UNKNOWN ${ELAPSED}s] ${f} (${SU} unknown)"
    elif [ ${REAL} -gt 0 ]; then
        echo "[REAL_TRACE ${ELAPSED}s] ${f} (${ERRS} verify-msg, ${REAL} real)"
    else
        echo "[FAIL ${ELAPSED}s] ${f} (${ERRS} errs)"
    fi
done
echo "=== done ==="
