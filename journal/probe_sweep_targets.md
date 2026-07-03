# Probe-Sweep Target Plan

**Drafted:** 2026-05-06 (autonomous probe-sweep week, day 1)
**Status:** living document — updated each iteration
**Source plan:** `journal/rq2_rq4_execution_plan.md` §1.1, `feedback_ai_probe_workflow.md`

This document picks the failing tests, groups them by encodable pattern, and orders the implementation sequence so each landing fixes a cluster rather than a single test.

## Baseline (in flight)

Today's verification suite run (`test-output-2026-05-06-baseline.log`) is still mid-execution as of writing. The four completed suites give the following snapshot — to be updated when the run finishes:

| Suite | Tests | Failures | Notes |
|---|---|---|---|
| DataStructure | 23 | 5 | matrixSet, matrixTrace, matrixRowSum, sortedInsertionPoint, heapSiftDown — all 240s timeouts |
| LoopInvariant | 34 | 12 | nested/2D/accumulator/recursion mix, mostly real failures (not timeouts) |
| Interprocedural | 21 | 10 | recursive*, getterInComputation, integerParseInt, etc. — many 240s timeouts |
| DesignPattern | 22 | 4 | computeDispatch, cursorSkip, scaleArray, builderSetName |
| **Subtotal** | **100** | **31** | |

Memory's last stable failure count is 86 (end of fix30, 2026-04-29). Whether 31 represents a third of the suite (good news) or the easy third (bad news) won't be clear until baseline finishes.

## Encodable patterns identified

The probe workflow on `Matrix4.trace` (the only validated probe) identified three patterns:

### Pattern P1 — Cross-field length precondition

When a method body iterates `for(int i = 0; i < <field>; i++) <arrayField>[i]`, the access is in-bounds only when `<field> <= <arrayField>.length`. Currently the inferrer emits `<arrayField> != null` and `0 <= <field>` but not the cross-field bound. New precondition: `<field> <= <arrayField>.length`.

**Generalisability:** HIGH. Direct extension of `analyzeCrossArrayLoopBounds` (the parameter-based variant for `b.length >= a.length`).

**Targets it should fix:** matrixSet, matrixTrace, matrixRowSum (plus possibly the array-intensive suite when it lands).

**Implementation site:** `PreconditionAnalyzer` — new method `analyzeFieldBoundedLoopArrayLength`.

### Pattern P2 — 2D null/length forall (diagonal access)

When a 2D access `data[i][i]` (or `data[expr][expr]`) appears in a loop bounded by `<bound>`, the safety condition is `(\forall int k; 0 <= k && k < <bound>; data[k] != null && k < data[k].length)`.

**Generalisability:** MODERATE. The diagonal pattern is mechanical; off-diagonal 2D access (`data[row][col]` with independent indices) is a different pattern requiring its own heuristic.

**Targets it should fix:** matrixTrace (and possibly some LoopInvariantVerificationTest 2D cases).

**Implementation site:** `PreconditionAnalyzer` — new method `analyzeTwoDimensionalDiagonalAccess`.

### Pattern P3 — Accumulator overflow bounds + matching loop invariant

When `sum += <arrayField>[i]` is inside a loop bounded by `<size-bound>`, the overflow safety conditions are: per-element `<arrayField>[k]` bounds, size cap, and a matching loop invariant `K_LO * i <= sum && sum <= K_HI * i`.

**Generalisability:** MODERATE — the *shape* is mechanical, but the constants `K_LO`, `K_HI`, `K_N` are arbitrary. Picking 1000, -1000, 10^6 keeps `K_HI * K_N + K_HI < INT_MAX` (~10^9 < 2^31), which works for typical fixtures but is a magic number.

**Caveat from `feedback_ai_probe_workflow.md` step 8:** "If the AI proposes specs that verify but use patterns that can't be heuristic (e.g. requires solving a non-trivial constraint per call site), flag it as Low generalisability — don't try to encode an unbounded family of constants into the inferrer." Picking a single fixed bound family (1000/10^6) sidesteps the unbounded-family concern; this stays Moderate, not Low.

**Targets it should fix:** matrixTrace, matrixRowSum, prefixSum, factorialLoop, productAccumulator (plus probably more accumulator tests in suites yet to land).

**Implementation site:** `OverflowPreconditionAnalyzer` — new method `analyzeFieldBoundedArraySumOverflow`; `LoopInvariantAnalyzer` — extend the accumulator-pattern handler to emit the matching `K_LO*i <= sum <= K_HI*i` invariant.

## Implementation order

The order is dictated by (a) which fix unlocks the most other fixes, (b) which fix is simplest and lowest-risk, and (c) which fix matches `feedback_propagation_focus.md`'s call to focus on WP/SP propagation.

### Day 2 (May 7) — P1 cross-field length

Lowest-risk, simplest. Emits one new precondition. Implementation est: 1.5 hours including test writing. Re-run DataStructure suite afterwards to confirm matrixSet, matrixRowSum, possibly matrixTrace flip from FAILED to VERIFIED.

Steps:

1. New analysis test in `PreconditionAnalysisTest` (or appropriate split — see CLAUDE.md 30-test-per-class rule) that asserts the inferrer emits `<field> <= <arrayField>.length` for the matrix shape.
2. Implement `analyzeFieldBoundedLoopArrayLength` in `PreconditionAnalyzer`.
3. New verification test in `DataStructureVerificationTest` asserting `inferAndVerify` succeeds for a representative shape.
4. Re-run DataStructure suite (subset, not full); confirm fix.
5. Run RegressionVerificationTest to confirm no regressions.

### Day 3 (May 8) — P3 accumulator overflow

Higher-impact because it fixes accumulator failures across multiple suites (LoopInvariant, DataStructure, possibly more). Implementation est: 4 hours.

Steps:

1. Analysis test asserting the inferrer emits per-element bounds, size cap, and matching loop invariant.
2. Implement `analyzeFieldBoundedArraySumOverflow` in `OverflowPreconditionAnalyzer`.
3. Extend the accumulator-pattern detector in `LoopInvariantAnalyzer` to emit the `K_LO*i <= sum && sum <= K_HI*i` invariant for the same trigger shape.
4. Verification tests: prefixSum, factorialLoop, productAccumulator, matrixTrace, matrixRowSum.
5. Re-run LoopInvariant + DataStructure subsets.

### Day 4 (May 9) — P2 2D null/length forall

Most surgical of the three. Should be done last because (a) it's the narrowest pattern (diagonal access only), and (b) by then P1+P3 may have closed the matrixTrace failure mode without P2 needing to fire. Implementation est: 3 hours.

Steps:

1. Analysis test asserting the forall is emitted for `data[i][i]` access.
2. Implement `analyzeTwoDimensionalDiagonalAccess` in `PreconditionAnalyzer`.
3. Verification test: matrixTrace (the only known fixture that hits this exact shape; if other 2D fixtures emerge they get added).
4. Re-run DataStructure subset.

### Day 5 (May 10) — Triage what's left

After P1, P2, P3, the matrix cluster + several accumulator failures should be closed. The remaining failures will be:

- **Recursion-related** (recursiveFactorial, recursiveFibonacci, recursiveBinarySearch, recursivePower, recursiveArraySum) — these need a different heuristic, likely `decreases` clause inference + recursive-call WP-propagation.
- **Heap structural** (heapSiftDown) — needs heap-specific structural invariants (parent ≤ children).
- **Sorted-array binary search** (sortedInsertionPoint) — needs midpoint-progress invariant + sortedness.
- **Other** — case by case.

Day 5 picks the next-highest-leverage target from this remainder list. Likely candidate: recursion-related, since it spans 5+ Interprocedural failures.

### Day 6 (May 11) — Status report + memory update

Final baseline run with all heuristics in place. Write up the failure-count delta. Update memory `MEMORY.md` with the autonomous-week summary. Tag the commit.

## Out of scope this week

- Article 1 LLM rerun (P1–P4 with fresh Gemini calls) — deferred per option (a) chosen 2026-05-06.
- Phase 2A.3 implementation (`jml-embedder` working code) — skeleton only this week per plan.
- Phase 2A.5+ OpenAPI extension implementation — defer to June.
- Phase 2B compositional implementation — defer to October.
- Phase 3 CI/CD integration — defer to March 2027.

## Risk register

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| P1 introduces a regression on the existing Article 1 corpus (causing Article 1's reported 94.2% precision to drop) | Low | Article 1 numbers stale | The Article 1 numbers are tied to a specific commit; if regression, document and roll forward. Article 1's headline claims are not at risk. |
| P3's 1000/10^6 constants don't fit some fixtures (an array with values outside ±1000) | Medium | Per-fixture failure | Detect when a literal in the source exceeds the bound; widen K_HI to the smallest power of 10 that fits, or skip the heuristic if no clean choice. |
| Docker rebuild forgotten between iterations | Medium (per `feedback_docker_rebuild.md`) | Stale binary verifies | Always `docker compose build test` before each verification subset run. |
| Subset run masks regression in non-targeted suites | Medium | False sense of progress | Always finish each iteration with a full RegressionVerificationTest run (which is fast). |
| `feedback_dont_reorder_specs.md` warns that even safe-looking AnnotationToJMLConverter changes cause +70 regression | Medium | Ship a fix that net-regresses the suite | Never touch AnnotationToJMLConverter ordering. P1/P2/P3 add new clauses; do not reorder existing ones. |
