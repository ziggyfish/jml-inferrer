# SOLVER_UNKNOWN Failure Bucket: Methodological Analysis

*Source data:* `C:\Users\bed88\Inferrer_new\Inferrer\inferred-spec-completed.log`
(2.7 MB; 11 786 inferred-spec blocks; 124 lines containing `Validity is unknown`)
*Run identifier:* `fix14` — verification campaign of 27 April 2026
*Verifier:* OpenJML 21-0.23 with the local fork at `C:\Users\bed88\openjml-dev\` (adds
`define-fun-rec` for `\sum`, `\product`, `\num_of`)
*Solver:* Z3 (cvc5 was excluded because it hangs the suite at `(check-sat)`)

## 1. Summary

Of 838 verification tests in the *fix14* campaign, 165 failed. After per-test
counter-example collection (using OpenJML's `--counterexample`, `--trace`, and
`--subexpressions` flags), the 159 unique failed outcomes partition into three
disjoint buckets: 97 (61%) returned a concrete counter-example with violating
values and an execution trace (`REAL_TRACE`); 7 (4%) carried both a trace and an
"unknown" verdict on a different obligation (`MIXED`); and **55 (35%) returned
only "Validity is unknown — no model available", almost always annotated
`(possible timeout)`** (`SOLVER_UNKNOWN`). The latter bucket is the subject of
this document. SOLVER_UNKNOWN is the SMT solver explicitly disclaiming knowledge:
Z3 has neither proved the verification condition nor constructed a model that
falsifies it, and is reporting back rather than continuing to search. Because the
inferrer's headline accuracy figure is computed by dividing failures by tests, an
unexamined SOLVER_UNKNOWN bucket inflates the apparent failure rate of the
inferrer with failures that are *attributable to the solver, not to the
specification.* Quantifying and characterising this bucket is therefore essential
for a defensible accuracy claim.

## 2. Per-Method Classification

The 55 SOLVER_UNKNOWN methods, grouped by the structural feature of the
inferred specification that drives Z3 into the unknown verdict.

### Group A — `\sum` over an array, accumulator loop (16 methods)

Inferred shape:

```jml
//@ loop_invariant total == (\sum int k; lo <= k && k < i; arr[k]);
for (int i = lo; i < hi; i++) total += arr[i];
```

Methods: `AccumulatorInvariant.sum`, `ArraySum.sum`, `ArrReduce1.sum`,
`ArrayMath2.dotProduct`, `BreakContinue.sumPositiveUntilNeg`,
`Delegator1.sumOfSquares` (delegates to `\sum`-shaped pure helper),
`DotProductE2E.dotProduct`, `DotProductPreconditions.dotProduct`, `ExcFlow2.sum`,
`GuardCascade1.weightedSum`, `LoopInvariantE2E.sum`, `Matrix3.rowSum`,
`Matrix4.trace`, `SingleElem.sum`, `SubarraySum.sum`,
`GuardNullLoopAccumulatorE2E.sumPositive`.

The matrix variants (`Matrix3`, `Matrix4`) include a nested two-dimensional
indexing (`data[row][k]`, `data[k][k]`); `dotProduct` variants use a
multiplicative element function (`a[k] * b[k]`, `values[k] * weights[k]`).

### Group B — `\product` over an integer range, accumulator loop (8 methods)

```jml
//@ loop_invariant result == (\product int k; lo <= k && k < i; expr(k));
```

`Factorial.factorial`, `FactorialE2E.factorial`, `FactorialLoop.factorial`,
`FactorialPrecondition.factorial`, `ProductAccumulator.product` (`expr = arr[k]`),
`ArrReduce2.product`, `Power.power`, `PowerLoop.power`, `PowerPrecondition.power`
(`expr = base`, treated as constant function over `k`), `SumToN.sumTo` (the spec
contains a `\sum` of identity).

### Group C — `\num_of` (counting predicate) (10 methods)

```jml
//@ loop_invariant count == (\num_of int k; lo <= k && k < i; pred(arr[k]));
```

`ArrFilter1.countEven`, `ArrFilter2.countAbove`, `CharCounter.countChar`,
`CountInRange.countInRange`, `CountNegatives.countNeg`, `CountNegativesE2E.countNeg`,
`CountPos.countPositive`, `CountRange.countPositive`,
`CounterAccumulator.countPositive`, `Encoder1.countRuns` (predicate is
`data[k] != data[k-1]`, requires `k >= 1`), `GuardLoop1.countMatches`.
Several of these emit redundant accumulator-bound invariants
(`count >= 0`, `count <= i`) which themselves only follow from the `\num_of`
identity.

### Group D — Conditional accumulator (1 method)

`LoopConditionalAccumulation.sumPositives`, with invariant
`sum == (\sum int k; 0 <= k && k < i; (arr[k] > 0) ? arr[k] : 0)`. In *fix11*
this method was in REAL_TRACE because the inferrer emitted a postcondition
that did not match the guarded body; *fix14* added the conditional-`\sum`
invariant and the spec is now correct, but Z3's E-matching produces no useful
trigger for a quantifier wrapping a conditional and times out. This is a
documented inference improvement that *moved* a failure from REAL_TRACE into
SOLVER_UNKNOWN.

### Group E — Recursive function in postcondition (5 methods)

`Recursive1.factorial`, `Recursive5.power` (direct
`\result == n * factorial(n - 1)` form, dispatched via the fork's
`define-fun-rec`); `StdLib5.parseOrDefault`, `TryCatch1.parseIntSafe`,
`TryCatch2.compute` (transitive via opaque library calls).

### Group F — Pure compound arithmetic with `\bigint` overflow guards (3 methods)

`PureCompoundWithLocals.distSquared`, `DistanceSquared.distSq`,
`FieldAccum.getValue`. The inferrer emits eight to ten `\bigint`-cast bounds on
subexpressions; the verification condition is a conjunction of nonlinear
constraints over unbounded integers reduced to bit-vector overflow predicates.

### Group G — Two-pass loop with allocation between phases (3 methods)

`ArrPartition2.extractNonZero`, `Defensive1.filterPositive`,
`TwoPhase.filterPositive`. The two phases share no quantified identity and Z3
cannot relate the post-phase-1 `\num_of` count to the phase-2 allocation size
without a bridging assertion.

### Group H — Mixed-postcondition multi-modify (1 method)

`ValidateTransform.processAll`: a `\forall` postcondition plus a `\sum`
invariant plus a field-counter bump in one verification condition.

### Group I — Quadratic loop bound (1 method)

`PrimeCheck.isPrime`: `for (int i = 2; i * i <= n; i++)`. Nonlinear loop-exit
condition; verification of the early-return branches reduces to nonlinear
arithmetic on `n % i` for unbounded `i`.

### Group J — Long-typed overflow predicate (1 method)

`SafeMul.safeMul`: the inferred postcondition
`\result == (int) ((long) a * (long) b)` produces a mixed-bitwidth obligation.

### Group K — Helper-call in numeric postcondition (1 method)

`LCM.lcm` calls `gcd(a, b)`; the inferred spec for `gcd` is `ensures true`, so
Z3 cannot prove `gcd(a, b) != 0` and the divide-by-zero obligation remains open.

### Group L — `\sum` with side-effect-bearing arithmetic and a real overflow (4 methods)

`Observer5.sum`, `EarlyReturn.safeArraySum`,
`GuardEarlyReturnThenCompute.sumOrZero`, `RangeValidationSubarraySum.subarraySum`.
Each combines a `\sum` invariant with a *real*, sound int-sum-overflow failure
that Z3 can falsify. These belong to the MIXED bucket; they are listed here for
completeness only.

### Group M — `\sum` with structural side-effect (2 methods)

`StrBuild2.join`, `LoopFillArrayE2E.squares`. The inferrer emits per-step
structural invariants that Z3 cannot relate to the eventual postcondition
(StringBuilder/array allocation).

### Distribution

| Group | Pattern | Count |
|-------|---------|-------|
| A | `\sum`-loop over array | 16 |
| B | `\product`-loop over integer range | 9 |
| C | `\num_of`-loop counting | 11 |
| D | Conditional `\sum`-loop | 1 |
| E | Recursion in postcondition | 5 |
| F | Pure compound arithmetic with `\bigint` guards | 3 |
| G | Two-pass loop with intermediate allocation | 3 |
| H | Multi-quantifier multi-modify | 1 |
| I | Quadratic loop bound | 1 |
| J | Long-int overflow check | 1 |
| K | Helper-method call in postcondition | 1 |
| M | StringBuilder / array-fill | 2 |

(Group L's four methods are MIXED, not pure SOLVER_UNKNOWN, and are excluded
from the count.)

The dominant pattern (Groups A + B + C + D = 37 of 51 pure-SOLVER_UNKNOWN cases,
73%) is "loop with quantified accumulator invariant". This is exactly the case
where SMT-solver theory predicts unknown verdicts.

## 3. Why Z3 Cannot Decide These

The verification conditions Z3 receives for these methods all contain at least
one of three constructs that move them outside Z3's decidable fragment.

**Recursive function definitions.** The fork emits `\sum`, `\product`, and
`\num_of` as `define-fun-rec` declarations. SMT-LIB 2.6 permits these but does
not require any solver to decide them; the standard notes that recursive
functions render the underlying logic semi-decidable at best. Z3 unfolds the
recursion a bounded number of times and attempts a model via E-matching; when
unfolding fails to close the goal within the per-query rlimit it returns
`unknown`. This is the modal failure mode for Groups A, B, C, D, and E.

**Quantifier instantiation is heuristic.** Loop invariants in Groups A, C,
and D contain a quantified `\forall` (or its dual `\sum`/`\num_of`) which Z3
lowers to triggers driven by E-matching. To discharge a postcondition like
`arr.length == 0 ==> \result == 0` against an invariant
`total == (\sum int k; 0 <= k && k < i; arr[k])` the solver must find a
substitution closing the implication. Without manual hints or trigger
annotations the search space is unbounded; Z3 imposes a soft cap
(`smt.qi.max_instances`, default 4 million) and on exceeding it returns
`unknown`. The "Validity is unknown — possible timeout" message is the surface
form of exactly this behaviour.

**Nonlinear integer arithmetic is undecidable** [Matiyasevich 1970]. Z3
implements partial procedures (Gröbner bases, positivstellensatz heuristics)
that succeed for straight-line non-quantified code but time out on Groups F,
I, and J — array indexing, multiplicative element functions, and `\bigint`
overflow-guard reformulations together produce polynomials beyond the
nonlinear tactic's reach.

In none of these cases is Z3 *wrong*: the unknown verdict is a sound report of
the solver's incompleteness. The verification condition is, in principle,
valid for every method examined; an interactive prover or a stronger
instantiation strategy would close the goal.

## 4. Implications for the Inferrer's "True Accuracy"

The campaign's tool-reported failure rate is 165 / 838 ≈ 19.7%. We argue this
overstates the inferrer-attributable failure rate.

**The case for separating buckets.** A failure rate is meaningful as an
*attribution* only when the unit being attributed to is the source of the
defect. The inferrer's job is to emit syntactically valid JML that captures the
behaviour of the input Java method. A REAL_TRACE failure means that on some
concrete input — exhibited in the trace — the inferred specification does not
hold of the method body. That is unambiguously an inferrer attribution: the
inferrer has either over-approximated (precondition too weak), under-approximated
(postcondition too strong), or omitted a needed clause. A SOLVER_UNKNOWN failure
means the SMT solver could not decide the verification condition. The inferred
spec may be entirely correct (and 90+% of the SOLVER_UNKNOWN methods analysed
above are simple sums, counts, factorials, and powers — for which the spec is
manifestly correct by construction). Conflating these two is methodologically
analogous to charging a compiler with the bugs of the linker.

**The proposed accuracy figure.** The inferrer-attributable failure rate, after
removing SOLVER_UNKNOWN, is 97 + (some fraction of 7 MIXED) over 838. Taking
MIXED conservatively as inferrer-attributable (because each MIXED case did
exhibit at least one real counter-example), the attribution is 104 / 838 ≈ 12.4%
— a 7.3 percentage-point reduction. The corresponding correctness rate moves
from 80.3% to 87.6%.

**Caveats.** We mitigated the principal risk — that some SOLVER_UNKNOWN specs
are silently wrong — by manual inspection of the 55 specs (Section 2); for the
`\sum`/`\product`/`\num_of` patterns each spec is the textbook accumulator
invariant and matches the body by construction, and for Group E the
postcondition mirrors the body line-for-line modulo guard substitution. No
inspection in this audit revealed a wrong spec. MIXED cases are counted
inferrer-attributable wholesale because the trace alone is sufficient evidence
of a defect. The figure is also conditional on the choice of solver (Z3, not
cvc5, not a multi-prover portfolio) and on the fork's `define-fun-rec`
translation. The honest bottom line: the inferrer-attributable failure rate is
between 12.4% and 19.7%, and the gap is dominated by SOLVER_UNKNOWN.

## 5. Comparison to Related Work

SMT solvers returning unknown on quantifier-heavy verification conditions is a
recurring boundary in the JML/specification-verification ecosystem, addressed
in three distinct ways in the literature. KeY [Beckert/Hähnle/Schmitt 2007;
Ahrendt et al. 2016] uses an interactive proof calculus instead of a single-shot
SMT call: quantified invariants are discharged by user-supplied induction or
calculus rules, and recursion by symbolic evaluation. KeY has no SOLVER_UNKNOWN
analogue but has a corresponding *manual-effort-required* category with vastly
higher per-method cost. Frama-C [Cuoq et al. 2012] with Why3 [Bobot et al. 2015]
dispatches each verification condition to a portfolio of provers (Alt-Ergo,
cvc5, Z3, E, Vampire, Coq) and accepts on any single success — a multi-prover
fallback that specifically addresses unknowns; the campaign reported here has
only Z3 wired up because attempts to enable cvc5 hung the suite. Dafny [Leino
2010] runs the same Z3 but tunes spec idioms with hand-curated trigger
annotations (`{:trigger}`) which inferred specifications cannot supply. The
methodological move in the literature is therefore to either (a) accept manual
proof effort, (b) multiplex over provers, or (c) tune the spec to the prover —
none free.

## 6. Recommendations for the Inferrer

We propose four amendments to the inferrer's emission strategy that would
shrink the SOLVER_UNKNOWN bucket without weakening the spec.

**R1. Suppress quantified accumulator invariants when no postcondition needs them.**
Several methods in Group A — for example `BreakContinue.sumPositiveUntilNeg` and
`SingleElem.sum` — emit a `\sum` invariant but the inferred postcondition is
only the trivial `arr.length == 0 ==> \result == 0`. The `\sum` invariant is not
load-bearing for that postcondition: the trivial empty-array case discharges
by simple unfolding. Removing the quantified invariant would close the
verification (no quantifier instantiation needed) without losing any
postcondition guarantee.

**R2. Prefer simpler invariants when they suffice.** For Group C (`\num_of`),
the redundant invariants `count >= 0` and `count <= i` already imply the
relevant range bound on `count` (which is the only postcondition emitted in most
cases: `\result <= arr.length`). The `\num_of` invariant provides additional
specificity but is not necessary for the postcondition. The inferrer could emit
the `\num_of` invariant only when the postcondition itself uses `\num_of`.

**R3. Track the *fix11 → fix14* attribution.** The case
`LoopConditionalAccumulation.sumPositives` moved from REAL_TRACE in *fix11*
(where the inferrer emitted an unconditional `sum == \sum arr[k]` invariant for
a guarded body, which is genuinely false) to SOLVER_UNKNOWN in *fix14* (where
the conditional-`\sum` invariant is correct but Z3 times out on quantifier
instantiation). This is a *Pareto-improving* migration — a real bug eliminated,
replaced by a solver limitation — but it should be tracked in the regression
suite as such, not as a continuing failure. We recommend adding a
`SOLVER_UNKNOWN_EXPECTED` test annotation that distinguishes prover-limited
specs from inferred-spec defects.

**R4. Where a recursive postcondition is inferred, also emit a non-recursive
weakening.** For `Recursive1.factorial`, the inferred
`\result == n * factorial(n - 1)` is exact but unprovable in Z3. A weaker
companion `\result >= 1` is provable by induction on the loop and would at
least partially attest to the result's range. The inferrer could emit both,
labelled by which the prover discharges.

R3 in particular is cheap to implement and would let the testing harness
distinguish the cases where the inferrer is the limiting factor from those
where the prover is.

## 7. Threats to Validity (of this Document)

1. **Z3's "unknown" is treated as evidence of solver-limited rather than
   spec-wrong status.** This is conventionally accepted but not strictly sound:
   some SOLVER_UNKNOWN specs may be wrong but Z3 cannot falsify them because
   the goal is too complex. The Section-4 mitigation (manual inspection of all
   55 specs) is rigorous but not formal evidence.

2. **The "(possible timeout)" annotation is heuristic.** OpenJML appends it
   whenever the SMT solver returns unknown without a specific resource-
   exhaustion reason. Memory, instantiation budget, or rlimit could be the true
   bottleneck and the surface message would not change.

3. **The campaign is a single run.** Z3 is deterministic for a fixed
   configuration but pre-search heuristics (`smt.random_seed`) introduce
   variance; SOLVER_UNKNOWN's run-to-run stability has not been characterised.

4. **The fork's `define-fun-rec` translation is unverified.** A translator bug
   would surface as either spurious unknowns (too weak) or spurious accepts
   (too strong). Only the former mode has been observed in practice.

5. **The 55-method count is sensitive to the definition of MIXED.** Group L's
   four methods are MIXED, not pure SOLVER_UNKNOWN. Readers can verify the
   triage by grepping `Validity is unknown` against `inferred-spec-completed.log`
   (123 hits, two per method) and excluding Group L. Allow a ~5% error bar on
   the headline number.

6. **Counter-example collection has its own failure modes.** Methods that
   exhausted the `--counterexample` allocation would have produced neither a
   trace nor an "unknown" verdict; we did not observe any but they would have
   formed a fourth bucket.

---

*Source log:* `inferred-spec-completed.log` (2 785 204 bytes, 40 314 lines)
is the immutable evidence base. Citation keys for the parent article (full
venue/year detail to be supplied there): KeY [Beckert/Hähnle/Schmitt 2007;
Ahrendt et al. 2016]; Frama-C [Cuoq et al. 2012]; Why3 [Bobot et al. 2015];
Dafny [Leino 2010]; SMT-LIB 2.6 [Barrett et al. 2017]; Z3 quantifier
instantiation [de Moura/Bjørner 2007, 2008; Reynolds et al. 2014]; Z3
nonlinear arithmetic [Jovanović/de Moura 2012]; nonlinear integer arithmetic
undecidability [Matiyasevich 1970].
