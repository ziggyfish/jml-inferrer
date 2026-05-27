# Experiment 05 — OpenJML Discharge of Propagated Clauses at Scale

**Strengthens:** the soundness of the RQ4 output; closes a gap where the
compositional chapter counts clauses but does not verify them.
**Tier:** 2.

---

## 1. What it tests

The compositional chapter reports that the pass adds 42,370 precondition clauses
but defers their formal discharge, arguing only that they *should* be sound
because they are lifted instances of already-validated callee clauses. This
experiment tests that argument: it runs the 42,370 propagated clauses through
OpenJML's Extended Static Checker and reports how many discharge.

**Hypotheses.**

- **H1 (soundness preserved).** The propagated clauses discharge at a rate
  comparable to the engine's other output — i.e. lifting a sound callee
  precondition through a sound guard yields a dischargeable caller clause, as
  argued.
- **H2 (failure characterisation).** The clauses that do *not* discharge fall
  into identifiable categories (substitution artefacts, guard-context the
  verifier cannot reconstruct, the known SMT tractability limits) rather than
  indicating the pass is unsound.

**Research question.** *Are the cross-method obligations the compositional pass
adds formally sound against the implementation, and where they are not, why?*

---

## 2. How it would be tested

**Subjects.** The five-library compositional corpus (Commons Lang, IO, Math,
jOOL, Vavr), or a stratified sample if full-corpus discharge is intractable
within the SMT time budget (it likely is — 21,052 methods × ESC is heavy).

**Procedure.**

1. Run inference with the compositional pass to produce the propagated specs.
2. Emit each method's propagated contract as JML annotations on the source
   (existing `AnnotationToJMLConverter` path).
3. Run OpenJML ESC over the annotated source, per method, recording for each
   *propagated* clause: discharged / flagged / unsupported / timeout.
4. Separate the propagated clauses from the baseline (single-pass) clauses so the
   discharge rate is reported *for the additions specifically*, not diluted by
   the already-validated base.
5. **H2:** categorise the non-discharged propagated clauses — substitution
   artefact, guard not reconstructible, recursive-multiplicative / array-quantified
   / for-each (the three known limits), or genuine unsoundness.

**Metrics.** Discharge / flag / unsupported / timeout rates for propagated
clauses, compared to the engine's baseline discharge rate (92.9% overall from
the inference study); per-category failure breakdown; per-library and per-shape
(branch-conditional vs disjunctive) discharge rates.

**Analysis.** H1 holds if the propagated-clause discharge rate is close to the
baseline. The disjunctive (polymorphic-dispatch) clauses are the interesting
case — a disjunction over candidates is weaker and may discharge *more* readily
than a conjunctive precondition, or may stress the solver differently; report
this separately.

---

## 3. How it would be added to the inferrer tool

The discharge machinery exists; the work is tagging propagated clauses and
scaling the ESC run.

**Tag propagated clauses.**
Extend `CompositionalAnalyzer` so each clause it adds carries a provenance flag
(e.g. a `Set<String>` of propagated-clause identities on the `MethodSpecification`,
or a wrapper marking origin = compositional). This lets the discharge harness
attribute each ESC verdict to baseline vs propagated. Minimal change — the
analyzer already knows which clauses it adds (`RefinementResult`).

**New harness `com.jml.inferrer.eval.PropagatedDischargeRunner`.**
Drives: inference + compositional pass → annotate → OpenJML ESC (via the existing
Docker `FormalVerificationTestBase` / `inferAndVerify()` plumbing, batched per
class) → parse ESC output → join verdicts to the provenance tags → emit a CSV
(`class, method, clause, origin{base|prop}, shape, verdict`).

**Scaling.**
Full-corpus ESC is heavy; add (a) a `--sample N` mode that stratifies by
added-clause shape and library, and (b) a per-clause timeout consistent with the
inference study's strictness config (`code-math=safe`, `spec-math=bigint`,
z3-4.13.4). Reuse the forked OpenJML in `openjml-dev/` (the `define-fun-rec`
quantifier support matters for the accumulator-bearing methods).

**Failure categoriser `com.jml.inferrer.eval.DischargeFailureClassifier`.**
Buckets non-discharged clauses by the known categories using the clause shape and
the ESC error message, reusing the categorisation logic already used to describe
the three tractability limits in the inference study.

**Reuse.** Docker OpenJML pipeline, `FormalVerificationTestBase`, the forked
solver, and the strictness configuration are all in place.

---

## Threats and pitfalls

- **Compute cost.** ESC over 21k methods may be infeasible; the stratified
  sample is the realistic path — report it as a sample with CIs, not a census.
- **Annotation emission at scale.** Emitting and re-parsing JML for the whole
  corpus may surface formatting edge cases; the existing 576-test regression
  suite guards the common cases but corpus-scale will find new ones.
- **Attribution correctness.** The provenance tagging must be exact, or baseline
  and propagated verdicts blur; unit-test the tagging on the
  `commons-test-project` first.
- **Timeouts ≠ unsound.** Keep timeout as its own category; conflating it with
  failure would understate soundness.

## Effort

Medium. Provenance tagging ≈ few days; harness ≈ 1 week; the (sampled) ESC run is
compute-bound, days–weeks of machine time; analysis ≈ 1 week.

## Deliverables

A discharge-rate result for the propagated clauses specifically, alongside the
baseline rate, plus a failure-category breakdown — turning the compositional
chapter's "should be sound" argument into a measured soundness result and
pre-empting the examiner's soundness objection.
