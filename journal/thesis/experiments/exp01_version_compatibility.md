# Experiment 01 — Version-to-Version Compatibility Detection

**Strengthens:** the thesis's central capability claim (RQ4 / compatibility).
**Tier:** 1 — keystone. Converts the compatibility argument from *demonstrated
mechanism* to *demonstrated result*.

---

## 1. What it tests

The thesis argues that because a caller's specification is derived from its
callees', a change to a library propagates into the contracts of code that uses
it, so behavioural compatibility becomes computable at the specification level.
That argument currently rests on a *mechanism* (measured caller-on-callee
dependence) but no end-to-end demonstration. This experiment tests the claim
directly.

**Hypotheses.**

- **H1 (detection).** Comparing inferred specifications of a library across two
  versions surfaces behavioural changes — strengthened preconditions, weakened
  postconditions, altered frame conditions — at the method level.
- **H2 (propagation).** Recomputing a *client's* inferred specification against
  each library version yields client-side contract differences exactly when the
  client exercises a changed library method, demonstrating that library change
  propagates to callers.
- **H3 (usefulness).** The specification-level diff flags behavioural
  incompatibilities that signature-compatibility checking (the compiler, japicmp)
  does *not* flag — i.e. it catches breakage that compiles cleanly.

**Research question.** *Does specification-level comparison across library
versions detect behavioural incompatibilities, including those invisible to
signature-level tools, and does library-side change propagate to client-side
contracts as the thesis predicts?*

---

## 2. How it would be tested

**Subjects.** Three to five libraries with public version histories and known
behavioural changes — e.g. Apache Commons Lang (3.x line), Commons IO, Gson.
For each, pick adjacent release pairs that the changelog documents as containing
behavioural (not merely additive) changes, plus at least one pair documented as
purely additive (a negative control that should produce no client-side breakage).

**Client corpus.** For each library, assemble a set of *client* methods that
call it — drawn from real downstream projects (GitHub dependents) or synthesised
to exercise specific library methods. Each client is held fixed across the two
library versions; only the library changes.

**Procedure.**

1. Run the inferrer over library version $V_{old}$ and $V_{new}$ independently,
   producing a per-method specification map for each.
2. **Library-side diff (H1).** For every method present in both versions,
   classify the spec change: precondition strengthened / weakened, postcondition
   strengthened / weakened, frame widened / narrowed, unchanged. Use a
   subsumption check (does $pre_{new} \Rightarrow pre_{old}$?) discharged by the
   SMT backend where decidable, falling back to syntactic comparison otherwise.
3. **Client-side propagation (H2).** Run the inferrer (with the compositional
   pass) on each client against $V_{old}$ and against $V_{new}$, with the library
   supplying callee contracts. Diff the client's resulting specification. Record
   whether a client-side change occurs iff the client calls a method whose
   library-side spec changed.
4. **Incompatibility classification (H3).** Label each detected change:
   *breaking* (strengthened callee precondition the client may now violate, or
   weakened callee postcondition the client relied on), *compatible*, or
   *additive*. Compare against (a) the changelog ground truth and (b) japicmp's
   signature-level verdict.

**Metrics.**

- Precision/recall of detected breaking changes against changelog ground truth.
- Number of *behavioural* incompatibilities detected that japicmp marks
  signature-compatible (the headline number — breakage that compiles).
- Propagation correctness: fraction of client-side changes that correspond to a
  genuinely exercised changed library method (H2).
- False-positive rate on the additive-only control pair.

**Analysis.** Report a confusion matrix against the changelog; McNemar's test
comparing the spec-level detector to japicmp; per-library breakdown.

---

## 3. How it would be added to the inferrer tool

The pieces largely exist; the experiment is mostly orchestration plus a diff
component.

**New class `com.jml.inferrer.compat.SpecDiffer`.**
Input: two `SpecificationCache` instances (old, new) keyed by the same method
signatures. Output: a `SpecDiff` per method with the change classification.
Reuses the `CallGraphBuilder` signature format already shared by
`CompositionalAnalyzer` so old/new methods key consistently. The
strengthen/weaken judgement is a precondition-subsumption check; wrap the
existing OpenJML invocation (the `--validate` path) to discharge
$pre_{new} \Rightarrow pre_{old}$ and $post_{old} \Rightarrow post_{new}$ as
small standalone verification conditions, falling back to canonical-form string
comparison when the solver times out.

**New harness `com.jml.inferrer.compat.VersionCompatibilityRunner`.**
CLI: `--old <jarOrSrc> --new <jarOrSrc> --clients <dir> --changelog <csv>`.
It (1) runs `CodebaseProcessor` over each library version, (2) runs it with
`withCompositional=true` over each client against each version (the library's
embedded or inferred specs supplying callee contracts via the existing
`ClassFileSpecificationReader` / standard-library-database path), (3) calls
`SpecDiffer`, (4) emits a CSV of detected changes and a confusion matrix against
the changelog.

**Reuse.**
- Embedding (Experiment 09 / `AsmJmlSpecWriter`) lets the library's inferred
  specs travel into the client analysis without re-running inference on library
  source — exercising the distribution mechanism end to end.
- The OpenJML discharge wrapper from the validation pipeline supplies the
  subsumption checks.
- `japicmp` is added as a Maven plugin / CLI invocation for the signature-level
  baseline comparison.

**Output artefact.** A `compat-report.csv` per library pair and a summary table
(precision/recall, behavioural-breakage-japicmp-missed count) suitable for direct
inclusion in the compatibility chapter.

---

## Threats and pitfalls

- **Subsumption undecidability.** Many precondition pairs will not discharge;
  the syntactic fallback may over- or under-count. Report the fraction decided
  by the solver vs the fallback, and treat the fallback's verdicts as advisory.
- **Changelog ground truth is noisy.** Changelogs under-document behavioural
  changes; a "false positive" against the changelog may be a real change the
  changelog omitted. Mitigate with manual adjudication of a sample.
- **Client corpus realism.** Synthesised clients risk only exercising the easy
  cases; include at least one real downstream project per library.

## Effort

Medium–high. `SpecDiffer` + subsumption wrapper ≈ 1–2 weeks; harness and corpus
assembly ≈ 1–2 weeks; analysis ≈ 1 week. The single most valuable experiment in
the set.

## Deliverables

A new chapter section (or its own results chapter) reporting detection
precision/recall, the count of behavioural incompatibilities missed by
signature-level tooling, and a worked example of a real breaking change caught
by the spec diff and missed by japicmp.
