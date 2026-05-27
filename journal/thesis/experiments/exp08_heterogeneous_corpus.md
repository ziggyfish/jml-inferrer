# Experiment 08 — Heterogeneous Corpus (Application and Framework Code)

**Strengthens:** external validity of RQ1 and the adoption claim; addresses the
corpus-homogeneity threat that recurs in every chapter (all evaluation is
open-source *library* code).
**Tier:** 3.

---

## 1. What it tests

Every empirical result in the thesis is on mature, well-structured open-source
*library* code (Commons Lang/IO/Math, jOOL, Vavr, Guava). The recurring threat is
that the results may not transfer to the application code, framework code, and
proprietary systems that make up the bulk of real software — precisely the
"industry" the title invokes. This experiment runs the inference and accuracy
validation on a deliberately *heterogeneous* corpus.

**Hypotheses.**

- **H1 (coverage holds).** The engine produces non-trivial specifications for a
  large fraction of methods in application/framework code, though likely a lower
  fraction than for utility libraries (the `other` category — event handlers,
  callbacks, I/O — is non-empty here and is the hardest to specify).
- **H2 (accuracy degrades gracefully).** Precision against intent and OpenJML
  discharge rate remain usefully high, with the degradation concentrated in
  identifiable categories (stateful/effectful methods, framework callbacks).
- **H3 (where it breaks is characterisable).** The method categories and code
  patterns where inference fails are identifiable and consistent, so the
  limitation is a mapped boundary rather than a uniform decline.

**Research question.** *Do the inference coverage and accuracy results transfer
from utility-library code to application and framework code, and where they
degrade, is the degradation characterisable?*

---

## 2. How it would be tested

**Corpus.** A spread deliberately unlike the existing one:
- **Framework code:** a slice of Spring (e.g. `spring-core`/`spring-beans`),
  which is callback- and reflection-heavy.
- **Application code:** a mid-size open-source Java application (not a library) —
  e.g. a web service or a desktop app — exercising the `other` category.
- **Android-style code** if feasible (lifecycle callbacks), as a stress case.
- Keep one utility library from the existing corpus as an anchor for comparison.

**Procedure.**

1. Run `CodebaseProcessor` over each subject; record coverage (fraction of
   methods receiving a non-trivial spec) and the per-category breakdown using the
   existing six-category taxonomy (now with a non-empty `other`).
2. **Accuracy (H2):** sample methods per category and run the dual oracle —
   manual-intent rating + OpenJML discharge — exactly as the inference study did.
   Full-corpus manual rating is infeasible; use a stratified sample with CIs.
3. **Boundary characterisation (H3):** for the methods with empty or wrong specs,
   categorise the cause (effectful method beyond local patterns, framework
   callback, reflection, concurrency, generics edge case) and report the
   distribution.

**Metrics.** Coverage and per-category coverage vs the utility-library anchor;
sampled precision and discharge rate per category with CIs; the failure-cause
distribution for uncovered/incorrect methods.

**Analysis.** The honest expected result: coverage and accuracy are lower than on
utility libraries but still useful on the imperative/value-like methods that
exist everywhere, with a clearly mapped boundary at effectful/framework/callback
code. This converts the homogeneity threat from an unbounded worry into a
measured, characterised limitation — which is itself a defensible contribution.

---

## 3. How it would be added to the inferrer tool

Mostly a corpus and measurement exercise on the existing pipeline; the additions
are corpus harnessing and per-category metric reporting at scale.

**New harness `com.jml.inferrer.eval.HeterogeneousCorpusRunner`.**
Resolves and unpacks the new subjects (Spring modules, the application repo),
runs `CodebaseProcessor` over each, and emits per-method records
(`subject, class, method, category, hasSpec, clauseCount`). Reuses the
`MavenHistoryHarvester`/cache resolution from Experiment 03 where the subject is
a Maven artefact, and a plain source-tree walk for application repos.

**Per-category metrics `com.jml.inferrer.eval.CoverageReporter`.**
Aggregates coverage and clause counts by the six-category taxonomy (the
categoriser already exists in `MethodSpecificationInferrer`/the categorisation
component), producing the coverage-vs-anchor table.

**Sampled-accuracy support.**
A `--sample` selector that draws a stratified sample per category for the manual
rating + OpenJML discharge, reusing the `FormalVerificationTestBase` Docker
pipeline for discharge and exporting a rating bundle (as in Experiment 07) for
the manual oracle.

**Failure categoriser `com.jml.inferrer.eval.UncoveredMethodClassifier`.**
For methods with empty/incorrect specs, classifies the cause from the AST shape
(effectful, callback, reflection, concurrency, generics), reusing the
categorisation analysis.

**Reuse.** The entire inference pipeline, the categoriser, the dual-oracle
validation, and the Docker OpenJML setup are unchanged; the work is corpus
plumbing and stratified measurement.

---

## Threats and pitfalls

- **Manual-rating cost.** Application/framework methods are harder and slower to
  rate than utility methods; the stratified sample must be sized for CIs, not a
  census, and raters need domain familiarity.
- **Build complexity.** Application repos may not parse cleanly with JavaParser
  at the configured language level, or may depend on generated sources; budget
  time for getting subjects to parse.
- **Category boundary cases.** The `other` category is heterogeneous; subdivide
  it (callback / I/O / event-handler) so the failure characterisation is
  actionable.
- **Selection bias.** Cherry-picking friendly application code would undercut the
  point; pre-register the subject-selection criteria.

## Effort

Medium. Corpus harnessing and getting subjects to parse ≈ 1–2 weeks; the runs are
cheap (inference is fast); the sampled manual rating is the labour cost ≈ 1–2
weeks. No core-engine change.

## Deliverables

A coverage-and-accuracy result on application/framework code with a per-category
breakdown and a mapped failure boundary — converting the thesis's most pervasive
external-validity threat into a measured, characterised limitation and directly
supporting the "for industry" framing.
