# Experiment 04 — Mutation Coverage of Propagated Specifications (P3 vs P3C)

**Strengthens:** downstream value of compositional propagation (RQ4), on the same
metric the rest of the thesis uses; closes the thesis's weakest empirical link.
**Tier:** 2.

---

## 1. What it tests

The compositional chapter establishes that propagation adds 42,370 cross-method
obligations, and a preliminary probe found a positive but noisy *test-count*
delta when the propagated specs were supplied to an LLM test generator. Test
count is a poor proxy for oracle quality (the thesis's own P2-vs-P3 finding
proves this). This experiment replaces the test-count signal with a **mutation
score** comparison.

**Hypothesis.** Tests generated from compositionally-propagated specifications
(P3C) achieve a higher mutation score than tests generated from single-pass
specifications (P3), because the propagated guard-conditional and disjunctive
clauses direct the model toward branch- and dispatch-dependent behaviours that
the single-pass spec leaves unstated — and these are where return-value and
conditional mutants survive.

**Research question.** *Do the additional clauses from compositional propagation
translate into measurably stronger fault detection, or only into more tests?*

---

## 2. How it would be tested

**Design.** A paired comparison on the same methods, two conditions:
- **P3:** LLM context = single-pass inferred spec (the existing P3 condition).
- **P3C:** LLM context = compositionally-propagated spec.
Model fixed, temperature fixed, five (or more) runs per method per condition, as
in the existing test-generation study.

**Corpus.** Start with the 11-class `commons-test-project` already wired for the
LLM experiment, then extend to a larger sample of methods that the compositional
pass actually refined (so the conditions genuinely differ — methods the pass did
not touch would make P3 ≡ P3C and dilute the signal). Select methods stratified
by the shape of the added clause (branch-conditional, disjunctive, null/range).

**Procedure.**

1. Generate P3 and P3C test suites with `ExperimentRunner` (the P3C phase
   already exists).
2. **Repair the harness so suites compile and run** — the prior probe failed
   here (leading markdown fences, surrogate-pair tokens, package mismatches).
   Without compiling suites there is no mutation score.
3. Run PIT over each suite against the unmutated class under test.
4. Compare mutation scores P3 vs P3C, paired by method, with the same
   statistical treatment as the main study (paired test, effect size, bootstrap
   CI, correction).
5. Decompose by added-clause shape: does the gain concentrate where the
   propagation added branch-conditional clauses (the predicted mechanism)?

**Metrics.** Mutation score per method per condition; paired delta with CI and
effect size; per-shape and per-class breakdown; compile/pass rates (to confirm
the harness repair worked).

**Analysis.** The headline is the paired mutation-score delta and whether it is
significant after correction. The per-shape decomposition tests the *mechanism*:
the gain should be largest on methods where propagation added the clauses that
encode branch and dispatch behaviour.

---

## 3. How it would be added to the inferrer tool

Most machinery exists; the work is harness repair, corpus extension, and the PIT
comparison wiring.

**Fix `com.jml.inferrer.experiment.ExperimentRunner` extraction.**
The `extractJavaCode` path already tolerates truncation and missing fences;
extend it to (a) strip leading/trailing stray fences robustly, (b) reject or
sanitise non-Java tokens (surrogate-pair `char` literals), (c) enforce the
expected package/class name via the existing `fixTestCode`. Add a post-generation
**compile gate** that attempts `javac` on each generated suite and logs failures
with the raw response, so a low score is never silently an extraction failure.

**New harness `com.jml.inferrer.experiment.MutationComparisonRunner`.**
Given the P3 and P3C generated suites, copies each into the
`experiment/commons-test-project` test tree, runs `mvn pitest:mutationCoverage`
per condition, parses PIT's XML/HTML report into per-method mutation scores, and
emits a paired CSV (`class, method, shape, p3_score, p3c_score, delta`).

**Corpus extension.**
Add a selector that, from a `CompositionalAnalyzer.RefinementResult`, lists the
methods the pass actually refined and their added-clause shapes, so the
experiment targets methods where P3 and P3C differ. This reuses the
`RefinementResult` the compositional pass already returns.

**Reuse.** `ExperimentRunner` P3/P3C phases, the `commons-test-project` PIT
setup, and the statistics scripts from the main study.

---

## Threats and pitfalls

- **Harness fragility was the original blocker.** Budget real time for the
  compile gate; without it the experiment cannot run. This is the critical path.
- **Equal-spec dilution.** Methods the pass did not refine make the conditions
  identical; the corpus selector must target refined methods or the signal
  washes out.
- **LLM cost and non-determinism.** Same as the main study; five runs minimum,
  budget for re-runs.
- **Mutation-score ceiling.** Some classes already score near 100% under P3
  (e.g. simple wrappers); stratify so the comparison is not dominated by methods
  with no headroom.

## Effort

Low–medium. Harness repair ≈ 1 week (the hard part); corpus selector and PIT
comparison ≈ 1 week; runs and analysis ≈ 1 week. Most components already exist.

## Deliverables

A paired P3-vs-P3C mutation-score result with effect size and a per-shape
decomposition, converting the compositional chapter's preliminary test-count
signal into a result on the thesis's primary fault-detection metric.
