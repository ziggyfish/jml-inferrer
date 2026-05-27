# Experiment 03 — Semantic-Versioning Correlation

**Strengthens:** the compatibility capability and the "industry" framing; a
novel, publishable side-result.
**Tier:** 1.

---

## 1. What it tests

Semantic versioning (semver) is the industry's declared contract for
compatibility: a patch bump promises bug-fixes only, a minor bump promises
backward-compatible additions, a major bump permits breaking changes. But the
declaration is manual and frequently wrong. This experiment tests whether the
*magnitude and kind* of inferred-specification change between two releases
correlates with the declared semver level — and, where it does not, whether the
mismatch flags a mislabelled release.

**Hypotheses.**

- **H1 (correlation).** Specification-change magnitude increases monotonically
  with semver level: patch < minor < major, on average.
- **H2 (mislabelling detection).** Releases whose spec-change profile is
  inconsistent with their declared level (e.g. a patch release with strengthened
  preconditions — a behavioural break shipped as a bug-fix) are detectable, and a
  sample of them corresponds to real, independently-confirmable compatibility
  problems (issue-tracker complaints, follow-up patch releases).

**Research question.** *Does inferred-specification change track declared semver
level across a large set of releases, and does specification-level analysis
identify releases whose declared level understates their behavioural change?*

---

## 2. How it would be tested

**Subjects.** A large set of release pairs from semver-following libraries on
Maven Central — ideally hundreds of consecutive-release pairs across dozens of
libraries, so the correlation has statistical power. The version strings give the
declared level (patch/minor/major) for free.

**Procedure.**

1. For each consecutive release pair, run the inferrer over both versions and
   compute the spec diff (`SpecDiffer`, Experiment 01).
2. Define a **spec-change score** per pair: a weighted count of strengthened
   preconditions, weakened postconditions, widened frames, and removed/added
   methods — with behavioural-break-type changes weighted above additive ones.
3. **H1:** regress spec-change score on declared semver level; report the
   ordering and effect size (e.g. Kruskal–Wallis across the three levels with
   post-hoc pairwise tests).
4. **H2:** flag pairs where the score is high but the declared level is low
   (a "stealth break"); for a sample, manually check the issue tracker / a
   subsequent patch release for confirmation that the release caused breakage.

**Metrics.** Distribution of spec-change score per semver level; effect size and
significance of the level ordering; count and confirmed-rate of detected stealth
breaks; precision of stealth-break flags on the manually-checked sample.

**Analysis.** The headline is the monotonic ordering (H1) plus a small set of
confirmed mislabelled releases (H2) — the latter is the compelling, novel,
industry-relevant result, since it shows the inferred specs catch real
compatibility problems that the declared version number hides.

---

## 3. How it would be added to the inferrer tool

Builds on `SpecDiffer`; adds version-history harvesting, a scoring function, and
statistics.

**New class `com.jml.inferrer.compat.MavenHistoryHarvester`.**
Given a set of `groupId:artifactId` coordinates, queries Maven Central's metadata
for the release list, downloads consecutive version pairs' source (or binary)
jars into the local cache, and parses each version string into a semver triple
and level. Rate-limit-aware, resumable, caches downloads.

**New class `com.jml.inferrer.compat.SpecChangeScorer`.**
Consumes `SpecDiffer` output for a pair and produces the weighted spec-change
score plus the per-category breakdown. The weights are a configurable
`ScoreConfig` so the scoring scheme is auditable and tunable.

**New harness `com.jml.inferrer.compat.SemverCorrelationRunner`.**
Drives harvest → inference (`CodebaseProcessor`) → diff (`SpecDiffer`) → score
(`SpecChangeScorer`) over the full set, writes a tidy CSV
(`library, from, to, level, score, breakdown...`), and runs the statistical
tests (delegating to an R/Python script in the replication package, or a small
embedded stats helper).

**Reuse.** Inference and `SpecDiffer` are shared with Experiments 01–02;
`MavenHistoryHarvester` is also reusable for scaling Experiment 08's corpus.

---

## Threats and pitfalls

- **Scale and runtime.** Hundreds of pairs × full inference is the most
  compute-heavy experiment here; needs the harvester to be resumable and the
  inference to be parallelised across pairs.
- **Semver compliance varies.** Many libraries do not actually follow semver;
  the correlation is over *declared* levels, and non-compliance is part of what
  H2 measures — but it muddies H1. Restrict H1 to libraries with a stated semver
  policy.
- **Score validity.** The weighted score is a construct; its weights must be
  justified (sensitivity analysis across weight schemes) so the correlation is
  not an artefact of the scoring choice.
- **Stealth-break confirmation is labour-intensive** and partly subjective;
  report it as a sampled, dual-rated finding, not an exhaustive one.

## Effort

Medium–high. Harvester ≈ 1 week; scorer + stats ≈ 1 week; the large-scale run
and the stealth-break adjudication ≈ 2–3 weeks. Compute-bound.

## Deliverables

A correlation result (spec-change vs declared semver level, with effect size),
and a curated list of confirmed mislabelled releases — a result with direct
industry resonance and a strong candidate for a standalone publication that also
feeds the thesis's adoption argument.
