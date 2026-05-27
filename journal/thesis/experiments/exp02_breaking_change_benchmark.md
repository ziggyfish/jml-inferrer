# Experiment 02 — Breaking-Change Benchmark

**Strengthens:** rigour of the compatibility result (RQ4); makes Experiment 01
comparable to prior API-evolution research.
**Tier:** 1.

---

## 1. What it tests

Experiment 01 measures compatibility detection against changelogs, which are
noisy. This experiment grounds the detector against a *curated* benchmark of
known Java library breaking changes, giving a defensible precision/recall figure
and positioning the result against the API-evolution literature, which uses such
benchmarks.

**Hypothesis.** The specification-level compatibility detector achieves
precision and recall on a curated breaking-change benchmark competitive with, and
complementary to, signature- and bytecode-level detectors (japicmp, Revapi,
clirr) — specifically, that it recovers *behavioural* breaks those tools
structurally cannot, at the cost of some recall on purely structural breaks.

**Research question.** *On a curated benchmark of known breaking changes, what
are the precision and recall of specification-level compatibility detection, and
how does its detected set relate (overlap / complement) to that of established
signature-level tools?*

---

## 2. How it would be tested

**Benchmark.** Use or assemble a labelled dataset of Java library version pairs
annotated with their breaking changes and break type (signature, behavioural,
exception-contract, etc.). Candidate sources: published API-evolution datasets,
the maven-central breaking-change studies, or a hand-curated set built from
release notes plus the libraries' own migration guides. Each entry: (library,
$V_{old}$, $V_{new}$, method, break type, breaking yes/no).

**Procedure.**

1. Run the Experiment 01 pipeline (`VersionCompatibilityRunner` + `SpecDiffer`)
   over every benchmark pair.
2. Classify each method as breaking / non-breaking by the spec diff.
3. Compute precision, recall, and F1 against the benchmark labels, broken down by
   break type — the key result being high recall on the *behavioural* subtype
   and acknowledged lower recall on the *pure-signature* subtype.
4. Run japicmp, Revapi, and clirr over the same pairs; compute the same metrics.
5. Compute set relationships: breaks found only by the spec detector, only by the
   signature tools, by both — the complementarity claim.

**Metrics.** Precision / recall / F1 overall and per break type; Venn-style
overlap counts against each baseline tool; statistical comparison (McNemar)
per tool.

**Analysis.** A per-break-type table (the spec detector should dominate on
behavioural breaks, lose on pure-signature breaks, and the union of the two kinds
of tool should beat either alone) is the headline. This frames the contribution
honestly: not a replacement for signature tools but a complement that catches the
behavioural breaks they miss.

---

## 3. How it would be added to the inferrer tool

Builds entirely on Experiment 01's components plus a benchmark loader and a
metrics module.

**New class `com.jml.inferrer.compat.BenchmarkLoader`.**
Parses the benchmark dataset (CSV/JSON of labelled pairs) into a list of
`(libraryPair, methodLabels)` records and resolves each version's artefact from
the Maven cache.

**New class `com.jml.inferrer.compat.CompatMetrics`.**
Given `SpecDiffer` output and benchmark labels, computes precision/recall/F1 per
break type and the overlap sets against the baseline tools. Emits a results table
and the confusion data.

**Baseline integration.**
Invoke japicmp / Revapi / clirr as external processes (each has a CLI or Maven
plugin) from a `BaselineComparators` helper, normalising their outputs to the
same `(method → breaking?)` shape so `CompatMetrics` can compare uniformly.

**Reuse.** `VersionCompatibilityRunner` and `SpecDiffer` from Experiment 01 are
the engine; this experiment adds only the labelled-benchmark scaffolding and the
multi-tool comparison.

---

## Threats and pitfalls

- **Benchmark availability.** A high-quality labelled benchmark may not exist
  off the shelf; building one is itself effort and a potential contribution, but
  curation bias is a threat — mitigate with dual-rater labelling and a published
  protocol.
- **Tool-output normalisation.** japicmp/Revapi/clirr report at different
  granularities; the normalisation to a common method-level verdict must be
  documented and validated on a sample.
- **Recall ceiling.** The spec detector cannot catch breaks in behaviour the
  inferrer never captured (the RQ1 recall gap propagates here); report this as a
  known upper bound rather than a surprise.

## Effort

Medium. If a benchmark exists: ≈ 2 weeks (loader, metrics, baseline wiring,
analysis). If a benchmark must be curated: add 2–4 weeks for curation and
labelling.

## Deliverables

A precision/recall/F1 table per break type, a complementarity (overlap) analysis
against japicmp/Revapi/clirr, and a defensible headline figure for the
compatibility detector that the examiner red-team objection ("the capability is
argued, not demonstrated") can be answered with.
