# Experiment 07 — Specification Cost: Manual vs Infer-and-Review

**Strengthens:** the adoption premise itself — the entire thesis rests on the
claim that manual specification cost is the binding constraint and that inference
removes it, yet that cost is currently asserted from the literature, not measured
on this tool.
**Tier:** 3.

---

## 1. What it tests

The thesis's economic argument is: manual specification is expensive and scales
with code size; inference plus review of flagged clauses is cheap and scales with
the (small) failure rate. This experiment measures the two costs directly and
compares them.

**Hypotheses.**

- **H1 (inference is cheaper).** The human time to obtain trustworthy
  specifications via inference + review of flagged/uncertain clauses is
  substantially less than the time to author equivalent specifications by hand.
- **H2 (cost scaling differs).** Manual cost scales with method count;
  infer-and-review cost scales with the (much smaller) count of
  flagged/non-discharged clauses — so the advantage widens with codebase size.
- **H3 (quality parity).** The infer-and-review specifications are of comparable
  quality (accuracy against intent, discharge rate) to the hand-written ones, so
  the cost saving is not bought with weaker specs.

**Research question.** *How much human effort does infer-and-review save over
manual authoring, how does the saving scale, and is the saving achieved without a
quality penalty?*

---

## 2. How it would be tested

**Design.** A controlled task study with participants (graduate students /
practitioners with JML or contract familiarity) specifying a common set of
methods under two conditions, counterbalanced:
- **Manual:** author JML from scratch given the source.
- **Infer-and-review:** start from the engine's inferred spec (with
  discharged/flagged status shown) and correct/complete it to acceptance.

**Task corpus.** ~30–50 methods stratified by category (utility, control-flow,
state-modification, etc.) so the cost comparison covers the spectrum where
inference is strong and weak.

**Procedure.**

1. Each participant specifies each method under one condition (Latin-square
   assignment so no participant sees the same method twice and conditions are
   balanced across participants and methods).
2. Record **time-on-task** per method per condition (instrumented editor or
   screen capture).
3. Collect the resulting specifications.
4. **Quality (H3):** validate every produced spec against the same dual oracle
   the thesis uses — manual-intent rating by independent raters + OpenJML
   discharge.
5. **Scaling (H2):** model total cost as a function of method count for each
   condition, using the per-method times and the measured flagged-clause rate.

**Metrics.** Median time-on-task per method per condition (paired by method);
the time ratio (manual / infer-and-review); spec quality (precision vs intent,
discharge rate) per condition; a projected cost-vs-size curve for each condition.

**Analysis.** Paired comparison of time-on-task (Wilcoxon, effect size); quality
comparison to establish parity (H3); the projected scaling curves (H2). The
headline is the time ratio with a quality-parity caveat.

---

## 3. How it would be added to the inferrer tool

This is primarily a human study; the tool's role is to *present* inferred specs
for review and to *instrument* the review.

**Review-mode output `com.jml.inferrer.review.ReviewBundleExporter`.**
Produces, per method, a review artefact: the source, the inferred JML with each
clause tagged discharged / flagged / unsupported (from the existing OpenJML
validation pass), and an editable field for the participant's corrected spec.
Export as a simple web form or an annotated source file the participant edits.
This reuses the validation pipeline's per-clause verdicts already produced by
`--validate`.

**Instrumentation `com.jml.inferrer.review.TaskTimer`.**
Lightweight per-method start/stop timing wrapper around the review form (or a
VS Code extension hook), writing a `times.csv`. Alternatively, instrument via the
editor's telemetry and import.

**Quality pipeline reuse.**
The collected specs (both conditions) are fed back through the engine's
validation path (`inferAndVerify`-style) and the manual-rating protocol from the
inference study, so quality is measured with the exact instruments the thesis
already validates against — no new quality machinery.

**No core-engine change** is required beyond the review-bundle exporter; the
inference itself is unchanged.

---

## Threats and pitfalls

- **Human-subjects approval.** Requires ethics clearance (UQ HREC); budget weeks
  of lead time. This is the gating constraint.
- **Participant expertise variance.** JML fluency varies enormously and dominates
  time-on-task; counterbalancing and a within-subject design control for it, but
  recruit participants of comparable background and report the variance.
- **Learning/anchoring effects.** Seeing the inferred spec may anchor the manual
  condition if not counterbalanced; the Latin-square design and distinct methods
  per condition mitigate this.
- **Ecological validity.** Lab specification of isolated methods is not
  production specification of a whole system; frame the result as a per-method
  cost estimate, and pair it with the scaling model rather than over-claiming
  whole-project cost.
- **Small N.** Recruiting enough qualified participants is hard; power the study
  for the per-method paired comparison, which needs fewer participants than a
  between-subjects design.

## Effort

High (mostly non-engineering): ethics approval (weeks), participant recruitment,
the review tooling (≈ 1–2 weeks engineering), running sessions, and analysis. The
engineering is small; the study logistics dominate.

## Deliverables

A measured time-ratio between manual and infer-and-review specification, a
quality-parity check, and a cost-vs-size projection — the first *direct* evidence
for the economic premise on which the whole adoption argument rests.
