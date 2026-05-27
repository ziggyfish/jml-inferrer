# Experiment 10 — Developer Study of Inferred-Specification Usefulness

**Strengthens:** the adoption claim, with human evidence — the thesis argues
adoption from technical measurements alone, and an examiner will note that
adoption is ultimately a human/organisational question.
**Tier:** 3.

---

## 1. What it tests

The thesis's central claim is about *adoption*: that removing the specification
cost and offering library-boundary capabilities would move formal methods out of
the niche. Every supporting result is technical (accuracy, value to an LLM,
overhead, propagation). This experiment adds the missing human evidence: do real
developers find inferred specifications useful, do the flagged clauses help them
catch real problems, and would they accept the inferred specs into their
workflow?

**Hypotheses.**

- **H1 (bug-finding).** Developers given inferred specifications (and the
  flagged/non-discharged clauses) catch more real defects in a code-review or
  integration task than developers without them.
- **H2 (acceptance).** Developers accept a high fraction of inferred clauses as
  correct and useful, and the flagged-clause review burden is manageable
  (consistent with the low flag rate the inference study reports).
- **H3 (perceived value).** Developers report that inferred specs would be
  worth adopting in their workflow, and identify where they help most (unfamiliar
  APIs, integration boundaries) — the qualitative adoption signal.

**Research question.** *Do inferred specifications help real developers catch
defects and reason about unfamiliar code, and would they adopt them?*

---

## 2. How it would be tested

**Design.** A mixed-methods study with practitioners / graduate developers.

- **Quantitative task (H1):** a controlled code-review or integration task with
  seeded defects (some of which violate an inferred precondition or postcondition
  the dependency's spec would catch). Two groups: with inferred specs available
  vs without. Measure defects found and time.
- **Acceptance task (H2):** participants review a set of inferred clauses
  (tagged discharged/flagged) for methods they understand and mark each
  accept / reject / unsure; record acceptance rate and review time per clause.
- **Qualitative (H3):** a post-task semi-structured interview / survey on
  perceived usefulness, trust, and willingness to adopt, coded thematically.

**Procedure.**

1. Recruit participants; counterbalance the with/without-specs condition across
   tasks and participants.
2. Run the seeded-defect task; record defects found, true/false positives, time.
3. Run the acceptance task; record per-clause verdicts and times.
4. Interview/survey; transcribe and thematically code (two coders, report
   inter-coder agreement).

**Metrics.** Defects found and false-positive rate by condition (H1, with effect
size); clause acceptance rate and per-clause review time (H2); coded themes and a
willingness-to-adopt summary (H3).

**Analysis.** H1: between/within-group comparison of defects found. H2:
acceptance rate vs the inference study's measured precision (do developers'
accept/reject judgements track the dual-oracle accuracy?). H3: thematic summary
with representative quotes — the qualitative adoption evidence the thesis
otherwise lacks.

---

## 3. How it would be added to the inferrer tool

The tool's role is to deliver inferred specs into a realistic review/integration
setting and to instrument acceptance; this is the most human-centred and least
engineering-heavy plan.

**IDE / review surfacing `com.jml.inferrer.review.SpecOverlay`.**
A lightweight presentation of inferred specs in the developer's environment:
either (a) the inferred JML injected as comments on the source (the engine's
default in-place output already does this — participants see the contracts inline
during review), or (b) a minimal VS Code / IntelliJ extension that shows the
inferred contract and its discharged/flagged status on hover. Option (a) needs no
new tooling; option (b) is a small extension over the existing annotated output.

**Acceptance capture `com.jml.inferrer.review.ClauseVerdictCollector`.**
Reuses the `ReviewBundleExporter` from Experiment 07 to present each clause with
its validation status and capture accept/reject/unsure plus timing, writing a
`verdicts.csv`.

**Seeded-defect harness.**
A curated task codebase with known seeded defects, half of which are catchable
via an inferred contract violation. The inferred specs are produced by the normal
pipeline; no engine change is needed — the experiment is about *presentation* and
*measurement*, not new inference.

**Reuse.** The engine's in-place annotated output is the primary delivery
mechanism; the review-bundle exporter and the validation verdicts are shared with
Experiment 07.

---

## Threats and pitfalls

- **Human-subjects approval (UQ HREC)** is the gating constraint; lead time in
  weeks. Plan alongside Experiment 07 (they can share an ethics application and
  participant pool).
- **Recruitment and N.** Qualified-developer recruitment is hard; a smaller
  mixed-methods study with strong qualitative depth may be more achievable and
  defensible than an underpowered quantitative one. Be explicit about which
  hypotheses are powered and which are exploratory.
- **Hawthorne / novelty effects.** Participants may over-engage with a novel
  tool; mitigate with a realistic task framing and by measuring acceptance
  against the independent dual-oracle accuracy (H2 cross-check).
- **Task realism.** Lab tasks under-represent real integration; frame findings as
  indicative adoption signal, triangulated with the technical results, not as
  proof of field adoption.
- **Researcher bias in qualitative coding.** Two independent coders, reported
  agreement, and a pre-registered codebook.

## Effort

High (mostly non-engineering): ethics approval, recruitment, task design, running
sessions, transcription and coding. Engineering is small (review surfacing +
verdict capture, ≈ 1 week, much shared with Experiment 07). Best run as a
companion to Experiment 07 under one ethics application.

## Deliverables

Quantitative defect-finding and clause-acceptance results plus a thematic
adoption analysis with practitioner quotes — the human evidence for the adoption
claim that no technical measurement can supply, and the most direct answer to the
examiner objection that the adoption thesis is argued from technical results
alone.
