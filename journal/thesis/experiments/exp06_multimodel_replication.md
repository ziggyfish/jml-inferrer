# Experiment 06 — Multi-Model Replication of the LLM Test-Generation Study

**Strengthens:** external validity of RQ2; the thesis currently defends only the
*ordering* of conditions, not the magnitudes, on a single model family.
**Tier:** 2.

---

## 1. What it tests

The headline value result (+272% test count, +40.7 pp mutation score for
specification-guided generation) was obtained with one model family (Gemini).
The thesis defends the *ordering* P1 < P2 < P3 < P4 as the contribution and
explicitly flags that magnitudes may be model-specific. This experiment tests
whether the effect — both ordering and magnitude — transfers across models.

**Hypotheses.**

- **H1 (ordering transfers).** The condition ordering P1 < P2 < P3 < P4 on
  mutation score holds for every model tested.
- **H2 (magnitude varies but stays large).** The P1→P3 improvement remains
  large (well above any conventional small-effect threshold) across models,
  though its size differs.
- **H3 (the P2-vs-P3 inversion is robust).** More tests without an oracle (P2)
  underperform specification-guided tests (P3) on mutation score for every
  model — the thesis's key methodological finding.

**Research question.** *Does the value of inferred specifications for test
generation transfer across LLM families, in direction and in approximate
magnitude?*

---

## 2. How it would be tested

**Models.** A spread across families and capability tiers: a frontier proprietary
model (e.g. GPT-class), a second proprietary family (Claude-class), the existing
Gemini result as the anchor, and at least one open-weights model (e.g. a
Llama/Qwen coder) to test whether the effect needs frontier capability. Hold
temperature, run count, and prompts fixed across models.

**Design.** Re-run the existing four-condition study (P1/P2/P3/P4) unchanged,
varying only the model. Same 312-method corpus, same five-runs-per-condition,
same metrics (test count, compile rate, pass rate, mutation score).

**Procedure.**

1. For each model, run all four conditions with `ExperimentRunner`.
2. Compute per-model: condition means, P1→P3 deltas (count and mutation), and the
   P2-vs-P3 comparison.
3. **Cross-model analysis:** is the ordering preserved everywhere (H1)? Are the
   magnitudes large everywhere though varying (H2)? Does the P2/P3 inversion hold
   everywhere (H3)? Report a model × condition table and a model × effect-size
   table.

**Metrics.** Per-model condition means and paired deltas with CIs and effect
sizes; a cross-model summary establishing the qualitative invariants (ordering,
inversion) and the magnitude spread.

**Analysis.** The defensible claim the thesis already makes (ordering) is
strengthened to "ordering invariant across N model families"; the magnitude
becomes a reported range rather than a single point. If any model breaks the
ordering, that is itself an important finding about where the effect's mechanism
depends on model capability.

---

## 3. How it would be added to the inferrer tool

`ExperimentRunner` already parameterises the model (`--model`) and logs raw
responses; the work is multi-provider client support and result aggregation.

**Generalise the model client.**
The runner currently targets the Gemini `generateContent` endpoint. Introduce a
`com.jml.inferrer.experiment.LlmClient` interface with implementations
`GeminiClient` (existing logic), `OpenAiClient`, `AnthropicClient`, and a generic
`OpenAiCompatibleClient` (for open-weights models served behind an OpenAI-style
API, e.g. via vLLM/Ollama). Select via `--provider` + `--model`. Each
implementation normalises to the same request (prompt, temperature, max tokens,
thinking-budget-off where applicable) and response (raw text) so the rest of the
pipeline is unchanged.

**Robust extraction (shared with Experiment 04).**
The `extractJavaCode` + compile-gate fixes from Experiment 04 are a prerequisite,
because different models format code differently; the compile gate prevents a
model's formatting quirk from masquerading as a low score.

**Result aggregation `com.jml.inferrer.experiment.MultiModelAggregator`.**
Adds a `model` and `provider` column to the metrics output (the analysis scripts
already accept a model identifier column, per the thesis's replication-package
design) and produces the model × condition and model × effect-size tables.

**Cost control.** A `--budget` cap and per-provider rate-limiting; the study is
~6,240 generations per model, so multiply by the number of models — make the
runner resumable so a provider outage does not lose a run.

**Reuse.** The whole four-condition harness, the PIT setup, and the statistics
scripts; only the client layer and aggregation are new.

---

## Threats and pitfalls

- **Cost.** N models × four conditions × 312 methods × five runs is the most
  API-expensive experiment; budget and resumability are essential. Open-weights
  models run locally to cap cost.
- **Provider drift.** Models update server-side; record exact model IDs/snapshots
  and dates, and treat each as a point-in-time measurement.
- **Extraction parity.** A model that the extractor handles poorly will look
  worse for harness reasons, not capability reasons — the compile gate and a
  per-model extraction-failure audit guard against this.
- **Training contamination.** All models likely saw Commons Lang; the thesis's
  existing argument (P1 ≪ P4 rules out pure recall) applies per model and should
  be restated.

## Effort

Medium. Client interface + 3 implementations ≈ 1–2 weeks; the runs are
cost/time-bound (days of wall-clock + budget); aggregation/analysis ≈ 1 week.
Lowest-risk big win for external validity.

## Deliverables

A model × condition results table and a cross-model effect-size summary
establishing that the ordering and the P2/P3 inversion are model-invariant and
the P1→P3 magnitude is large across families — directly answering the
single-model threat the thesis names.
