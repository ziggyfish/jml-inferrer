# Article 3 — Reviewer Red Team (Pass 6)

Adversarial reading of the submission as Reviewer 2. Severity scale:
Critical (paper must change before resubmission), Major (rebuttal
needs new analysis or extensive rewrite), Minor (rebuttal can be a
paragraph edit). Items below are objections the article must
anticipate, ordered by severity within each tier.

## Critical

### C1. "What does 'refined' mean for downstream behaviour?"
- **Objection.** The paper measures structural addition (clause counts
  and shapes) but never shows that the added clauses are
  *semantically correct* against the code or that they change any
  downstream tool's behaviour. A reviewer will ask: if 42,370 new
  clauses are added but none of them help a test generator, IDE, or
  verifier, the contribution is unclear.
- **Where it lands.** Abstract last sentence, RQ1 framing in
  Section 5.2, Discussion 6.1.
- **Rebuttal.** Section 6.4 ("Limitations") already frames the
  downstream-impact study as planned follow-up. The article's
  positioning needs to make clearer that the structural claim is
  prerequisite, not equivalent, to the downstream claim — i.e. that
  before asking whether richer specs help, one must demonstrate that
  the richness exists. Recommend tightening §1 paragraph 3 to make
  this prerequisite framing explicit.
- **Needs new experiments?** No. The LLM-downstream experiment is
  separately in flight (gemini-2.5-flash, P3/P3C comparison on
  11 classes × 5 runs); if it lands before resubmission, can be
  added as a section 5.4 "downstream signal" rather than a primary
  result.

### C2. "60% callee-resolution rate is not a measurement, it's a bug."
- **Objection.** The threats section admits 25--47% of call sites
  fail simple-name matching. A reviewer will read this as a
  measurement instrument that's fundamentally unsound, not as a
  lower bound.
- **Where it lands.** Threats §7 construct validity, Section 5
  results table footnote.
- **Rebuttal.** The lower-bound framing is sound: a missed call
  site can only *under-count* additions, not over-count. But the
  reviewer may push for an upper-bound estimate too, or for a
  full type-resolving harness run on a subset. Recommend running
  the harness on one library (Commons IO, smallest) with JavaParser's
  SymbolSolver enabled, comparing the additions count, and reporting
  the delta as a calibration. ~1 day of work; would meaningfully
  strengthen the construct-validity argument.
- **Needs new experiments?** Yes, but small — single-library calibration.

## Major

### M1. "How is your CompositionalAnalyzer different from a partial WP transformer?"
- **Objection.** The algorithm section calls itself a "lifting step,
  not a complete WP transformer", but does not precisely characterise
  what it can and cannot do. A formal-methods reviewer will want a
  list of which WP transformer cases are covered (sequential
  composition over guarded calls — yes; alias-aware substitution — no;
  loop body — no; arithmetic statement — no).
- **Where it lands.** Section 3.4 ("What the algorithm is and is not")
  partially addresses this but informally.
- **Rebuttal.** Add a small table in Section 3 that enumerates the
  WP cases the pass handles vs delegates vs ignores. Easy to write,
  high reviewer-satisfaction return.

### M2. "You claim novelty against KeY/OpenJML but they verify, not infer."
- **Objection.** The related-work comparison table positions the
  pass against KeY and OpenJML SC, but those are verifiers (consume
  hand-written specs), not inferrers. The comparison is apples to
  oranges. A reviewer who works on KeY will object that the article
  invents a comparison axis to win on.
- **Where it lands.** Table 3 (related.tex novelty positioning).
- **Rebuttal.** The comparison is along three orthogonal axes (produces
  JML, propagates compositionally, discharges via SMT); KeY is at
  (no, yes, yes), our pass at (yes, yes, via OpenJML). The narrative
  text following the table addresses this but should be more explicit
  that the table is a position-on-three-axes map, not a head-to-head
  comparison.

### M3. "Why these five libraries and not, e.g., Spring or Netty?"
- **Objection.** The five libraries are all "library code" (utility,
  I/O, math, functional, collections). Application code, framework
  code, and middleware (Spring, Netty, Tomcat) have different call-graph
  shapes and may not show the same compositional gain.
- **Where it lands.** Threats §7 external validity.
- **Rebuttal.** The four-idiom-family framing is intentional and the
  paper acknowledges generalisation to framework/application code is
  open. A reviewer may want a sanity-check run on one application
  codebase. Adding Spring's beans module (~150 classes) would be a
  ~30-minute additional measurement and a meaningful external-validity
  strengthener.

## Minor

### m1. "Avg new clauses per refined method is reported, but not the variance."
- **Objection.** Mean 13.37 with max 665 on Math is noted but the
  variance / IQR / median are not. A reviewer reading the dispersion
  paragraph may push for a histogram or boxplot.
- **Rebuttal.** Add a single boxplot figure if space permits;
  otherwise add a sentence reporting the IQR computed from the
  per-method output.

### m2. "Section 4 says 414-line analyser; what counts as a line?"
- **Objection.** Inconsistent LOC reporting (blank lines, comments,
  imports counted differently).
- **Rebuttal.** Replace "414-line" with "approximately 400 LOC
  (excluding blank lines and imports)" or omit the number; the
  size is not load-bearing for any claim.

### m3. "9-page conference paper is fine for SANER, tight for ICSE."
- **Objection.** ICSE has a 10-page main body limit (plus refs).
  The current 9 pages is comfortable but leaves little room for the
  downstream-impact section if it lands.
- **Rebuttal.** Plan for 10 pages once the LLM-downstream signal is
  added; current 9 leaves headroom.

## Items NOT to weaken in response to reviewer pushback

- The "single pass is not subsuming" claim is exact for the
  measured inputs. Do not soften to "may not be subsuming" — the data
  is exact, not statistical.
- The branch-conditional-shape dominance claim holds on 4 of 5
  libraries; do not over-claim to "all five" (jOOL has null-check
  dominance).
- The 44 s total runtime is real wall-clock on the measurement machine.
  Do not present it as a theoretical complexity bound.
