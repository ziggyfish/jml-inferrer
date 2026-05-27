# Pass 6 — Reviewer Red-Team Report (Article 3 → ICSE 2027)

*Run date: 2026-05-26. Supersedes / supplements `REVIEWER_REDTEAM.md` (the original SANER-era redteam, content still largely applicable).*

Reviewer mindset: adversarial Reviewer 2 at an A* venue with high acceptance bar. Will hit hardest on novelty, generalisability, baseline strength, and the gap between the *measured* claim and the *interpreted* claim.

## Critical

### C1. The downstream claim is unproven; only the structural-prerequisite claim is measured
- **Where:** §I (RQ framing), §V.E (downstream subsection), §IX (Conclusion).
- **Objection:** The paper measures that the second pass *adds clauses* and that those clauses *are of shapes* the single pass cannot produce. It does not measure whether those additional clauses materially improve any downstream tool — better test generation, more bugs caught, better LLM completions, fewer false positives. The §V.E downstream signal is a single 8-class test-count delta (+9.1% mean) acknowledged as preliminary. A reviewer will say: "you've measured the input, not the output."
- **Rebuttal needs to say:** the downstream RQ is explicitly identified as future work in §IX. The contribution being made is the *structural prerequisite* — the additional clauses exist on 5 libraries — which is necessary for the downstream gain to be possible at all.
- **Needs new experiments?** Optional. A corpus-scale PIT-mutation re-run on Lang under both spec sets would close the gap from "structural" to "downstream-impact" but is ~2 days of work.

### C2. The "compositional refinement" baseline is one specific single-pass implementation
- **Where:** §VII Threats external validity.
- **Objection:** The paper compares against the inferrer's existing `InterproceduralAnalyzer`. A reviewer will ask: what if a more careful single-pass implementation, with even modest enhancements (e.g., propagating through one enclosing guard), already captures most of the gap?
- **Rebuttal needs to say:** the chosen baseline is the *deployed* one; the categorical structural argument (single-pass *cannot by construction* produce disjunction over polymorphic dispatch candidates from a sibling-cache lookup) holds against any single-pass implementation.
- **Needs experiments?** Optional. Could implement a "single-pass with one guard look-up" and re-run.

### C3. Guava is excluded
- **Where:** §VII Threats external validity.
- **Objection:** The predecessor papers report on Guava. This paper drops it ("source-jar size pushes the harness's parsing phase beyond the budget"). A reviewer will read this as "the analyser doesn't scale to Guava" or "the result didn't hold on Guava". Either reading is bad.
- **Rebuttal needs to say:** the exclusion is harness-engineering, not analyser-correctness. The §III algorithm has no per-library coupling.
- **Needs experiments?** Yes — small, mechanical. One overnight run with `-Xmx16g` or a streaming source-jar reader is likely sufficient.

## Major

### M1. The shape categorisation is regex-based and the "other" bucket is unanalysed
- **Where:** §V.B (Table~\ref{tab:shapes}), §VII Threats construct validity.
- **Objection:** The bucketing is regex-based; the *other* bucket holds 0.2--1.7% of clauses, described as "arithmetic comparisons our regex does not match (e.g., `abs(x) <= K`)". A reviewer will ask: are you sure none are actually polymorphic-dispatch or branch-conditional clauses misclassified? On 42,370 total, that's 85--720 unaccounted-for per library.
- **Rebuttal needs to say:** the regex precedence is structural-shape-first, content-second. A sample inspection of 100 *other*-bucket clauses would close the doubt. ~2 hours.

### M2. The version-step result (§V.D) is one library at one 2-year delta
- **Where:** §V.D, abstract, conclusion.
- **Objection:** Commons Lang 3.12.0 → 3.14.0 is a single instance. A reviewer will ask whether the dataset is large enough to support the framing "the propagation produces a tractable behavioural-compatibility artefact".
- **Rebuttal needs to say:** the §V.D result is intentionally a single instance; the structural claim is the 5-library measurement. A 2-version diff on a second library (Commons IO 2.11.0 vs 2.13.0, or Math 3.5 vs 3.6.1) would take an hour and defuse the objection.

### M3. The "414-line analyser" is reported by line count, not complexity or correctness
- **Where:** §IV.
- **Objection:** LOC is not a meaningful complexity measure. Cyclomatic complexity, number of methods, coverage from JaCoCo would all be more informative.
- **Rebuttal needs to say:** add (a) cyclomatic complexity, (b) JaCoCo coverage. The "2 bugs found during corpus run" point in §IV already addresses the implicit trust question.

### M4. Polymorphic-dispatch disjunctions: precision vs informativeness
- **Where:** §III.E, §V.B, §VI.
- **Objection:** The paper reports "1.8--9.7%" polymorphic-dispatch disjunctions. A reviewer will ask: are these disjunctions over 2 candidates (informative) or 20+ candidates (vacuously easy to satisfy)?
- **Rebuttal needs to say:** add a histogram of candidate-set sizes per disjunction. Likely most are 2--3 candidates; a tail of 20+ is a known CHA-precision issue and addressable with RTA.

### M5. The "branch-conditional implications dominate" claim depends on the four-of-five framing
- **Where:** abstract, §V, conclusion.
- **Objection:** "Dominate on four of five libraries" — the fifth (jOOL) has them as a *third*, not the largest single category. A reviewer might say the headline does not hold uniformly.
- **Rebuttal needs to say:** tighten to "branch-conditional implications are the dominant single category on the majority of libraries and are substantial (>30%) on every library".

### M6. The runtime claim is single-platform, single-Java-version
- **Where:** §V.C, §VII threats.
- **Objection:** "44 seconds total" is platform-specific.
- **Rebuttal needs to say:** Pass 5 added the platform disclosure to threats (OpenJDK 21 G1GC on Windows 11). The qualitative claim (no fixpoint iteration fires; second pass is bounded by single-pass cost) is platform-independent.

## Minor

### m1. The `\thanks{}` footnote in the title block is a non-standard ICSE convention
The `\thanks` is standard IEEEtran behaviour for replication notes; it saves half-a-column.

### m2. The "five libraries spanning four idiom families" framing is undermotivated
Add explicit per-library motivation in §V.A (Lang = utility delegators, IO = stream abstractions, Math = numerical, jOOL/Vavr = generic-heavy functional).

### m3. Font shape warning around `\thanks{}`
Silenced via `\DeclareFontShape` workaround.

### m4. The §V.E "downstream signal" is preliminary and disclaimed five times
Tighten to one short paragraph; the +9.1% mean test-count delta should lead, not be buried in caveats.

### m5. The "two bugs uncovered" subsection in §IV could be framed as methodological strength
One sentence sharper: "corpus run finds bugs the unit suite misses".

## Summary

- **Critical (must address):** C1 framing as structural-prerequisite (one-sentence sharpening), C2 baseline-strawman defence (~1 paragraph in threats), C3 Guava inclusion (overnight run).
- **Major (should address if time permits):** M1 inspect *other* bucket sample, M2 second version-step, M3 add coverage, M4 candidate-set-size distribution, M5 abstract wording tighten, M6 already mitigated.
- **Minor (camera-ready):** m1–m5.

**Highest single-shot improvement:** including Guava (C3). It's the most-named gap by the predecessor papers and the easiest to fix definitively.

**Lowest-cost improvement with high reviewer impact:** abstract tightening for M5 (uniform "substantial" rather than uneven "dominant"). Edit only, ~10 minutes.
