# Pass 6 — Reviewer Red-Team Report

Article: *Embedding Inferred JML Contracts in Java Bytecode and OpenAPI Specifications*
Venue assumed: SANER (Research Track, double-anonymous, IEEEtran)
Reviewer mindset: adversarial Reviewer 2, sceptical of engineering-flavoured papers.

## Critical

### C1. Compressed-JAR overhead is unmeasured; bytecode-size overhead may misrepresent real distribution cost
- **Where:** §V Empirical, table~I and tab:opt; threats does not address it.
- **Objection:** Distribution JARs are DEFLATE-compressed. The reported 4.63–10.20% delta is on raw class-file bytes summed across entries; reviewers will ask whether the constant-pool strings compress out, shrinking real-world JAR delta substantially. Conversely, the v3 negative result (per-method DEFLATE) becomes more puzzling without a baseline-JAR-compression measurement.
- **Rebuttal needs to say:** the harness can be re-run to report compressed-JAR size delta; preliminary expectation is that the delta narrows but does not vanish because UTF-8 entries with high entropy after token encoding compress only modestly. We should report both numbers.
- **Needs new experiments?** Yes — small. Re-zip embedded vs. original JAR; compare. One day of work.

### C2. OpenAPI extension claims are by-construction only; RQ4 is empirically unanswered
- **Where:** §I RQ4 ("Does an OpenAPI extension family integrate with existing OpenAPI tooling without modification?"), §III.C, §VI threats external validity.
- **Objection:** RQ4 is posed empirically but the answer is "validated by construction"; no concrete OpenAPI documents from a real microservice were processed, no swagger-parser/openapi-generator runs are shown, no quantitative roundtrip measurement at the service layer.
- **Rebuttal needs to say:** add at least one concrete OpenAPI 3.x document (e.g. a public sample like the Petstore or one of springdoc-openapi's emitted descriptions) and demonstrate end-to-end embedding + parser preservation. Currently the OpenAPI side is a single ~12-line code listing in the format-design section.
- **Needs new experiments?** Yes — small. One Petstore-or-similar fixture, two parser runs, three numbers in a table.

### C3. The contribution is framed as engineering; reviewers will ask for the research question
- **Where:** §I.
- **Objection:** "We propose a uniform mechanism" reads as a tool paper. The four RQs are operational ("Can X be done?", "What is the overhead?") rather than scientific ("Under what conditions does X generalise?", "Why does Y dominate Z?").
- **Rebuttal needs to say:** the empirical contribution is the *format design lessons* (§V.E "What is empirical about this optimisation") — twelve-token dictionary, default-omission, v1→v2 reduction. Reframe one RQ as a comparative empirical question over format variants, which is what tab:configs already answers.
- **Needs new experiments?** No — re-framing only. Move tab:configs analysis from §V.F into the introduction's contribution framing.

## Major

### M1. Single-inferrer dependency for the "real specs" run
- **Where:** §V.D, throughout.
- **Objection:** All 10,332 "real" specs come from the authors' own inferrer (Article 1's tool). The "lossless transport" claim is necessarily about that one tool's clause vocabulary.
- **Rebuttal needs to say:** the format is independent of inferrer (Discussion §VI.B already says this), but generality of the *byte overhead and reduction percentages* depends on the clause shape distribution. Demonstrating one alternative-inferrer roundtrip (e.g., a tiny Daikon-imported spec set) would substantially harden the claim.
- **Needs new experiments?** Yes — small. Could be deferred to follow-up section.

### M2. Only 3 of 10 protocol libraries
- **Where:** §V.A.
- **Objection:** Article 1's protocol identifies 10 libraries; this paper reports 3 and calls the rest "mechanical." Reviewers will ask for the mechanical run.
- **Rebuttal needs to say:** the harness is uniform across libraries; the additional seven (Math, jOOL, Vavr, jsoup, JFreeChart, JUnit, AssertJ) can be added without conceptual change. We should run them and add the rows.
- **Needs new experiments?** Yes — small, mechanical: harness reruns.

### M3. 917/3,249 Commons Lang methods dropped — "100% lossless" is on a subset
- **Where:** §VI threats construct validity, §V.D 4th paragraph.
- **Objection:** 28% of source-inferred Commons Lang methods are never tested because the harness's name+arity descriptor heuristic can't distinguish overloaded same-arity methods. The headline claim is therefore conditioned on harness success, not on embedder success on the full corpus.
- **Rebuttal needs to say:** the 917 are lost in *measurement*, not in embedding. The embedder itself never sees them. A full type-resolving harness would close this gap with no embedder change. Article already states this, but emphasis can be sharper, e.g., by stating the headline as "100% lossless on every spec the harness embeds; 71.8% measurement coverage on Commons Lang specs-with-clauses."
- **Needs new experiments?** Optional — better harness; or accept the wording fix.

### M4. Per-class budget never quantified
- **Where:** §III.D (sidecar fallback), §IV.A.
- **Objection:** The sidecar JAR is described as a fallback for "specifications that exceed the per-class bytecode budget"; the budget is never numerically given, and the data does not show how often it kicks in across the 20,546 methods.
- **Rebuttal needs to say:** the JVM constant-pool limit is 65,535 entries and the per-attribute limit is 4 GB; in practice the sidecar never fires on any of the three libraries (no class reached either bound). We should report this explicitly with a sentence in §V.D.
- **Needs new experiments?** No — instrumentation of existing runs; sentence-level edit.

### M5. Throughput variability not characterised
- **Where:** §V.D Throughput paragraph; threats now lists "across 39 runs" but no IQR/range per library.
- **Objection:** Medians are reported but no measure of dispersion. A reviewer will ask whether the 22,000 m/s Commons IO median is 21,500–22,500 (tight) or 8,000–35,000 (wide), because the operational claim ("comfortably support per-PR-comment workflows") depends on the lower quartile, not the median.
- **Rebuttal needs to say:** raw per-run data are in the replication package (Pass 5 disclosure); reporting IQR alongside median in the table would close the gap.
- **Needs new experiments?** No — recompute from existing 39 runs and add a column.

### M6. The "negative test" is one class, not a corpus-scale property
- **Where:** §V.D Negative-test paragraph.
- **Objection:** Loading `StringUtils` via a class loader that does not see `JmlSpec` is an *existence proof*, not a property. The article claims consumer tolerance broadly; reviewers will note the test is one method invocation.
- **Rebuttal needs to say:** rerun the loader across every class in the embedded JARs (20,546 classes × 3 libraries) and report the percentage that load. Expectation: 100%.
- **Needs new experiments?** Yes — but trivially small: one loop in the existing harness.

## Minor

### m1. Why @JmlSpecs rather than custom attribute? — qualitative arguments only
- **Where:** §VI.A Discussion.
- **Objection:** Three reasons are listed (tool visibility, repeatable annotations, forward compatibility) without quantitative comparison against a prototype custom-attribute embedder.
- **Rebuttal:** the choice is grounded in *toolchain compatibility*, which is a binary property rather than a measured one. The discussion could acknowledge that the trade-off is qualitative and an attribute-based alternative is left for future work.
- **Needs experiments?** No.

### m2. The twelve tokens — why twelve?
- **Where:** §III.A Token-encoded clause strings.
- **Objection:** The choice of twelve is unexplained. The learned-dictionary experiment shows 28 is also reasonable; the gap (12 vs. 28) is 0.59 percentage points.
- **Rebuttal:** twelve is the empirical sweet spot — every token in the dictionary represents > 0.5% of corpus bytes; below that frequency the encoding adds dictionary bookkeeping for marginal gain. A sentence in §III.A would close this.
- **Needs experiments?** No.

### m3. Version skew handling
- **Where:** §III.A Backward compatibility paragraph.
- **Objection:** `version() default = "2"` implies a versioned format but the article does not say what a future v3 reader does with a v2 annotation, nor what a v2 reader does with v1 strings encoding tokens it does not know.
- **Rebuttal:** the reader is backward-compatible (already stated). Forward compatibility (older reader, newer writer) needs an explicit policy — e.g., "unknown members are skipped, unknown tokens fall through as control characters."
- **Needs experiments?** No — one paragraph.

### m4. "Order is the array order; requires clauses are emitted in source order" — but the array ordering across kinds (requires before ensures before signals) is unstated
- **Where:** §III.A.
- **Objection:** Two writers emitting the same logical spec could produce different annotation byte sequences if they pick different cross-kind orderings, breaking byte-level roundtrip with a third-party writer.
- **Rebuttal:** the convention is alphabetical-by-member-name (the JVM annotation format already enforces this). One sentence in §III.A.
- **Needs experiments?** No.

### m5. "Approximately 700 lines of code" / "approximately 250 lines" — not reproducible
- **Where:** §IV.
- **Objection:** Soft numbers without commit hash are not reproducible.
- **Rebuttal:** pin to the GitHub tag the replication package references; or report exact LOC at submission time.
- **Needs experiments?** No.

### m6. README contradicts the actual paper
- **Where:** `journal/article2/README.md`.
- **Objection:** The README says the article is about *service-boundary LLM test generation* and is *not yet started*. The actual paper is about *bytecode/OpenAPI embedding* and is fully drafted.
- **Rebuttal:** README is stale and harmless because reviewers won't see it; but it should be reconciled before the artefact is published. (Pass 7 / task #9.)
- **Needs experiments?** No.

## Summary

- **Critical (must address):** C1 compressed-JAR overhead (small experiment), C2 OpenAPI empirical evaluation (small experiment), C3 framing (edit only).
- **Major (should address if time permits):** M1 alt-inferrer roundtrip, M2 the remaining seven libraries, M3 wording sharpening on 917/3,249, M4 per-class budget disclosure, M5 IQR alongside medians, M6 corpus-scale negative test.
- **Minor (can address in camera-ready):** m1–m6.

If only one of the Critical items can be addressed before submission, **C2 (OpenAPI empirical run)** has the highest expected reviewer-score lift, because it converts an answered-by-construction RQ into an answered-by-measurement RQ.
