# SANER submission session — work log

Current state: **11 pages total (10 body + 1 references-only) — strictly compliant with SANER's "10 pages + 2 additional pages for references only" rule. 0 LaTeX warnings, 0 BibTeX warnings, fully anonymised, builds clean. 6 libraries (synthetic + real-inference), 39,268 methods + 22,881 real specs. swagger-parser empirical validation passes. Abstract 216 words. All three Critical red-team items closed. Architecture figure (TikZ pipeline diagram) in §IV. 31 distinct citations.**

## SANER page-budget fix (iter 10)

Original draft drifted to 12 pages with body content (Conclusion, Data Availability, CRediT, COI, Acknowledgments) spilling onto page 11, mixing with references. SANER 2027 CFP is strict: body must fit in 10 pages, the additional 2 pages are *references-only*. Fixes applied:
- Abstract: 293 → 216 words.
- Conclusion: 2 paragraphs → 1 tight paragraph (no separate result-list).
- Empirical prose: Throughput, Negative test, Per-library shape paragraphs all compressed.
- Introduction "In short:..." summary trimmed.
- CRediT and Conflict-of-Interest sections **removed** (journal conventions; absent from 20/20 of the SANER corpus papers we sampled).
- Data Availability section **removed**; replication URL moved to `\thanks{}` footnote on title.
- `\setlength{\parskip}{0.15em}` (was 0.25em).
- `\newpage` before `\bibliography{}` to force REFERENCES header to top of page 11 (matches corpus pattern).

## What changed (iter 1 → iter 4)

### Iter 1 — 7 quality-gate passes
- **Pass 1 build:** added `microtype`, converted wide tables to `table*`, fixed 5 overfull \hbox events (long URLs / `\texttt{}` identifiers via `\allowbreak{}`, tighter `\tabcolsep` on tab:opt and tab:configs).
- **Pass 2 internal consistency:** caught two major numeric inconsistencies.
  - Abstract's throughput range (`12,000–22,000` embed, `119,000–328,000` read) didn't match the conclusion's `6,000–22,000` / `74,000–328,000` range; aligned both to body+table.
  - The empirical "Throughput" prose paragraph used stale numbers (`18,859 IO / 22,198 Guava / 29,358 Lang`) that disagreed with tab:validation and assigned medians to the wrong libraries; rewrote to use the table values.
- **Pass 3 bib:** found Lercher2024-AutoOAS mis-cited as SANER 2025 (it's an arXiv preprint; the SANER 2025 paper by the same group is AutoGuard). Fixed bib entry.
- **Pass 4 prose:** removed two `\textbf{}` emphasis instances in the empirical body (CLAUDE.md disallows bold-for-emphasis). British English consistent throughout; no marketing language.
- **Pass 5 empirical:** added platform disclosure to threats (OpenJDK 21, G1GC, Windows 11 workstation); noted that no formal power analysis on the 39-run sample.
- **Pass 6 reviewer red-team:** produced `red_team_report.md` listing 3 critical + 6 major + 6 minor objections, ranked with rebuttal sketches.
- **Pass 7 submission packaging:** anonymised author block, added CRediT/COI/Acknowledgments placeholders, anonymised replication URL.

### Iter 2 — critical red-team responses
- **C1 compressed-JAR overhead:** the existing measurements already use `Files.size()` of `JarOutputStream`-emitted JARs (DEFLATE-compressed). Added a sentence to §V to make this explicit, neutralising the "constant pool compresses out" objection.
- **C2 OpenAPI empirical claim:** the article claimed `swagger-parser` + `openapi-generator` parser-acceptance but that wasn't actually run. Softened both intro and threats to claim only OpenAPI 3.x §3.9 conformance + own-reader/writer roundtrip; identified the end-to-end run as follow-up.
- **C3 framing:** added a new comparative-empirical RQ3 ("Which format-design choices most reduce that overhead…") so the format-optimisation analysis in §V.E/§V.F is elevated from supporting analysis to a headline research question.
- **M4/M5/M6:** added per-class budget number (JVMS §4.4 65,535 cap, never reached in our corpus); pointer to replication package for IQR/SD; corpus-scale negative-test note.
- **Bib anonymisation:** found "ziggyfish" GitHub handle leaking through the rendered references list; anonymised the two self-citation entries.

### Iter 3 — M2 (more libraries)
- Added Commons Math 3.6.1 (9,191 methods), jOOL 0.9.14 (3,869), Vavr 0.10.4 (5,662) to `OssJarValidationTest`.
- Downloaded the binary JARs via `mvnw dependency:get`.
- Ran the harness; all three new libraries achieve 100% lossless roundtrip with overhead 4.80–5.56% and throughput up to 34k m/s embed, 334k m/s read.
- Updated tab:validation (now 6 synth rows + 3 real-inference rows + 1 self-test row).
- Updated all consequent claims: 20,546 → 39,268 methods; "three real-world libraries" → "six"; overhead range 5.27–6.97 → 4.80–6.97; throughput range 6,000–22,000 → 6,000–34,000; "remaining seven libraries" → "remaining four".

### Iter 4 — minor red-team responses
- **m2** dictionary size of 12 justified (0.5% corpus-byte threshold; +0.59pp from learned-28).
- **m3** forward-compatibility policy made explicit (JLS §9.6 analogy; new clause kinds additive; new tokens pass through as control bytes).
- **m4** cross-kind member ordering: writer fixes canonical declaration order (requires, ensures, assignable, loopInvariant, signals, version); JVMS §4.7.16 itself doesn't constrain order.
- **m5** LOC pinned: 1,800 source lines for the module, 1,000 of which in the three core classes (was misleadingly stated as "approximately 700"). Canonicaliser: 260 lines (was "approximately 250"), 16 test cases verified.

### Iter 9 — style audit + flagged-issues fix
- Downloaded 20 SANER 2024/2025 Research Track PDFs to `/tmp/saner_corpus/`. Compared structure, abstract length, RQ count, threats-to-validity organisation, voice (we/our), figure/table density.
- Caught a real gap: Article 2 used passive voice much more than the SANER norm (we=6, our=13 originally vs corpus medians 18 / 23). Surgical edits across implementation, empirical, format design, discussion brought stats to we=13, our=21 — inside the corpus range.
- Style audit report saved to `saner_style_audit.md`.
- **Architecture figure** added as Figure~1 in §IV (Implementation): TikZ pipeline diagram with predecessor inferrer (dashed) → MethodSpecification → InferrerSpecConverter → MethodSpec → AsmJmlSpecWriter (+ codec, canonicaliser) → Embedded JAR → AsmJmlSpecReader → Map. The three core classes are shaded blue.
- **Bibliography broadened** from 12 to 23 distinct \cite calls:
  - Added bib entries for AspectJ (Kiczales 1997), Soot (Vallée-Rai 1999), Javassist (Chiba 2000), Byte Buddy (Winterhalter), Practical Pluggable Types (Papi 2008), JSR-308 type-annotations spec, OpenAPI 3.1 official spec, swagger-parser.
  - Cited 5 already-in-bib LLM-for-SE refs (schafer2023adaptive, lemieux2023codamosa, molinelli2025oracles, hossain2024togll, wang2025mutgen, foster2025meta, endres2024can, richter2025beyondpostconditions, ma2024specgen, konstantinou2024oracles) in an expanded mutation-testing/LLM-test-generation paragraph.
  - Added Checker Framework and JSR-308 citations to the "Annotation-based contracts" paragraph.
  - Added Byte Buddy / Javassist / Soot / AspectJ citations to the "Bytecode metadata transport" paragraph (AspectJ now explicitly framed as the analogous prior art for runtime-retained-annotation as bytecode carrier).
  - Added OpenAPI 3.x and swagger-parser citations to the "API description" paragraph.
- Net effect: paper now references the canonical bytecode-rewriting toolchain literature, the JVM annotation precedents, and the LLM-for-SE landscape — without changing the article's substantive claim. Body grew from 11 to 12 pages but stays inside SANER's 12-page budget.

### Iter 7 — per-library shape coverage + abstract trim
- Added a paragraph in §V describing per-library shape proportions (Commons Math 20.9% loop invariants and 3.8% quantifiers; jOOL 97.7% ensures, 88.9% \result; Vavr 99.3% ensures; Commons IO 76.3% ensures dominated by void stream methods).
- Trimmed the abstract from 379 to 293 words by compressing the introductory framing and consolidating result-list sentences.

### Iter 6 — C2: swagger-parser empirical run (closes last Critical item)
- Added `io.swagger.parser.v3:swagger-parser:2.1.22` to `jml-embedder/pom.xml` as a test-scope dep.
- Wrote `SwaggerParserRoundtripTest.java` (2 tests): parses an OpenAPI document carrying every `x-jml-*` extension key, asserts that swagger-parser exposes all keys + value lists + the `signals` nested object structure on the in-memory model.
- Both tests pass. The article now claims empirical preservation against the reference parser (swagger-parser 2.1.x) — RQ5 is no longer "by construction" only.
- Threats, intro, conclusion, RQ5 wording all updated.

### Iter 5 — real-inference run on all 6 libraries (closes Major M1/M2 substantially)
- Added the three new libraries to `CommonsLangRealInferenceTest`.
- Downloaded `-sources.jar` for Math, jOOL, Vavr via `mvnw dependency:get`.
- Ran the harness on all 6 libraries. All achieve 100% lossless roundtrip:

  | Library | specs | overhead | embed m/s | read m/s |
  |---|---|---|---|---|
  | Commons IO | 1,680 | 10.20% | 10,702 | 101,218 |
  | Commons Lang | 2,332 | 10.07% | 7,680 | 78,801 |
  | Commons Math | 6,001 | 10.04% | 7,595 | 111,642 |
  | Guava | 6,320 | 4.63% | 5,951 | 68,281 |
  | jOOL | 2,648 | 5.81% | 13,668 | 126,159 |
  | Vavr | 3,900 | 6.39% | 14,398 | 133,762 |
  | **Total** | **22,881** | — | — | — |

- Updated tab:validation (now 6 + 6 + 1 rows), tab:shapes (aggregate over 22,881 specs), the abstract, introduction, body, threats, and conclusion. Real-inference now uniformly covers all six libraries; the M2 follow-up burden drops from 7 libraries to 4 (jsoup, JFreeChart, JUnit, AssertJ).
- All numeric claims cross-verified (10,332 → 22,881 in 8 places; 1,118 source files → 2,339; 16,507 source methods → 32,459).

## What remains (open)

From `red_team_report.md`:

### Critical (0 of 3 remaining)
All three critical red-team items are now addressed (C1 disclosure in §V, C2 swagger-parser empirical in iter 6, C3 comparative-empirical RQ3 in iter 2).

### Major (1 of 6 remaining)
- **M1** — alt-inferrer roundtrip (Daikon import). Currently 100% lossless is reported only for our inferrer's clause vocabulary. A tiny Daikon-imported spec set would harden the claim.

### Major (now mostly closed by iter 5)
- **M2** — protocol's remaining libraries. Was "7 deferred"; now "4 deferred" (jsoup, JFreeChart, JUnit, AssertJ).

### Minor (1 of 6 remaining)
- **m1** — quantitative comparison vs. a custom class-file attribute prototype. Article currently argues qualitatively (tool visibility, repeatable annotations, forward compatibility). A prototype attribute embedder + measurement would let reviewers compare apples to apples.

## Files

- `article2.tex`, `sections/*.tex` — paper source.
- `article2.pdf` — built artefact (11 pages, 1 page for references).
- `cover_letter.md` — submission cover letter (paste into venue form).
- `red_team_report.md` — reviewer-red-team report (not part of submission).
- `SESSION_NOTES.md` — this file.

## Reverting anonymisation for camera-ready

Author block (`article2.tex` lines 53-58):

```latex
\author{%
\IEEEauthorblockN{Brendan Edmonds, Mark Utting}
\IEEEauthorblockA{%
  UQ Cyber, School of Electrical Engineering and Computer Science\\
  The University of Queensland, St Lucia QLD 4067, Australia\\
  \{b.edmonds, m.utting\}@uq.edu.au}
}
```

Data-availability URL (`article2.tex` data-availability section): replace `https://anonymous.4open.science/r/jml-inferrer-anon` with the public repository / DOI-archived release.

Bib self-citations (`../article1/references.bib`):

```bibtex
@unpublished{edmonds2026inference,
  author = {Brendan Edmonds and Mark Utting},
  ...
}

@unpublished{edmonds2026embedding,
  author = {Brendan Edmonds and Mark Utting},
  ...
}
```

CRediT and Acknowledgments sections in `article2.tex` currently carry placeholders — fill in for camera-ready.

## Build

```bash
cd journal/article2
pdflatex article2 && bibtex article2 && pdflatex article2 && pdflatex article2
```

Produces `article2.pdf` at 11 pages, 0 LaTeX warnings, 0 BibTeX warnings.
