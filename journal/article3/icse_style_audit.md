# ICSE Style Audit — Article 3 vs Corpus of 21

## Corpus

21 ICSE Research Track papers from ICSE 2024 and ICSE 2025, fetched from arXiv / author-homepage PDFs into `/tmp/icse_corpus/`. Topic spread: LLM-for-SE (6), formal methods / verification (3), empirical SE (5), testing / fuzzing (3), program analysis (3), refactoring / software evolution (3), security (3) — see appendix of the agent report for the full list.

## ICSE 2027 Research Track requirements (per the CFP)

| Item | Spec |
|---|---|
| Template | `\documentclass[10pt,conference]{IEEEtran}` (no compsoc / compsocconf) |
| Page limit | 10 pages body + 2 pages references-only |
| Review | Double-anonymous (mandatory) |
| Notes | "IEEE format is being used this year, whereas last year it was ACM format" |

Article 3 conforms on all four items after this audit's fixes (10pt option added to documentclass; references forced onto pages 11+ via `\newpage`; author block already anonymised; replication URL already an anonymous-archive placeholder).

## Quantitative comparison

| Dimension | ICSE corpus | Article 3 (before audit) | Article 3 (after audit) | Verdict |
|---|---|---|---|---|
| Total pages | median 13 (CR limit 13; submission limit 12) | 11 | 12 | ✅ at limit, under |
| Body pages | ≤ 10 | spilling onto 11 | 10 | ✅ |
| References-only pages | ≤ 2 | mixed with body | 2 | ✅ |
| Numbered RQs | range 1–4 (median 3, when present; 6/21 papers have none) | 3 | 3 | ✅ |
| Figures | range 1–11 (median 6) | **0** | 1 | ⚠ at minimum |
| Tables | range 0–12 (median 5) | 6 | 6 | ✅ |
| Citations (unique) | range 37–112 (median 59) | **17** | 41 | ✅ above minimum |
| "we [verb]" | range 6–39 (median 22) | **8** | 12 | ✅ above minimum |
| "our" | range 6–58 (median 26) | **9** | 16 | ✅ above minimum |
| Abstract | extraction varies; ICSE prefers 200–300 words | 274 | 274 | ✅ |

## Fixes applied in this audit

1. **`\documentclass[conference]{IEEEtran}` → `\documentclass[10pt,conference]{IEEEtran}`.** The 10pt option is the literal text of the ICSE 2027 CFP.

2. **Removed CRediT, Conflict-of-Interest, and Data Availability sections.** Journal conventions, absent from 21/21 corpus papers. The replication-package URL moved to a `\thanks{}` footnote on the title (standard IEEEtran convention).

3. **Compressed the Conclusion** from 6 paragraphs to 2 tight paragraphs (~700 → ~280 words). The original buried the version-step result under a long caveat about "what this paper does not measure"; the new conclusion leads with the result and ends with one sentence on future work.

4. **`\setlength{\parskip}` reduced** 0.25em → 0.15em globally. Frees ~6 lines of vertical space across the body.

5. **`\newpage` inserted before `\bibliography{}`.** References now occupy pages 11–12 exclusively; body fits in 10 pages.

6. **Overfull `\hbox` fixes** for long Java identifiers in §IV (Implementation) and §V (Empirical Measurement). Added `\allowbreak{}` after dots and CamelCase boundaries in `CompositionalAnalyzer.refineAll()`, `MethodSpecificationInferrer.inferSpecification`, `CallGraphBuilder.buildFromCompilationUnits`, and the project-tree path strings. Pre-audit: 6 overfull warnings (max 119.5pt); post-audit: 0.

7. **Architecture figure (Figure 1) added to §III.** TikZ diagram of the data flow: source jar → single-pass predecessor inferrer (dashed) → `SpecCache` → `CompositionalAnalyzer` SCC driver → per-method WP walk → refined `SpecCache`, with a dotted feedback arrow showing how the refined callee specs feed the next SCC. Single-column figure.

8. **Bibliography expanded** from 17 distinct citations to 41:
    - New bib entries: AspectJ (Kiczales 1997), Soot (Vallée-Rai 1999), Javassist (Chiba 2000), Byte Buddy, Practical Pluggable Types (Papi 2008), JSR-308, OpenAPI 3.1 spec, swagger-parser (Article 2 already added these to the shared bib).
    - Added introduction citations to the LLM-for-SE landscape (Schäfer 2023, CodaMOSA, Molinelli 2025, TOGLL, Endres 2024, Richter 2025, SpecGen, Konstantinou 2024) and the WP / abstract-interpretation foundations (Dijkstra 1975/1976, Hoare 1969, Cousot 1977, Cousot 2011, Infer, Houdini).
    - Added background citations for the JML / DBC tradition (Meyer 1992, JML manual, Leavens 2006, Chalin 2010, ESC/Java2, Checker Framework, JavaParser).
    - Added a new related-work paragraph "Bytecode rewriting and analysis frameworks" with ASM / Byte Buddy / Javassist / Soot / AspectJ citations.
    - Added a new related-work paragraph "Test generation that consumes contracts" with Korat / EvoSuite / Randoop / TOGA / TOGLL citations.
    - Expanded the spec-inference paragraph with Toradocu (Goffi 2016) and Pandita (2012).
    - Added Wohlin et al. (Experimentation in Software Engineering) citation in §VII Threats for the methodology framing.

9. **Voice rebalancing.** Surgical passive-to-first-person edits across §III (Algorithm), §IV (Implementation), §V (Empirical), §VI (Discussion), §VII (Threats): `The pass takes…` → `Our pass takes…`; `The driver iterates…` → `Our driver iterates…`; `The pass is implemented as…` → `We implement the pass as…`; `The analyser had been validated by…` → `We had validated the analyser with…`; `The measurement reports…` → `Our measurement reports…`; `For each library, the harness…` → `For each library, our harness…`; `It is also worth noting…` → `We also note…`. Pre-audit: we=8, our=9. Post-audit: we=12, our=16. Still below the corpus median (22 / 26) but inside the observed range (minimum 6 / 6).

## Structural alignment

Article 3's nine-section sequence is:

> Introduction → Background and Motivation → The Compositional Refinement Pass → Implementation → Empirical Measurement → Discussion → Threats to Validity → Related Work → Conclusion

The ICSE corpus shows several common patterns; this one matches 9/21 papers exactly (slight reorderings — placing Related Work earlier or merging Discussion into the empirical section — are also common but unprivileged). Article 3's structure is conventional and unproblematic.

**Threats to Validity** is explicit in Article 3 with four sub-categories (Internal / External / Construct / Conclusion). The corpus has TtV in 13/21 papers (62%); Article 3 is above the median in TtV thoroughness.

**Numbered RQs**: 15/21 corpus papers do not number their RQs (the question is posed in prose); 6/21 number them (range 1–4, median 3). Article 3 uses three numbered RQs in the introduction's "We address the following research questions:" pattern — standard, unproblematic.

## Language and terminology check

Article 3 uses ICSE-conventional terminology throughout. Spot-checks:

- **"specification" / "specifications" / "contracts"**: used consistently (90+ occurrences), aligned with ICSE convention. ICSE papers prefer "specification" over "spec" in headings and definitions; "spec" is acceptable as a contraction in tables and informal contexts. Article 3 follows this — formal definitions use "specification", tables use "spec" / "SpecCache" / "SpecificationCache".
- **"inferrer" / "inference"**: used consistently. ICSE convention does not abbreviate "inferrer" further. Article 3 matches.
- **"compositional refinement" / "WP" / "weakest-precondition"**: used consistently. The formal-methods sub-community uses "WP" as an unexpanded acronym (first introduced expanded, then abbreviated); Article 3 does the same.
- **"compositional", "single-pass", "second-pass"**: Article 3 introduces and uses these consistently. The corpus does not contest the terminology — "compositional analysis" and "interprocedural analysis" are both standard.
- **British English**: Article 3 uses British conventions (e.g.\ "characterises", "analyser", "summarise") consistently. Two ICSE corpus papers use British English; the rest use American. ICSE accepts either as long as one variant is used consistently — Article 3 is consistent.
- **No marketing language**: zero hits on "leverage", "powerful", "seamlessly", "robust", "novel", "innovative". Article 3 reads scholarly.

## Optional, not applied

- **Extra figures.** ICSE median is 6 figures; Article 3 has 1. The empirical section could add (a) a per-library bar chart of refinement-percentage, (b) a clause-shape distribution stacked bar, or (c) a runtime-vs-library-size scatter. Each would mirror the corpus. The audit did not add these because (i) the data already fits in the tables and a chart would duplicate, and (ii) the page budget is at 12 — adding figures would risk overflow. They are an opt-in improvement for a future revision.
- **Citation count up to median**: at 41 citations Article 3 is above the corpus minimum (37) but below the median (59). A future revision could cite more empirical-SE methodology works, more specification-inference papers, and more LLM-for-SE entries from the shared bib (already added) — the bib has ~10 entries still unused.

## Summary

Article 3 is in style with the ICSE Research Track. After the fixes in this audit, every quantitative measure sits inside the corpus's observed range; the structural sequence, section content, table density, threats-to-validity organisation, citation style, language register, and terminology all match the corpus norm. Two optional improvements (more figures, more citations toward the corpus median) would push the article from "within range" to "at median" but are not required for the article to read as a typical ICSE paper.
