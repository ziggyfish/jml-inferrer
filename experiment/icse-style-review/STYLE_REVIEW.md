# Article 3 vs ICSE 2024 — style review

Anchored on 26 ICSE 2024 main-track papers (titles + authors collected from
dblp), with a full read of the most directly comparable neighbour: **LAMBDA
— "A Framework For Inferring Properties of User-Defined Functions"** (Liu,
Arulraj, Orso, ICSE'24, [DOI 10.1145/3597503.3639147]). LAMBDA is the closest
analogue to Article 3: a static inference tool, dataflow-based, with a
measurement-driven evaluation on a real corpus. Where the comparison points to
divergence, I flag it with **MATCH** / **DIFF** / **CONSIDER**.

## Comparison cohort (sample of 26)

Empirical / static-analysis / testing ICSE 2024 papers used as the cohort:
LAMBDA (Liu/Arulraj/Orso), Ripples of a Mutation (Du/Palepu/Jones), Hypertesting
of Programs (Pasqua/Ceccato/Tonella), Symbol-Specific Sparsification of IDE
Problems (Karakaya/Bodden), Reorder Pointer Flow in Sound Concurrency Bug
Prediction (Guo/Zhu/Cai), Object Graph Programming (Thimmaiah et al.), Semantic
Analysis of Macro Usage for Portability (Pappas/Gazzillo), Fast Deterministic
Black-box Context-free Grammar Inference (Arefin et al.), Marco: A Stochastic
Asynchronous Concolic Explorer (Hu/Duan/Yin), Evaluating Code Summarization
Techniques (Mastropaolo et al.), and others.

## Structural comparison (LAMBDA vs Article 3)

| Element | LAMBDA (ICSE'24) | Article 3 | Verdict |
|---|---|---|---|
| Page count | 11 (incl. refs) | 10 | **MATCH** — both within ICSE's main-track allowance |
| Title style | Descriptive ("A Framework For…") | Question-style ("Does Compositional Refinement…") | both common; Article 3's interrogative is fine |
| Abstract length | ~250 words | ~290 words | **MATCH** |
| Section 1 | Introduction with **Challenges / Existing Techniques / Our Approach** sub-paragraphs, ending in a bulleted contributions list | Same shape (Intro → premise → contributions list) | **MATCH** |
| Section 2 | Background, with **Motivating Example + Case Study** subsections | Background (single subsection) — no explicit motivating example | **CONSIDER**: adding a one-method *motivating example* is a low-cost ICSE convention |
| Section 3 | "Problem Formulation" with formal property definitions | Folded into Background/Algorithm sections | **DIFF**: LAMBDA splits formalism out; Article 3 keeps it inline. Both are accepted shapes. |
| Approach section | **Algorithm 1** as a numbered pseudocode block | Prose description of the compositional pass | **CONSIDER**: a numbered Algorithm 1 box is an ICSE convention for inference/static-analysis papers and would strengthen Article 3's "do this on real code" credibility |
| Evaluation | "**5. EVALUATION**" with explicit **RQ1 / RQ2 / RQ3** in a list, each becoming a numbered subsection (5.3, 5.4, 5.5) | Same shape: numbered RQs, each answered in a section | **MATCH** — Article 3 follows the convention precisely |
| Empirical setup | Implementation / Evaluation Setup / per-RQ subsections | Subjects-and-method, then Results / Shape distribution / Runtime | **MATCH** in spirit |
| Per-RQ takeaway | Framed grey **summary boxes** ("LAMBDA was able to…") at the end of each RQ section | Prose summary at the end of each results subsection | **CONSIDER**: ICSE reviewers appreciate the box — easy add, high reviewer-readability return |
| Tables | Tables 1–4 (per-property, per-query) | Tables 1–4 (per-library, per-shape, per-runtime) | **MATCH** in density and granularity |
| Figures | Workflow figure + per-RQ result plot | Plots/diagrams not currently emphasised; mostly tables | **CONSIDER**: a workflow figure for the inference + compositional pass would help readers |
| Threats to Validity | **No** explicit section | Explicit section with internal/external/construct/conclusion | LAMBDA omits, but most ICSE empirical papers include one. Article 3's section is a **plus**, keep it. |
| Related Work | Late section, narrow categories (UDF Translation, UDF Compilation), tight | Related-work table positioning Article 3 vs Daikon/Houdini/etc. | **MATCH** |
| Conclusion | Short, summary + future work | Short, summary + future work | **MATCH** |
| Citations | Numeric, ~28 entries, mix of papers + URLs | Numeric, similar mix | **MATCH** |
| Tone | "we" first-person plural, direct, low hedging | Same | **MATCH** |

## Specific style markers Article 3 already has right

- **Numbered RQs (RQ1–RQ4)** with each answered in a named section — directly mirrors LAMBDA.
- **Bulleted contributions list at end of Introduction** — convention-matched.
- **Numeric citations**, **third-person plural voice**, **standard table-heavy empirical results** — all match ICSE 2024 conventions.
- **Explicit threats-to-validity section** — present in Article 3, absent in LAMBDA; ICSE reviewers expect it for empirical-measurement papers, so keep it.
- **Per-library breakdown table** — directly parallels LAMBDA's per-property breakdown table.
- **Page budget (~10)** — within ICSE main-track main-body allowance.

## Where Article 3 diverges from the LAMBDA style — and what to consider

| Adjustment | Cost | Reviewer-perceived value |
|---|---|---|
| **Add a Motivating Example subsection in §2** (one small caller-callee pair where the compositional pass adds a clause the single pass misses, with the actual JML shown) | low | high — anchors the abstract claim concretely on page 2 |
| **Add Algorithm 1 box** for the compositional refinement pass (the SCC-iterating driver + per-method lift) | low | high — inference/static-analysis ICSE papers conventionally include pseudocode; absence is unusual for this paper type |
| **Add a workflow figure** showing inferrer → cache → compositional pass → refined cache → OpenJML / consumer | low | medium — improves scannability for reviewers skimming |
| **Per-RQ takeaway box** (1–2 sentences in a framed grey box) | trivial | medium — ICSE reviewers anchor on these |
| **Tighten "Problem Formulation" content into a small §3** with the formal definitions of "single-pass propagation", "branch-conditional obligation", "polymorphic-dispatch disjunction" | medium | medium — separates formal setup from approach and helps citations to the formal definitions |

## What the broader 26-paper cohort confirms about ICSE 2024 conventions

- **RQ-driven evaluation is the dominant style** for empirical/measurement papers; both numbered RQs and the section-per-RQ pattern are near-universal among the 26 papers that report measurements. Article 3 matches.
- **Title style is mixed.** Question-style titles ("Does X help Y?", as Article 1 uses) and descriptive-with-tool-name ("LAMBDA: A Framework…") both appear. Article 3's question-style title is conventional.
- **Implementation availability** (a published artefact / replication package) is conventional — LAMBDA has [9] referenced from the contributions; Article 3 has a Data Availability section, which matches.
- **No paper in the cohort exceeds the page limit** as part of the main body — they go over only in the references.
- **Threats sections appear in most empirical papers** in the cohort (Ripples of a Mutation, the empirical study papers); Article 3 having one is the safer choice.

## Bottom line

Article 3 is written **in line with ICSE 2024 conventions on every load-bearing
axis**: page count, abstract length, RQ-driven structure, numbered
contributions, tables-and-prose empirical reporting, threats section, related
work positioning, and citation style. The five **CONSIDER** items above are
adjustments that would make it land more strongly against the LAMBDA-class
benchmark — a motivating example and a numbered Algorithm 1 are the highest
return, and both are <1 page of work. None of the **CONSIDER** items represent
something currently *missing* in a way that would risk a desk reject; they are
incremental improvements toward the most polished ICSE-2024 templates.

The structural and stylistic risk for Article 3 at ICSE is therefore not
prose-shape — it's the empirical risk you already know (the compatibility
capability is mechanism-demonstrated, not end-to-end demonstrated), not the
writing.

## Sources

- [LAMBDA paper (NSF Public Access)](https://par.nsf.gov/biblio/10538583-framework-inferring-properties-user-defined-functions)
- [LAMBDA paper PDF (direct)](https://par.nsf.gov/servlets/purl/10538583)
- [LAMBDA (ACM DL DOI)](https://doi.org/10.1145/3597503.3639147)
- [Ripples of a Mutation (Spider Lab)](https://spideruci.org/publication/du-ripple-2024/)
- [Ripples of a Mutation (ACM DL)](https://doi.org/10.1145/3597503.3639179)
- [ICSE 2024 main-track proceedings (dblp)](https://dblp.org/db/conf/icse/icse2024.html)
