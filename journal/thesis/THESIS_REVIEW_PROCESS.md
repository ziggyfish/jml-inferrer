# Thesis Review Process (Traditional Monograph)

A staged review process for the PhD thesis *Configuring Formal Methods for
Industry: Inferring, Distributing, and Propagating JML Specifications*
(`journal/thesis/`), structured as a **traditional monograph**: a single
continuous narrative with one unified literature review, one methods framing,
and results organised thematically around the thesis's argument rather than by
the papers the work was published in.

This process exists because a 60,000-word monograph has failure modes that the
per-article quality gates (see the project `CLAUDE.md`) do not catch: drift in
the overarching argument across chapters, inconsistency between the abstract /
introduction / conclusion, **duplicated background or methods that should have
been stated once and referenced**, and claims that overreach the evidence.

> **Monograph vs by-publication.** In a monograph, the chapters are *not*
> standalone papers and repetition is a **defect to eliminate**, not an
> accepted cost. A chapter that carries its own self-contained introduction,
> related-work survey, or conclusion is a sign the material has not been fully
> integrated into the single narrative. The review treats the thesis as one
> argument told once, end to end.

## How to use this document

Run the passes **in order** — earlier passes establish facts (e.g. the build
is clean, the numbers are consistent) that later passes depend on. Each pass
states: **(a)** what is checked, **(b)** how to check it, **(c)** what to
report. End every full review with the one-line summary:

`[thesis passes 1–10: N issues found, M fixed, K flagged for author decision]`

A **full review** runs all ten passes and is warranted before any milestone
submission (confirmation, mid-candidature, final submission to examiners). A
**light review** (passes 1, 2, 4, 6) is sufficient after a localised edit to a
single chapter. Always state at the top which review was run.

Distinguish three dispositions for every issue:
- **Fixed** — corrected automatically; safe, unambiguous (typo, broken ref,
  inconsistent number with a known-correct source).
- **Flagged** — surfaced for author decision; involves judgement, scope, or a
  claim only the author can adjudicate.
- **Vouched** — checked and found correct; report only when a pass would
  otherwise look skipped.

---

## Pass 1 — Build integrity

**Checks the thesis compiles to a correct artefact.**

- Run the full LaTeX cycle from `journal/thesis/`:
  `pdflatex → bibtex → pdflatex → pdflatex` on `thesis.tex`.
- Confirm: zero LaTeX errors; **zero undefined references, citations, or
  labels**; zero multiply-defined labels; every `\input{}` file resolves.
- Confirm the table of contents, list of figures, and list of tables are
  populated and page numbers resolve (run the extra `pdflatex` if "Rerun to
  get cross-references right" appears).
- Report: final **page count**, and whether any LaTeX *warnings* remain
  (not just errors).

**Report:** page count; warning count; any unresolved ref/label/citation.

---

## Pass 2 — Argument coherence (the spine)

**The single most important pass in a monograph, because the monograph *is* one
argument and a broken spine has nowhere to hide.** The spine is the adoption
question — *why are formal methods niche, and can inferred + propagating
library-boundary specifications change that* — and the compatibility mechanism
(callee-spec change ⇒ caller-spec change).

- The **thesis statement** (Ch 1) names exactly what the body delivers — no
  more (no overclaim), no less (no undelivered promise) — and the conclusion
  closes on the same statement.
- The **four research questions** as stated in Ch 1 are each (a) answered in a
  named chapter, (b) revisited in the conclusion, and (c) phrased consistently
  in all three places. RQ numbering matches the chapter "answers RQ\emph{n}"
  references.
- The **argument advances chapter to chapter** with no gap and no backtrack:
  each chapter's opening states how it follows from the previous and what it
  sets up for the next; each closing hands off explicitly. A reader should be
  able to state, after any chapter, what remains to be shown.
- The **adoption framing** is present and consistent in: abstract, Ch 1 intro,
  Ch 7 synthesis, Ch 8 conclusion. No residue of any superseded framing.
- The **compatibility claim** is framed identically everywhere as *mechanism
  demonstrated, end-to-end version-diff experiment deferred to future work* —
  no sentence anywhere implies the version-comparison experiment was run.
- Every `\ref{ch:...}` / `\ref{sec:...}` points where the surrounding prose
  says it does; the introduction's promised chapter order matches the actual
  order.

**Report:** any claim that overreaches the evidence; any RQ phrased
inconsistently across intro/chapter/conclusion; any place the compatibility
experiment is implied to have been run; any chapter whose opening/closing does
not connect to its neighbours; any narrative gap or backtrack.

---

## Pass 3 — Numeric consistency

**Every headline number is identical wherever it appears.** The monograph
repeats its key figures across abstract, chapter bodies, synthesis, and
conclusion; these must agree to the digit.

Cross-check, across all files, that these match exactly:
- Inference accuracy: precondition precision (94.2%), postcondition precision
  (87.6%), clause discharge rate (92.9%), corpus coverage (99.0%), 312 methods.
- Test generation: +272% test count, +40.7 pp mutation score, P1–P4 condition
  numbers, mutation-score means per phase.
- Distribution: 100% lossless roundtrip, overhead range (<11% / 4.63–10.20%),
  throughput ranges, 20,546-method and 10,332-spec corpus figures.
- Compositional: 42,370 new precondition clauses, 25,203 postcondition clauses,
  21,052 methods, 5 libraries, per-library refined-% (24.33–43.85%), per-library
  shape percentages, 44 s total runtime.

Method: grep each number; confirm one canonical value; flag any divergence to
the source table in the chapter that owns the result.

**Report:** every number that appears with two different values; the
authoritative value and where it lives.

---

## Pass 4 — Register and prose audit

**One voice, one spelling system, no chapter that reads like a standalone
paper.**

- **British English throughout** (analyse, behaviour, optimise, recognise,
  artefact) — `\color` and other LaTeX macros are exempt.
- Tense consistency within sections: past for completed work, present for the
  thesis's standing claims.
- Every acronym (JML, WP, SP, SMT, ESC, AST, LLM, OpenAPI, ASM, CHA, RTA)
  defined **once**, on first use in the thesis, then used without redefinition.
- Consistent terminology: "the engine" / "JML-Inferrer" / "the system" used
  deliberately, not interchangeably mid-argument; "specification" vs "contract"
  used consistently.
- No marketing register ("seamless", "powerful", "leverage", "robust",
  "cutting-edge", "simply", "very").
- No double spaces; no LaTeX straight-quote artefacts (`"..."` instead of
  ``` ``...'' ```); em-dash usage consistent.
- **Chapter voice:** every chapter reads as part of a continuous monograph, not
  as a paper. Flag any chapter-internal "In this paper / this article", any
  chapter abstract, any self-contained per-chapter related-work or conclusion
  section that duplicates the thesis-level ones.

**Report:** spelling-system violations; redefined or undefined acronyms;
terminology drift; register lapses; any standalone-paper phrasing or structure.

---

## Pass 5 — Empirical defensibility

**Report missing items only; do not vouch for whether the experiments were
sound — that is outside scope.**

- Every statistical claim carries effect size, confidence interval, p-value,
  and (where multiple comparisons) the correction.
- Variance / standard deviation reported alongside means.
- Sample sizes stated and, where a power claim is made, justified.
- Baselines and conditions (P1–P4, synthetic vs real specs, single-pass vs
  compositional) described well enough to reproduce.
- Model version, temperature, run count, and prompt provenance disclosed or
  pointed to in a replication package.
- The **single methods chapter / section** is complete enough that every
  empirical chapter draws its protocol from it without re-specifying it; if an
  empirical chapter introduces a method detail, that detail belongs in (or is
  cross-referenced to) the unified methods framing, not duplicated.
- Threats to validity are handled in one consolidated treatment that covers
  corpus homogeneity, single model family, residual unverified clauses, and the
  status of the compatibility claim — not scattered piecemeal.
- Categorisation / shape-bucketing criteria are operational and reproducible.

**Report:** missing statistical components; under-described baselines;
undisclosed parameters; method detail duplicated outside the methods framing.

---

## Pass 6 — Bibliographic integrity

- Every `\cite{}` resolves to a `references.bib` entry (the thesis shares
  `../article1/references.bib`).
- Every entry cited at least once from the thesis (orphan check is advisory —
  the .bib is shared with the source articles).
- Author lists complete; flag any `and others` on a paper-of-record entry.
- For entries added or modified since the last Pass 6: title, year, venue
  verified against the actual publication; DOIs resolve.
- No citations to predatory venues or retracted papers.
- Citation style consistent (thesis uses `plain`; confirm it renders
  consistently throughout).
- **One literature is surveyed once.** In a monograph the related work is a
  single unified chapter/section; confirm no empirical chapter re-surveys a
  body of work already covered there — it should cite back to the survey
  instead.

**Report:** unresolved keys; incomplete author lists on key references;
metadata errors found on verification; related-work re-surveyed outside the
unified literature chapter.

---

## Pass 7 — Monograph structural integrity

**Replaces the by-publication integrity pass. Checks that the material has been
genuinely integrated into one continuous work rather than stitched from three
papers.**

- **Single literature review.** Background and related work live in one place
  (Ch 2). No empirical chapter carries its own related-work section; where a
  chapter needs to position a specific result, it cites back to Ch 2 rather
  than re-reviewing.
- **Single methods framing.** Shared experimental machinery (corpora, the
  inference engine, the validation pipeline, the statistical approach) is
  established once and referenced thereafter, not re-explained per chapter.
- **Thematic, not paper-shaped, chapters.** Chapters are organised by the
  argument's stages (inference and accuracy; downstream value; library-boundary
  distribution; compositional propagation and compatibility), not by "Paper 1 /
  Paper 2 / Paper 3". No chapter is recognisably "Article *n* lightly edited".
- **Repetition audit (strict).** Any passage that restates background, method,
  or motivation already given earlier is a defect: flag it for consolidation.
  Forward/backward cross-references replace repetition. (This is the opposite
  of the by-publication tolerance for redundancy.)
- **No stranded framings.** Where the monograph reframes material from a source
  paper (notably the compatibility framing of the compositional chapter), the
  reframing is complete — no sentence retains the source paper's original
  framing mid-chapter.
- **Continuous pagination and numbering.** Figures, tables, and sections are
  numbered continuously in thesis order, not restarted per incorporated paper.

**Report:** duplicated background/methods/motivation; any per-chapter
related-work or methods section; any chapter that reads as a lightly-edited
paper; stranded source-paper framings.

---

## Pass 8 — Front and back matter, and university formatting

- Abstract present, self-contained, and within the university word limit
  (UQ: typically ≤ ~500 words for the thesis abstract — confirm against current
  HDR guidelines).
- Declaration by Author present with all required UQ sub-statements.
- **Publications during candidature** listed in the appropriate front-matter
  section. In a traditional monograph these are listed as *publications arising
  from the thesis*, **not** as the chapters themselves; confirm the front matter
  does not describe the thesis as a thesis-by-publication. Co-author
  contribution statements present where any included material is co-authored.
- Acknowledgements present; ORCID / affiliation as required.
- Table of contents, list of figures, list of tables present and correct.
- Every figure and table has a caption that is self-contained (readable without
  the surrounding text) and is referenced from the body before it appears.
- Page margins, line spacing, and front-matter ordering conform to current UQ
  HDR thesis formatting requirements (verify against the live UQ guidelines —
  these change).
- Data-availability / replication-package statement present and its URL
  resolves (or is flagged as a placeholder to fill before submission).

**Report:** missing required front-matter components; abstract over length;
any front matter that mis-describes the thesis as by-publication; orphan or
forward-referenced figures/tables; formatting items to verify against live UQ
guidelines.

---

## Pass 9 — Examiner red-team

**Read the thesis as an adversarial examiner. Produces text only — do not edit
the thesis in response unless explicitly asked.**

Produce a list of likely examiner objections, ordered Critical / Major / Minor.
For each: the objection in one sentence; where in the thesis it lands; what the
defence would need to say; and whether it needs new work or can be met by
editing alone. Pay particular attention to the thesis's known soft spots:

- **The compatibility capability is argued, not demonstrated end-to-end.** An
  examiner will press: "you claim library-boundary specs enable compatibility
  analysis but never ran a version-diff — is the mechanism evidence enough?"
- **Corpus homogeneity** — all evaluation is open-source library code; does the
  adoption argument hold for application/framework/proprietary code?
- **Single model family** for the LLM studies — are the magnitudes
  model-specific?
- **Heuristic soundness** — the residual unverified clauses; what is actually
  guaranteed?
- **The adoption thesis is partly an economic/sociological claim** — is it
  over-reached on the evidence of technical measurements alone?
- **Monograph-specific:** does the single narrative genuinely require all three
  studies, or could an examiner argue one chapter is detachable? The synthesis
  must make each study load-bearing for the argument.

Also produce a short list of **anticipated viva questions** with one-line
defensible answers.

**Report:** the ranked objection list; the viva-question list. No edits.

---

## Pass 10 — Final submission readiness

**Run only immediately before a milestone submission.**

- Passes 1–8 re-run clean (Pass 9 is advisory, Pass 10 gates).
- Anonymisation correct if the submission is examined blind (replication URLs,
  acknowledgements, self-citations that reveal identity).
- All `[anonymized]` / placeholder URLs and TODO markers resolved or
  consciously left with a tracked note.
- PDF opens, is navigable (bookmarks/outline present from `hyperref`), and the
  page count matches Pass 1.
- A clean build from a fresh checkout reproduces the same PDF (no reliance on
  stale `.aux` / `.bbl`).
- Word count recorded against the target.

**Report:** anonymisation status; unresolved placeholders; clean-build
reproducibility; final page and word count.

---

## Disposition log template

Append a dated entry per review run:

```
### YYYY-MM-DD — {full | light} review (traditional monograph)
- Pass 1: <result>
- Pass 2: <result>
- ...
[thesis passes 1–10: N found, M fixed, K flagged]
Flagged for author: <bulleted list of decisions only the author can make>
```
