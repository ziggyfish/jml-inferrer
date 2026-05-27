# Article 2: Embedding Inferred JML Contracts in Java Bytecode and OpenAPI Specifications

**Status:** drafted, currently being prepared for the SANER research track. Anonymised for double-anonymous review.

## Premise

Automatically inferred JML specifications materially improve downstream tooling — test generators, IDEs, verifiers, LLMs reading APIs at inference time — but only when the consumer has the source tree. Compiled Java libraries and remote REST services do not carry that channel. This paper proposes and evaluates a uniform mechanism for distributing inferred JML contracts to consumers of compiled Java artefacts and OpenAPI service descriptions.

## Contributions

1. **`@JmlSpecs` annotation type** — runtime-retained, repeatable per clause, written into class-file `RuntimeVisibleAnnotations` by an ASM-based embedder.
2. **OpenAPI 3.x extension family** (`x-jml-requires`, `x-jml-ensures`, `x-jml-assignable`, `x-jml-signals`, `x-jml-invariant`) preserved by standard parsers without modification.
3. **Maven classifier sidecar** for cases where in-bytecode embedding is unsuitable (signed JARs; over-budget specs).
4. **Empirical evaluation** across 20,546 methods of three real-world libraries (Apache Commons Lang, Apache Commons IO, Guava) plus a 10,332-spec real-inference corpus.
5. **Format-optimisation step** (single packed annotation per method; default-omission for `assignable \nothing`; twelve-token dictionary) — measured against a more verbose v1 baseline.
6. **Negative test** confirming consumer tolerance (classes load in JVMs that lack the annotation type).

## Headline Results

- 100.0% lossless roundtrip on every measurement run (synthetic and real-inference).
- Bytecode-size overhead: 5.27–6.97% under synthetic specs, 4.63–10.20% under real inferred specs.
- Embedding throughput 6,000–22,000 methods/second; reading 74,000–328,000 methods/second.
- Format-optimisation reduction: 48–55% on synthetic, 31% on real-inference.

## Files

- `article2.tex` — main IEEEtran conference document.
- `sections/` — body sections (introduction, background, format_design, implementation, empirical_validation, discussion, threats, related_work, conclusion).
- `cover_letter.md` — submission cover letter (kept outside the PDF; paste content into the venue's submission form).
- `red_team_report.md` — internal reviewer-red-team report (Pass 6 of the quality gates); not part of the submission package.
- `article2.pdf` — built artefact.

## Relationship to Article 1

Article 1 (`../article1/`) reports on what specifications do for LLM-generated tests. Article 2 makes those specifications transportable to consumers without source. The two papers are non-overlapping: Article 1's claim is about test quality given specifications; Article 2's claim is about the mechanism by which specifications travel to a consumer that lacks source. Article 2 should cite Article 1 once it is publicly available; if Article 1 is still under review at submission time the citation is to the preprint or working manuscript.

## Build

```
pdflatex article2 && bibtex article2 && pdflatex article2 && pdflatex article2
```

Produces `article2.pdf` (10 pages at SANER's IEEEtran conference format).
