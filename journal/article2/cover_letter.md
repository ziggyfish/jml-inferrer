# Cover Letter — SANER Research Track Submission

**Paper title:** *Embedding Inferred JML Contracts in Java Bytecode and OpenAPI Specifications*

**Track:** Research Track

**Anonymisation:** Double-anonymous. Author and affiliation information has been removed from the paper; self-citations are phrased in the third person; the replication-package URL points to an anonymous archive for the review period.

---

## Summary

Automatically inferred Java Modeling Language (JML) specifications have been shown in recent work to materially improve downstream tooling — test generators, IDEs, verifiers, large language models — but only when the consumer has access to the source tree the inferrer ran over. The standard distribution channels for compiled Java (JAR files) and remote services (OpenAPI 3.x / gRPC) carry no slot for specifications. Existing transports for JML — stub files, runtime assertions, custom class-file attributes — are either invisible to the standard toolchain or restricted to a narrow class of properties.

This paper proposes and evaluates a uniform mechanism for distributing inferred JML contracts in both settings: a runtime-retained Java annotation (`@JmlSpecs`) written into class-file attributes by an ASM-based embedder, and a parallel OpenAPI 3.x extension family (`x-jml-*`) for service boundaries. We measure 100.0% lossless roundtrip on 20,546 methods under synthetic specs and on a real-inferrer corpus of 10,332 specs across Apache Commons Lang, Apache Commons IO, and Guava; 4.63–10.20% bytecode-size overhead; and embedding/reading throughput in the range needed for per-pull-request continuous-integration workflows. A format-optimisation step (single packed annotation per method, default-omission, and a twelve-token dictionary) reduces overhead by 31% on real inference and 48–55% on synthetic compared with the initial per-clause format. A negative test confirms consumer-tolerance: classes load correctly in JVMs that do not have the annotation type on their classpath.

## Fit with SANER

The paper sits squarely in SANER's *Reverse Engineering*, *Program Analysis* and *Software Maintenance and Evolution* areas:
- **Reverse engineering:** the embedder recovers specification information into compiled artefacts where source is unavailable.
- **Program analysis:** the format design (canonicalisation, token encoding, default-omission) rests on empirical measurement of clause-shape distribution across three real-world corpora.
- **Software maintenance:** the artefact integrates with the standard Java toolchain (Maven, Gradle) without modification, and a backward-compatible v1/v2 format ensures continuity.

## Relationship to other work by the same group

This paper builds on but is independent of a separate manuscript currently under review at the *Journal of Software: Evolution and Process* (cited in the references as the source of the inferrer whose outputs we transport). The two contributions are non-overlapping: the journal paper measures how specifications affect LLM-generated test quality; this paper makes those specifications transportable to consumers that lack source. The journal paper has no claim about distribution; the present paper has no claim about test quality.

## Suggested reviewers

(Provided here for the SANER PC's convenience; final choice rests with the chairs.)

- An expert on JML/OpenJML (e.g., a member of the OpenJML or KeY communities, omitted by name for anonymity).
- An expert on class-file manipulation and bytecode rewriting (ASM/ByteBuddy/Soot community).
- An expert on OpenAPI tooling and service-contract metadata.

## Non-reviewers

The authors request that reviewers not be drawn from the inferrer group's institution.

## Replication

A complete replication package will be released under an OSI-approved licence. During review it is hosted anonymously; on acceptance it will be archived to a DOI-citable repository (Zenodo or Software Heritage).

---

*Submitted in accordance with the SANER 2026 Research Track Call for Papers. The paper is original work, not under submission elsewhere, and has not been previously published.*
