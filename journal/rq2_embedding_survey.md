# RQ2 Phase 2A.1 — Survey of Specification Embedding Mechanisms

**Drafted:** 2026-05-06 (autonomous probe-sweep week, day 1)
**Status:** working draft — to be reviewed before Phase 2A kickoff (June 2026)
**Source plan:** `journal/rq2_rq4_execution_plan.md` §2A.1

---

## 1. Scope

RQ2 asks whether formal specifications can be represented and distributed in compiled or interface-only environments where source is unavailable. This survey enumerates the candidate mechanisms identified in the execution plan, plus three additional carriers that surfaced during this review (ProGuard/R8 metadata streams, JEP 181 nest-mates context attributes, and JAR manifest entries). For each, the table reports six dimensions:

| Dimension | What it measures |
|---|---|
| **Expressiveness** | Whether the carrier preserves arbitrary JML clauses (including `\sum`, `\forall`, `\old`, nested quantifiers) without lossy encoding |
| **Tooling support** | Whether mainstream IDEs, build tools, and reflection APIs surface the carrier without bespoke adapters |
| **Byte overhead** | Estimated bytes per method-spec under realistic JML clause counts (1 requires + 1 ensures + optional loop_invariant) |
| **JVM compatibility** | Whether the carrier survives across JDK 8, 11, 17, 21, including ahead-of-time compilers (GraalVM `native-image`), proguard/R8, and downstream class transformers |
| **Stability** | Whether the carrier is tied to a specific spec or compiler version (e.g. JVMS major version, OpenAPI 3.x → 4.x churn) |
| **Roundtrip fidelity risk** | Likelihood that `extract(embed(spec))` returns a non-canonically-equal spec, given the carrier's encoding constraints |

The decision criterion for the primary candidate is: **survives roundtrip on ≥95% of inferred clauses, has at least one mature library for read/write, and does not require a JVM that the broader ecosystem has abandoned.**

---

## 2. Candidate carriers

### 2.1 Java bytecode annotations — `RuntimeVisibleAnnotations`

A custom annotation type `@JmlSpec(requires = "...", ensures = "...", assignable = "...", loopInvariant = "...")` written into each method's `RuntimeVisibleAnnotations` attribute. JML clauses are preserved verbatim as string literals.

- **Read/write:** ASM `AnnotationVisitor`, BCEL, ByteBuddy, javap, or pure reflection (`Method.getAnnotation(JmlSpec.class)`).
- **Granularity:** method, parameter, field, type, package — JLS already covers the elements JML needs.
- **Repeatability:** `@Repeatable` allows multiple `@JmlSpec` annotations per method, so each clause can be a separate annotation rather than concatenated strings (avoids escaping and quoting issues).

### 2.2 Custom class-file attribute — `JmlContract`

Per JVMS §4.7.1, vendors may define class-file attributes outside the standard set. JVMs ignore unrecognised attributes silently. Encoding is fully under our control: a structured binary tree of clause types (CONSTANT_Utf8 indices for symbols, op codes for boolean connectives, etc.).

- **Read/write:** ASM has a `Attribute` extension hook; nothing else in the ecosystem will decode it without a plugin.
- **Visibility:** invisible to reflection, javap (without `-private -v` it doesn't even mention the attribute), IDEs, and shading tools.

### 2.3 JML stub files — `.jml` / `.refines-jml`

The traditional JML deployment carrier: a sidecar source file containing only signatures + JML clauses, refining the binary class. OpenJML reads stubs natively.

- **Read/write:** OpenJML toolchain, JML Reference Implementation, ESC/Java2 (legacy).
- **Distribution:** must travel separately from the JAR (e.g., as `Class-Path:` reference, sibling artifact, or Maven classifier `-jml`).

### 2.4 OpenAPI 3.x extensions — `x-jml-*`

For REST endpoints rather than Java method calls. Each operation (`paths.<route>.<verb>`) gets `x-jml-requires`, `x-jml-ensures`, `x-jml-assignable` strings. OpenAPI parsers preserve unknown `x-*` properties.

- **Read/write:** swagger-parser, openapi-generator, springdoc-openapi.
- **Granularity:** per-operation, per-parameter, per-schema; matches the granularity of JAX-RS/Spring MVC controllers.

### 2.5 Pact / consumer-driven contracts

Pact files describe expected request/response pairs as concrete examples. Specifications would be encoded as additional metadata on each interaction (`metadata.jml.requires`, etc.) or as standalone matchers.

- **Read/write:** Pact JVM, Pact CLI.
- **Conceptual mismatch:** Pact is an example-based contract format, not a logical-spec format. Encoding `\forall`, `\sum`, or `\old` as Pact metadata defeats Pact's broker/verifier model — the broker cannot interpret the JML, only carry it. Pact becomes a transport, not a verifier.

### 2.6 Java records and sealed types as carriers

A `record` with named components (`requires`, `ensures`, ...) compiled into a constant `static final` field on the annotated class. Sealed-type variants encode clause types as separate record kinds (`PreCondition`, `PostCondition`, `LoopInvariant`).

- **Read/write:** standard reflection on the static field; no special tooling.
- **Granularity:** per-class, with per-method indexed by name+signature inside the carrier object.

### 2.7 Maven / Gradle artifact metadata

A separate Maven classifier (`-jml.jar`) or pom-property (`<jmlSpec>...</jmlSpec>`) carrying the specs as a sibling artifact.

- **Read/write:** Maven Resolver, Gradle metadata API.
- **Distribution:** travels with the artifact via the dependency graph.

### 2.8 ProGuard/R8 mapping streams *(not in original plan)*

ProGuard and R8 already maintain a side-channel mapping file (`mapping.txt`) and an embedded mapping-id constant. A spec stream could share the channel.

- **Read/write:** ProGuard / R8 toolchain only; no general consumer.
- **Stability:** tied to the obfuscator's version; survives obfuscation (which most other carriers do not).

### 2.9 JAR manifest entries *(not in original plan)*

`META-INF/MANIFEST.MF` per-entry attributes. JML spec stored as a base64-encoded JSON blob keyed by class+method signature.

- **Read/write:** `java.util.jar.Attributes` API.
- **Granularity:** the manifest is class-level at best (`Name:` headers on individual entries); per-method requires a side-table keyed by signature.

### 2.10 Class constant-pool string entries *(not in original plan)*

Specs encoded as a `CONSTANT_Utf8_info` reference held by an unused field initialiser. Survives any transformation that preserves bytecode validity.

- **Read/write:** any class-file parser; trivial to implement.
- **Cost:** pollutes the constant pool, may inflate it past the 65,535-entry limit on large classes.

---

## 3. Comparison table

| Carrier | Expressiveness | Tooling | Byte overhead/method | JVM compat | Stability | Fidelity risk |
|---|---|---|---|---|---|---|
| **Bytecode annotations (`@JmlSpec`)** | High (verbatim strings) | High (ASM, reflection, IDEs) | ~80–200 B (string-length dominated) | JDK 8+, GraalVM-friendly | Stable since Java 5 | Low (string-equality) |
| **Custom class attribute (`JmlContract`)** | Highest (structured) | Low (custom only) | ~40–100 B | JDK 1.0+; **risk:** ProGuard/R8 strip unknown attributes | Stable per JVMS | Low if encoding is canonical |
| **JML stub files** | Highest (native) | Medium (OpenJML; not IDEs) | 0 in bytecode (out-of-band) | All JDKs | Tied to JML grammar version | Low (text format) |
| **OpenAPI `x-jml-*`** | Medium-high (string blobs) | High (REST tooling) | N/A (REST-only) | N/A | OpenAPI 3.x stable; 4.x in preview 2026 | Low |
| **Pact metadata** | Low (example-driven) | High (Pact ecosystem) | N/A | N/A | Pact spec versioned | High — semantic mismatch |
| **Java records on class** | High (typed) | High (reflection) | ~120–300 B | JDK 16+ for `record`; backport to 8 needs codegen | Stable since records GA | Low |
| **Maven classifier sidecar** | Highest (any format) | High (Maven/Gradle) | 0 in main JAR | All JDKs | Stable | Low |
| **ProGuard/R8 mapping** | Medium | Very low (toolchain-only) | ~50 B | Stripped if not opted-in | Tied to obfuscator | Medium |
| **JAR manifest entries** | Medium (string blobs) | Medium (manifest API) | ~80 B header overhead | All JDKs | Manifest format frozen | Medium (escaping) |
| **Constant-pool string** | Medium | Very low (bytecode-only) | ~30–80 B | All JDKs | Stable | Medium (encoding) |

Byte-overhead estimates are based on a typical inferred spec for a 1-arg method: `requires p != null` (8 B), `ensures \result == this.f` (24 B), `assignable \nothing` (16 B), plus ~40 B annotation framing.

---

## 4. Roundtrip risk analysis

The plan's risk register flags spec-string mangling for complex JML expressions (`\sum`, `\forall`, nested `\old`). A canonical printer is needed for any string-based carrier. The following carriers minimise this risk:

- **Custom class attribute** — structured encoding eliminates string-mangling entirely; clauses are reconstructed from typed nodes.
- **Java records** — typed components survive without escaping.
- **Bytecode annotations with `@Repeatable`** — one annotation per clause sidesteps clause-separator escaping.

The string-blob carriers (manifest entries, constant-pool entries, single-string `@JmlSpec`) require an explicit canonical-form printer with property-based test coverage of `extract(embed(parse(s))) == parse(s)` for every JML construct emitted by the inferrer.

---

## 5. Reviewer-2 anticipated objection

> *Why a custom annotation type when JSR-305 (`@Nullable`, `@NotNull`) already addresses a subset of preconditions, and the Checker Framework has a richer annotation vocabulary?*

Response: JSR-305 was withdrawn before final standardisation (2012); only its informal annotations are in widespread use, and they cover only nullability. The Checker Framework's annotations are type-system-shaped (one annotation per type qualifier) and do not generalise to arbitrary JML clauses such as `\sum`, `\result == \old(this.f) + p`, or loop invariants. They are complementary signals, not a substitute carrier.

---

## 6. Recommendation

**Primary carrier: bytecode annotations (`@JmlSpec`) with `@Repeatable` per-clause.** Rationale: highest tooling support, lowest fidelity risk under repeat-annotation encoding, preserved across the JDK 8–21 deployment surface this thesis cares about, and read/writeable by ASM (which the rest of the embedder will already need).

**Secondary carrier: Maven classifier sidecar.** For specs too large to embed without bytecode bloat (e.g., methods with many quantified loop invariants), or when the JAR is signed and re-signing is infeasible.

**Tertiary carrier: JML stub files.** Drop-in for OpenJML-aware consumers; useful as an intermediate format the embedder can import.

**REST side: OpenAPI 3.x `x-jml-*` extensions.** Aligns with downstream tooling (springdoc-openapi auto-discovers). Sidecar JSON Schema as a fallback.

**Rejected (this round):**

- **Custom class attributes** — too risky given ProGuard/R8 strip behaviour without explicit `-keepattributes JmlContract`. Worth revisiting in a future optimisation pass once the annotation carrier is mature.
- **Pact metadata** — semantic mismatch.
- **Constant-pool entries** — too low-level; no upstream tooling support.
- **ProGuard mapping streams** — toolchain-coupled, not portable.

---

## 7. Open questions for Phase 2A.2 design doc

1. **Encoding the canonical form.** Are clauses normalised before embedding (e.g., `a > b` ↔ `b < a`) or preserved as the inferrer emitted them? Preference: preserve, with a separate `canonicalise()` operation called explicitly when comparing specs.

2. **Versioning.** The annotation carries `@JmlSpec(version = "1.0", ...)`. How are forward-incompatible spec-language changes (e.g., addition of `\forall_subset`, refactor of `assignable`) handled? Preference: semantic versioning of the annotation type itself, with a registry of known versions.

3. **Generic methods.** Erasure removes type parameters from the bytecode. Specs may quantify over the erased parameter; is the original parametric type recoverable from `Signature` attribute? Yes for source-compiled classes, no for synthetic ones.

4. **Inner classes / lambdas / records.** Each compiles to a synthetic class. Inferred specs must be relocated to the originating method or class — the embedder needs an annotation-target mapping table.

5. **Annotation retention semantics.** `RetentionPolicy.RUNTIME` vs `CLASS`. `CLASS` retention saves slight startup memory but is not visible to reflection. The integration tests in 2A.3 should cover both.

6. **Class loaders.** A consuming JVM that doesn't have the `@JmlSpec` annotation type on its classpath must not fail at class load. Annotations referencing missing types are tolerated by the JVM at load time but throw `TypeNotPresentException` on first reflective access — acceptable, document the constraint.

7. **Annotation size limits.** A single annotation's element values must fit in a `CONSTANT_Utf8_info`, which has a 65,535-byte limit. Long quantified specifications must be split across multiple annotations. Trigger threshold: ~50,000 chars per clause string. Almost no inferred spec hits this in practice; flag for the corner case.

---

## 8. Action items for the design doc (Phase 2A.2)

1. Define the `@JmlSpec` annotation class precisely — element types, defaults, repeatability, retention. Pick a fully-qualified name (`com.jml.spec.JmlSpec` proposed).
2. Specify the canonical printer + parser pair, with a property-based test plan against the existing inferrer's output for the 312-method Article 1 corpus.
3. Specify the OpenAPI extension's JSON Schema — exact key names, allowed types, validation rules.
4. Decide on the Maven classifier convention — `-jml`, `-spec`, or something else; pre-empt collision with existing classifier conventions in the Maven Central index.
5. Versioning policy — semantic version on the annotation, version-tagging convention on the OpenAPI extension and on the sidecar JAR.
6. Decide on annotation retention — recommendation: `RUNTIME` so reflection-based consumers can read specs; the byte cost is negligible.
7. Pick an annotation-target mapping policy for inner classes / lambdas / records — recommendation: synthetic carriers inherit specs from their originating user method via a `targetMethodSignature = "..."` annotation element.
8. Decide on a fallback path for consumers without the `@JmlSpec` type on their classpath — recommendation: tolerate `TypeNotPresentException` at the consumer side; document explicitly.
