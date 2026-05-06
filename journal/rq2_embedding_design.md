# RQ2 Phase 2A.2 — Specification Embedding: Format Design

**Drafted:** 2026-05-06 (autonomous probe-sweep week, day 1)
**Status:** working draft — to be reviewed before module implementation begins
**Source plan:** `journal/rq2_rq4_execution_plan.md` §2A.2
**Companion:** `journal/rq2_embedding_survey.md` (the carrier comparison; informs §2 below)

---

## 0. Document scope

This document specifies the on-the-wire format and consumption API for the primary, secondary, and tertiary carriers chosen in the survey. It does not specify the Maven module layout (covered in §2A.3 prep) or the OpenAPI extractor implementation (covered in §2A.6). It does specify enough that an implementer can write the embedder and extractor against a fixed contract.

Sections:

1. Goals and non-goals.
2. Carrier choice recap (one paragraph).
3. The `@JmlSpec` annotation type.
4. Canonical form for JML clause strings.
5. Annotation-target mapping for synthetic classes.
6. The OpenAPI extension format.
7. The Maven classifier sidecar format.
8. The consumer API.
9. Versioning, evolution, and deprecation policy.
10. Property-based test plan.
11. Threats to fidelity and mitigations.

---

## 1. Goals and non-goals

**Goals.**

- Specifications produced by JML-Inferrer survive a roundtrip `extract(embed(spec))` with byte-for-byte equality on the canonical form, on at least 95% of inferred clauses across the Article 1 corpus.
- Mainstream JDK 8–21 toolchains (javac, javap, ASM, ByteBuddy, reflection, Maven, Gradle) read the carrier without bespoke plugins.
- Consumers without the `@JmlSpec` type on their classpath load the annotated class without `NoClassDefFoundError`. Reflective access is allowed to throw `TypeNotPresentException`; that is the documented constraint.
- The format is forward-compatible: a v1 reader handles a v2 annotation by ignoring unknown elements, not by crashing.

**Non-goals.**

- Acting as the sole specification carrier. JML stub files remain the source of truth for OpenJML's verifier; the embedded annotations are a redistribution channel, not a verification input.
- Carrying executable preconditions or runtime assertion checking. Specs ride alongside the bytecode; the consumer chooses what to do with them.
- Retrofitting onto class files compiled before this thesis. The format is forward-emitting only.
- Surviving aggressive obfuscation. ProGuard / R8 may rewrite type names, breaking string-form references inside JML clauses. Canonical form (§4) preserves the source-level type names; consumers running on obfuscated bytecode are expected to feed the obfuscator's mapping file alongside.

---

## 2. Carrier choice recap

The survey settled on bytecode annotations as the primary carrier, OpenAPI 3.x extensions as the REST-side primary, and Maven classifier sidecars as the secondary fallback for oversized specs. JML stub files remain the tertiary input format. This document specifies all three.

---

## 3. The `@JmlSpec` annotation type

### 3.1 Fully-qualified name and module

```
package com.jml.spec;
@Repeatable(JmlSpecs.class)
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR, ElementType.FIELD, ElementType.TYPE})
public @interface JmlSpec {
    Kind kind();
    String text();
    int order() default 0;
    String version() default "1.0";
    String targetSignature() default "";

    enum Kind { REQUIRES, ENSURES, ASSIGNABLE, SIGNALS, LOOP_INVARIANT, LOOP_DECREASES, INVARIANT, ALSO_PARTITION, AXIOM, INITIALLY }
}

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR, ElementType.FIELD, ElementType.TYPE})
public @interface JmlSpecs { JmlSpec[] value(); }
```

The annotation lives in a published artefact `com.jml:jml-spec:1.0.0` containing only the annotation type, the `Kind` enum, and a small canonicalisation utility (§4.4). No transitive dependencies. ~12 KB JAR. Apache 2.0 licence to match the inferrer.

### 3.2 Element rationale

- `kind()` — typed clause kind, removes the need for the parser to disambiguate string form `requires X` from `ensures Y`.
- `text()` — the clause body in canonical form (§4). For `requires X`, this is just `X`, not `requires X`.
- `order()` — preserves the inferrer's emission order across `requires` clauses where order may be load-bearing for well-definedness chains (see `PreconditionAnalyzer.analyzeFieldArrayIndexConstraints` in the inferrer source — JML evaluates well-definedness left-to-right; reordering null-checks past dereferences breaks proofs). Default `0`; multiple annotations of the same kind are sorted by `order` ascending.
- `version()` — the spec-language version; defaults to `1.0`. Forward-incompatible changes bump the major version. A v1 consumer ignores any annotation whose version's major is greater than its supported maximum.
- `targetSignature()` — a JVM method descriptor (e.g., `(I)Ljava/lang/String;`) that, when non-empty, redirects this annotation's spec to a different method on the same class. Used for synthetic carriers (lambdas, inner classes, records — §5).

### 3.3 Repeated annotation usage

```java
@JmlSpec(kind = REQUIRES, text = "p != null", order = 1)
@JmlSpec(kind = REQUIRES, text = "p.length > 0", order = 2)
@JmlSpec(kind = ENSURES, text = "\\result == p.length")
@JmlSpec(kind = ASSIGNABLE, text = "\\nothing")
public int firstLength(String[] p) { ... }
```

The repeated form is the standard form. Single-`@JmlSpec` usage is allowed for trivial cases but provides no information the repeated form can't carry.

### 3.4 Why per-clause, not per-method

A single `@JmlSpec(requires={"a","b"}, ensures={"c"})` would be syntactically smaller. It is rejected for two reasons:

1. **Order preservation across kinds.** JML clause emission order across kinds is not significant for verification, but **order within `requires` is significant** (left-to-right well-definedness). The struct-shaped annotation requires a separate `requiresOrder` element, which complicates the schema. The flat repeated form puts ordering in one element (`order`).

2. **Forward compatibility.** Adding a new clause kind in v2 requires adding a new annotation element in the struct form; that breaks v1 readers. In the flat form, v2 simply emits annotations whose `kind` v1 doesn't recognise; v1 ignores them.

### 3.5 Annotation byte budget

Each `@JmlSpec` is roughly:
- 12 B annotation framing
- 4 B per element (`kind`, `text`, `order`, `version`, `targetSignature`)
- variable B per element value (`text` dominates: 8–200 B typical)
- Total: ~50–250 B per clause

A typical inferred spec for a 1-arg method (3 requires + 1 ensures + 1 assignable + 1 loop_invariant) costs ~600 B in the bytecode. On the Article 1 corpus (312 methods, mean ~5 clauses), total embedding overhead per JAR is ~1 MB — negligible against the typical artefact size of 10s of MB.

### 3.6 Retention

`RetentionPolicy.RUNTIME`. The byte cost over `CLASS` is negligible (`RuntimeVisibleAnnotations` vs `RuntimeInvisibleAnnotations` are the same shape; only the attribute name differs). Reflection-based consumers — runtime verification, IDE tooltips, downstream test generators — need RUNTIME. Setting RUNTIME on the canonical type does not preclude downstream re-emission as CLASS by tools that prefer to suppress reflection.

---

## 4. Canonical form for JML clause strings

A canonical form is required so that string equality `extract(embed(s)).text() == s` is meaningful. Without canonicalisation, equivalent specs that differ in whitespace, parenthesisation, or operator spelling would appear as roundtrip failures.

### 4.1 Lexical normalisation

- All whitespace runs collapse to a single space.
- No leading or trailing whitespace.
- No spaces immediately inside `(`, `[`, or before `)`, `]`, `,`, `;`.
- Single spaces around binary operators (`+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<=`, `>=`, `<`, `>`, `&&`, `||`, `==>`, `<==>`).
- No space between unary operators and their operand (`!x`, `-x`).
- No space around `.` or `::`.

### 4.2 Operator spelling

JML allows two spellings for several operators: `==>` and `=>` for implication, `<==>` and `<=>` for biconditional, `<:` and `subtypeof`. The canonical form uses **the longer arrow forms** (`==>`, `<==>`) and **the symbolic forms** (`<:`). This matches OpenJML's pretty-printer.

### 4.3 Quantifier syntax

```
(\forall T x; range; body)
(\exists T x; range; body)
(\sum T x; range; body)
(\product T x; range; body)
(\num_of T x; range; body)
```

Range is mandatory in canonical form even when the source allowed an unbounded quantifier. Unbounded quantifiers expand to `(\forall int x; true; body)` — an inefficient form for the verifier but unambiguous in the carrier. Quantifier variables are alpha-renamed to `k` (single quantifier), `i, j, k` (nested), preserving inner-out reading.

### 4.4 Parenthesisation

Minimum parens for unambiguous reparse. Operator precedence matches JLS: `||` < `&&` < `==>` < relational < additive < multiplicative < unary. Where two operators of equal precedence chain (`a + b - c`), left-associative (`(a + b) - c`) is the canonical reading; print as `a + b - c` (parens are redundant). Where left-associativity would change semantics from the source (`a == b == c`), parens are inserted: `(a == b) == c`.

### 4.5 Identifier quoting

JML keywords used as identifiers (e.g., a parameter named `result`) are escaped with a backtick: `` `result` ``. This is the JML 1.0+ convention.

### 4.6 The canonicaliser API

```java
package com.jml.spec;

public final class JmlCanonicaliser {
    public static String canonicalise(JmlSpec.Kind kind, String text) { ... }
    public static boolean equalsCanonical(String a, String b) { ... }
}
```

The canonicaliser uses an internal AST built from a small JML expression grammar (the inferrer already has this; package-port to `jml-spec`). It does not attempt semantic equivalence (e.g., `a > b` and `b < a` remain distinct). Semantic equivalence is left to OpenJML.

### 4.7 Failure modes

If the canonicaliser cannot parse a clause (e.g., a clause containing an unknown JML extension), it returns the input unmodified and emits a warning. The annotation carries the unmodified text; consumers will see exactly what the inferrer emitted. This is intentional: a non-roundtrippable clause must remain debuggable rather than be silently mangled.

---

## 5. Annotation-target mapping for synthetic classes

Inner classes, lambdas, method references, and `record` accessors compile to synthetic classes or methods. The user-meaningful method (the one the inferrer reasons about) is not the same class file as the bytecode the JVM executes. The mapping table below resolves each synthetic shape to a primary target.

| Source construct | Synthetic carrier | Primary target |
|---|---|---|
| Lambda body | `lambda$<method>$N` synthetic method on the enclosing class | The enclosing user method |
| Method reference | `lambda$<method>$N` or `LambdaMetafactory` invokedynamic | The referenced method |
| Anonymous inner class method | `OuterClass$1.method` | The user method on the anonymous class |
| Local class method | `OuterClass$Local.method` | The user method on the local class |
| `record` accessor | `MyRecord.field()` synthetic | The user field declaration |
| `record` canonical constructor | `MyRecord.<init>` | The user record declaration |

The embedder writes the spec onto the **synthetic** carrier (so reflection on the bytecode finds it), with `targetSignature` set to the method descriptor of the user method that originally received the inferred spec. The extractor reads from the synthetic carrier and resolves `targetSignature` back to the user-meaningful key.

For lambdas and method references, the user-meaningful key is the enclosing method's signature; lambdas are not independent specifiable units, they are sub-expressions. The inferrer either emits the lambda's spec as a clause on its enclosing method (preferred) or skips it (current behaviour).

---

## 6. OpenAPI extension format

### 6.1 Per-operation extension

```yaml
paths:
  /orders/{id}:
    get:
      x-jml-requires:
        - "id != null"
        - "id > 0"
      x-jml-ensures:
        - "\\result != null ==> \\result.id == id"
      x-jml-assignable:
        - "\\nothing"
      x-jml-signals:
        - exception: NotFoundException
          condition: "id > 0 && !exists(id)"
```

Each `x-jml-*` is an array of canonical-form strings. Order within the array is significant for `x-jml-requires` (well-definedness), insignificant elsewhere. `x-jml-signals` is an array of `{exception, condition}` objects — exception types are JVM internal names (`com/example/NotFoundException` slash form) so cross-language consumers can resolve them.

### 6.2 Per-schema extension

```yaml
components:
  schemas:
    Order:
      type: object
      x-jml-invariant:
        - "this.total >= 0"
        - "this.lines != null"
      properties:
        total: { type: integer, x-jml-bounds: "0..1000000" }
```

`x-jml-invariant` on a schema corresponds to a class invariant on the deserialised type. `x-jml-bounds` on a property is shorthand for a `\old(this.total) >= 0 && this.total <= 1000000` invariant; the bound shorthand is convenience syntax for human readers.

### 6.3 JSON Schema for the extension

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://jml-inferrer.org/schemas/openapi-jml-extension-1.0.json",
  "title": "OpenAPI JML extension",
  "type": "object",
  "patternProperties": {
    "^x-jml-(requires|ensures|assignable|loop-invariant|invariant)$": {
      "type": "array",
      "items": { "type": "string" }
    }
  },
  "properties": {
    "x-jml-signals": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["exception", "condition"],
        "properties": {
          "exception": { "type": "string" },
          "condition": { "type": "string" }
        }
      }
    }
  }
}
```

The schema is published alongside the annotation artefact. Consumers can validate an OpenAPI document against the schema to confirm well-formedness independently of the inferrer.

### 6.4 Sidecar JSON fallback

When the OpenAPI document cannot be modified (e.g., generated from controller annotations and published by the framework), the embedder writes a sibling file `<service>.contract.json` keyed by `<route> <verb>`:

```json
{
  "version": "1.0",
  "operations": {
    "GET /orders/{id}": {
      "requires": ["id != null", "id > 0"],
      "ensures": ["\\result != null ==> \\result.id == id"]
    }
  }
}
```

The sidecar carries the same content as the OpenAPI extension; consumers use whichever they have.

---

## 7. Maven classifier sidecar format

For specs whose total bytecode footprint exceeds an annotation budget (default 50,000 chars per clause string, ~10 KB per method), or for cases where the JAR is signed and the embedder cannot re-sign (e.g., enterprise deployments), the embedder writes a sibling JAR with classifier `-jml`.

### 7.1 Sidecar layout

```
mylibrary-1.0.0-jml.jar
  META-INF/
    MANIFEST.MF
    jml-version: 1.0
    jml-source-jar: mylibrary-1.0.0.jar
    jml-source-sha256: <hex>
  com/example/MyClass.jmlspec
```

Each `.jmlspec` is a single text file. The format is exactly the JML stub file format (covered already by OpenJML's stub reader), so the sidecar can be loaded directly by OpenJML without an intermediate parse.

### 7.2 Discovery

Consumers discover the sidecar via:
1. Maven coordinate `<group>:<artifact>:<version>:jml` — explicit dependency on the sidecar.
2. Module-path scan — a `META-INF/jml-sidecar.json` file lists the corresponding main artefact's coordinates.
3. Classpath sibling — the consumer looks for `<jar-name>-jml.jar` next to the main jar on the classpath.

The embedder writes (1); the extractor tries (1), (3), then (2) in order.

---

## 8. Consumer API

### 8.1 Reading from bytecode

```java
package com.jml.spec.read;

public interface JmlSpecReader {
    Optional<MethodSpec> readForMethod(Class<?> clazz, String methodName, Class<?>... paramTypes);
    Map<MethodKey, MethodSpec> readAll(Class<?> clazz);
    Map<MethodKey, MethodSpec> readJar(Path jar) throws IOException;
}

public record MethodKey(String className, String methodName, String descriptor) { ... }

public record MethodSpec(
    List<String> requires,        // canonical form, ordered
    List<String> ensures,
    List<String> assignable,
    List<String> loopInvariant,
    List<SignalsClause> signals,
    String version
) { ... }
```

### 8.2 Reading from OpenAPI

```java
package com.jml.spec.read;

public interface OpenApiJmlReader {
    Optional<OperationSpec> readForOperation(OpenAPI document, String path, String method);
    Map<OperationKey, OperationSpec> readAll(OpenAPI document);
}
```

### 8.3 Writing — embedder

The embedder's API is symmetric:

```java
package com.jml.spec.write;

public interface JmlSpecWriter {
    void embedJar(Path inputJar, Path outputJar, Map<MethodKey, MethodSpec> specs) throws IOException;
    void embedClass(byte[] inputClass, byte[] outputClass, Map<String, MethodSpec> specs) throws IOException;
    void writeSidecar(Path inputJar, Path sidecarJar, Map<MethodKey, MethodSpec> specs) throws IOException;
}
```

### 8.4 Pipeline integration

`MethodSpecificationInferrer` already maintains a `SpecificationCache` keyed by method signature. The integration point is to extend the cache lookup: on miss, attempt to read from an embedded annotation on the callee class before falling back to "uninterpreted callee" semantics.

---

## 9. Versioning, evolution, and deprecation policy

### 9.1 Annotation type version

The `version()` element of `@JmlSpec` carries a semver string. Major changes (e.g., a clause kind whose semantics changed): bump major. Minor changes (new clause kind, new element): bump minor. Patch changes (clarification, no on-the-wire change): bump patch.

A consumer is parameterised by a maximum supported major version. Annotations with a higher major are skipped with a warning. Annotations with the same major and a higher minor are read, with unknown elements ignored.

### 9.2 Adding a clause kind

New `Kind` enum values are appended; consumers tolerant of unknown kinds (the recommended consumer pattern: `if (!Kind.values()contains(k)) skip;`) read the rest of the annotations correctly. v1 readers see v2's new kinds as unknown and skip them; v2 readers see v1's annotations and read them as a strict subset.

### 9.3 Removing a clause kind

A clause kind is never removed in a minor version. Removal requires a major bump. The removed kind is annotated `@Deprecated` for at least one major version cycle before removal.

### 9.4 Spec language version

Independent of the annotation type version, the spec-language version (currently JML 1.0+) tracks the syntax of the `text()` element. JML evolves slowly; major bumps are unlikely. Annotation `version` tracks the annotation type, not the spec language; if JML ever evolves incompatibly, a separate `specLanguageVersion()` element will be added.

---

## 10. Property-based test plan

The embedder/extractor pair is exercised by property-based tests over the inferrer's existing 312-method Article 1 corpus plus the 576-test verification corpus.

### 10.1 Roundtrip property

For every `(class, method)` in the corpus:
- Run the inferrer to produce `MethodSpec spec`.
- Embed `spec` into the class file.
- Extract the embedded annotations back to a `MethodSpec spec'`.
- Assert: `JmlCanonicaliser.equalsCanonical(spec, spec') == true`.

Failure mode: a clause that does not roundtrip (canonicaliser mangles or extractor loses data). Target failure rate: <5% on Article 1, <2% on the verification corpus (the verification corpus is the inferrer's own training input and should be pristine).

### 10.2 Forward-compatibility property

- Embed a v2 annotation (with a kind unknown to v1) into a class.
- Read it with a v1 reader.
- Assert: v1 reader returns the v1-known clauses; logs a warning for the v2-only clause.

### 10.3 Missing-annotation-type property

- Embed annotations into a class.
- Strip the `@JmlSpec` type from the consumer's classpath.
- Load the class.
- Assert: `Class.forName` succeeds; reflection on annotations throws `TypeNotPresentException` cleanly.

### 10.4 Obfuscation tolerance property

- Run the embedded JAR through ProGuard with `-keepattributes RuntimeVisibleAnnotations,RuntimeVisibleParameterAnnotations,Signature`.
- Assert: extractor reads the same specs after obfuscation as before.

### 10.5 Synthetic-target property

- Take a class with lambdas, anonymous inner classes, and records.
- Run the inferrer.
- Embed.
- Extract from the synthetic carriers.
- Assert: every spec's `targetSignature` resolves to a user-meaningful method.

---

## 11. Threats to fidelity and mitigations

| Threat | Mitigation |
|---|---|
| String mangling in `text()` (whitespace, operator spelling, quantifier renames) | §4 canonicaliser; property test §10.1 |
| Constant-pool bloat on classes with many specs | Per-method size budget; spill to sidecar (§7) when budget exceeded |
| Annotation type missing from consumer classpath | Tolerated by JVM at load; reflection raises `TypeNotPresentException`; documented constraint (§1) |
| ProGuard / R8 strip annotations | `-keepattributes RuntimeVisibleAnnotations` + sample `proguard.cfg` shipped with the artefact |
| Lambda / inner-class target resolution drifts across javac versions | Property test §10.5 across javac 8, 11, 17, 21 |
| OpenAPI extension stripped by an aggressive parser | Sidecar JSON fallback (§6.4); explicit allowlist of `x-jml-*` keys in the consumer |
| Versioning confusion between annotation version and JML language version | Dedicated elements; documented in §9; v1 reader exits cleanly on unknown major |
| Long quantified specs exceed CONSTANT_Utf8 64KB limit | Spill to sidecar; warning at embedding time |
| OpenAPI document not editable (auto-generated by springdoc) | Sidecar JSON fallback (§6.4) |
| Repeated annotation order not preserved by some annotation processors | `order()` element makes order recoverable from any storage shape |

---

## 12. Open items for module implementation

1. Concrete Maven coordinates: `com.jml:jml-spec:1.0.0` (annotation), `com.jml:jml-embedder:1.0.0` (writer), `com.jml:jml-extractor:1.0.0` (reader). Confirm `com.jml` group ID is available on Maven Central before publishing.
2. Decide whether `jml-embedder` and `jml-extractor` ship as one artefact or two. Recommendation: one (`jml-embedding`) with read-only consumers depending only on `jml-spec`.
3. ASM major version: 9.x (current) or pin to 9.6+? Pin to the lowest version that supports JDK 21 class files (9.5+).
4. Logging: SLF4J interface (matches the rest of the inferrer) or `java.util.logging` (zero dependency)? Recommendation: SLF4J + a `slf4j-nop` runtime exclusion so the consumer chooses.
5. Default `targetSignature` resolution policy when the synthetic shape isn't in the table in §5: log a warning and write to the synthetic carrier with `targetSignature = ""`. Consumers handle empty `targetSignature` by treating the synthetic method as itself the target.
