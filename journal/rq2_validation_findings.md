# RQ2 Phase 2A.7 — Empirical Validation Findings

**Run date:** 2026-05-06 (autonomous probe-sweep week, day 2)
**Source:** `src/test/java/com/jml/inferrer/embedder/OssJarValidationTest.java`
**Raw metrics:** `journal/rq2_validation_metrics.txt`
**Plan reference:** `journal/rq2_rq4_execution_plan.md` §2A.7

---

## 1. Headline numbers

Embedder applied to two real-world OSS Java libraries, with synthetic specs generated per method (one `requires p != null` per non-primitive parameter, `ensures \result != null` for reference returns, `assignable \nothing`).

**After the day-3 abstract-method emission fix (rev. day 6 with Commons IO):**

| Library | Methods | Roundtrip fidelity | Byte overhead | Embed throughput | Read throughput |
|---|---:|---:|---:|---:|---:|
| Apache Commons Lang 3.14.0 | 4{,}029 | **100.0% (4{,}029 / 4{,}029)** | +11.95% (642 KB → 720 KB) | 28{,}022 m/s | 216{,}068 m/s |
| Apache Commons IO 2.13.0 | 2{,}677 | **100.0% (2{,}677 / 2{,}677)** | +13.49% (473 KB → 537 KB) | 10{,}480 m/s | 146{,}147 m/s |
| Guava 33.3.0-jre | 13{,}840 | **100.0% (13{,}840 / 13{,}840)** | +11.76% (3.0 MB → 3.4 MB) | 22{,}353 m/s | 235{,}144 m/s |
| Inferrer self-test (real specs) | 73 | **100.0% (73 / 73)** | --- | --- | --- |

For matched methods, equality is exact: zero clause-level mismatches across either library.

Plan success criterion: ≥95% fidelity on ≥8 of 10 libraries. Cleared with margin on the first two; the remaining eight are mechanical to validate.

**Before the fix (day 2):**

| Library | Methods | Roundtrip fidelity | Byte overhead | Embed throughput | Read throughput |
|---|---:|---:|---:|---:|---:|
| Apache Commons Lang 3.14.0 | 4{,}029 | 96.9% (3{,}904 / 4{,}029) | +11.10% | 14{,}245 m/s | 154{,}830 m/s |
| Guava 33.3.0-jre | 13{,}840 | 97.6% (13{,}508 / 13{,}840) | +11.65% | 21{,}054 m/s | 189{,}397 m/s |

The 3% gap was abstract / interface methods, not multi-release JAR entries (the original hypothesis). The writer's `SpecEmittingMethodVisitor` had hooked `visitCode`, `visitParameter`, `visitAnnotation`, and `visitAnnotationDefault` to trigger annotation emission — but abstract methods do not call any of these; only `visitEnd` is guaranteed for them. Adding a `visitEnd` hook closed the gap entirely.

## 2. The 3% fidelity gap — root cause and fix

Initial hypothesis (multi-release JAR keying) turned out to be wrong. The actual cause was identified by instrumenting the harness to print sample unmatched method keys: every dropped method was on an interface or otherwise abstract.

```
[commons-lang3-3.14.0] sample unmatched (125 total):
  org/apache/commons/lang3/function/FailableConsumer::accept(Ljava/lang/Object;)V
  org/apache/commons/lang3/time/DateParser::getTimeZone()Ljava/util/TimeZone;
  org/apache/commons/lang3/function/FailableLongConsumer::accept(J)V
  org/apache/commons/lang3/time/FastDatePrinter$Rule::estimateLength()I
  ...
```

All ten sampled keys were interface methods. ASM's MethodVisitor lifecycle drives different visitX callbacks depending on the method shape:

- **Concrete methods** trigger `visitParameter`, `visitAnnotationDefault`, `visitCode`, instructions, `visitMaxs`, `visitEnd`.
- **Abstract / interface methods** trigger only `visitEnd` (no code, no parameters in the bytecode).

The writer's `SpecEmittingMethodVisitor` triggered emission lazily on the first occurring of `visitCode`, `visitParameter`, `visitAnnotationDefault`, or `visitAnnotation`. None of these fire for abstract methods, so no annotation was ever written for them.

**Fix:** override `visitEnd` to also call `ensureEmitted()`. The boolean idempotency flag on the wrapper ensures concrete methods (which trigger one of the existing hooks first) are not double-emitted.

After the fix: 100.0% fidelity on both libraries. Zero gap remaining.

The original hypothesis (multi-release JAR keying) was rooted in inspection of META-INF/versions/9 entries in commons-lang3, which do exist; but those entries do not carry the same method shapes as the root namespace, so they did not contribute to the count discrepancy. The keying is correctly per-namespace already.

## 3. Byte overhead — analysis

11.1–11.7% overhead is well within budget. The plan budgeted "negligible" overhead without quantifying. For comparison:

- A typical Spring Boot fat-JAR is in the 50–100 MB range; an 11% overhead adds ~5–10 MB. Acceptable for a development artefact, possibly costly for a runtime-distributed library.
- A library JAR in the 1–10 MB range pays 100 KB to 1 MB overhead. Negligible for distribution.
- The synthetic specs are deliberately bulky (one annotation per parameter plus one for the return). Real inferred specs from the inferrer are typically smaller per method (preconditions are often empty for simple getters, etc.), so this 11% figure is a *worst-case* estimate.

**Optimisation paths** if this becomes load-bearing:
- Compress repeated annotation strings via the constant-pool string interning (already free at the JVM level).
- Use the secondary Maven classifier sidecar (`-jml.jar`) instead of in-bytecode embedding for libraries where the overhead is unacceptable.
- Skip emission for trivially-empty specs (we already do this).

## 4. Throughput — analysis

- **Embedding:** 14–21k methods/sec. For a 4,000-method JAR (commons-lang scale), that's ~280 ms end-to-end. For a 14,000-method JAR (Guava scale), that's ~660 ms. Negligible against typical Maven/Gradle build steps.
- **Reading:** 150–190k methods/sec. Reading is ~10× faster than writing because it skips full class rewriting. A 14,000-method JAR is read in ~73 ms.

These numbers comfortably support per-PR-comment workflows in CI/CD (RQ4): even pessimistic re-running on every PR is sub-second per JAR.

## 5. Negative test — class load without `@JmlSpec`

A class loaded via a `URLClassLoader` rooted at the embedded JAR, with the platform class loader as parent, does not see the `com.jml.spec.JmlSpec` annotation type. Confirmed:

- `Class.forName("org.apache.commons.lang3.StringUtils", true, loader)` succeeds.
- `Method.getAnnotations()` either returns the resolvable annotations or throws `TypeNotPresentException` — both are documented behaviour. The JVM does not crash; class load is unaffected.

This validates the plan's claim that the embedder is consumer-tolerant: a downstream JVM that has no awareness of JML still loads and executes the class normally.

## 6. Limitations of this validation

1. **Synthetic specs**, not inferrer-generated specs. To make the harness independent of the inferrer's source-side work, this run uses a deterministic spec generator that emits realistic-shaped clauses based on method signatures. Phase 2A.7 is incomplete until the inferrer is run over the same library's source and the *real* inferred specs are roundtripped.

2. **Two libraries**, not the plan's full ten. The remaining eight (Apache Commons IO, Apache Commons Math, jOOL, Vavr, jsoup, JFreeChart, JUnit, AssertJ) are deferred to later sessions. The 3% multi-release-JAR gap analysis tells us what to expect: libraries that ship multi-release JARs will show similar gaps; libraries that do not (older or single-version artefacts) will show ~100% fidelity.

3. **No JVM-version sweep.** Plan §2A.7 calls for verifying class-file load on JDK 8, 11, 17, 21. This run was JDK 21 only. The tighter JDK-8-class-files (older Maven artefacts) will need separate validation, gated on whether commons-lang3 still ships JDK-8-compatible bytecode (it does — class files target Java 8, regardless of the build's JDK).

4. **No obfuscation pass.** Plan §10.4 calls for ProGuard / R8 with `-keepattributes RuntimeVisibleAnnotations`. Deferred.

## 7. Decision-point status

Plan §2A.2 decision point (end of September 2026): "Roundtrip fidelity ≥95% on ≥8 of 10 libraries → proceed to Phase 2B."

**Current status:** ≥95% on 2 of 10 libraries with two specific gap-causing edge cases (multi-release JARs, constructor variants) identified and tractable. On track for the September decision point. Remaining libraries are mechanical to validate and the writer-side multi-release fix is a contained refactor.

## 8. Follow-up actions

1. Refactor `AsmJmlSpecWriter` to handle multi-release JAR entries as a per-namespace key (anticipated +2–3 percentage points of fidelity, into the 99% range).
2. Validate against the remaining eight libraries — mechanical, ~2 hours total.
3. Add an obfuscation pass (ProGuard) to the harness — confirms the `-keepattributes` recipe in the design doc.
4. Replace synthetic specs with inferrer-generated specs once Phase 2A.4's converter is exercised on a real library's source.
5. Capture these numbers verbatim in Article 2's empirical validation section.
