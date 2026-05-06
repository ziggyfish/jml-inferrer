# Thesis Progress Review

**Last update:** 2026-05-06
**Phase:** end of autonomous RQ2/RQ3/RQ4 week (six sessions, 2026-05-06)
**Test surface:** 140 green tests across the codebase, 0 regressions.

---

## Status by research question

### RQ1 — Heuristic specification inference (Article 1)

**Article 1 status:** drafted; system-maturity update applied (LOC 11,600 → 20,000; verification-suite size 237 → 576; OpenJML fork + solver-config paragraph added). 7 Quality Gates run twice. PDF builds clean (21 pages). Headline empirical numbers (272% test count, 40.7 pp mutation, Cohen's $d = 2.41$, 94.2/89.3 / 87.6/78.1 precision-recall) tied to the LLM-experiment snapshot and unchanged.

**Inferrer maturity:** verification-suite failure count plateaued at 86 (fix30, 2026-04-29 paired-emission cycle). One additional analysis-level heuristic shipped 2026-05-06: P1 cross-field-length precondition (`PreconditionAnalyzer.analyzeFieldBoundedLoopArrayLength`), targets the matrix-shape failures. End-to-end Docker verification of P1 deferred per user steer ("not too fussed about RQ1, remaining tests are stretch goals").

**Outstanding (acknowledged stretch):** P2 (2D diagonal forall), P3 (accumulator overflow bounds + matching loop invariants), recursion / heap-structural / sorted-array shapes. Verification baseline started on 2026-05-06 ran for 6+ hours and exited mid-`StringOperationVerificationTest` (11 of ~24 suites completed, 67 cumulative failures); not restarted.

**Pre-submission packaging (carried forward):** Wiley `wileyNJD-v2.cls` swap, ORCIDs, cover letter, suggested-reviewers list.

---

### RQ2 — Spec embedding in compiled artefacts and OpenAPI (Article 2)

**Article 2 status:** drafted; 13 pages; builds clean; 7 Quality Gates run twice. Three-library empirical evidence + real-inferred-specs corpus.

**Phase 2A milestones (all delivered):**

| Phase | Plan budget | Delivered |
|---|---|---|
| 2A.1 Survey | 2 weeks | ✅ `journal/rq2_embedding_survey.md` |
| 2A.2 Format design | 2 weeks | ✅ `journal/rq2_embedding_design.md` + `JmlCanonicaliser` (16 tests) |
| 2A.3 Bytecode embedder/extractor | 3 weeks | ✅ `AsmJmlSpecWriter` + `AsmJmlSpecReader` + sidecar (6 tests) |
| 2A.4 Inferrer integration | 2 weeks | ✅ `InferrerSpecConverter` + roundtrip test (4 tests) |
| 2A.5 OpenAPI extension | 2 weeks | ✅ `OpenApiJmlExtension` (6 tests) |
| 2A.6 Spring REST inferrer | 3 weeks | ✅ `RestEndpointInferrer` (7 tests) |
| 2A.7 Empirical validation | 4 weeks | ✅ 3 OSS libraries + corpus run; `OssJarValidationTest`, `CorpusLevelRoundtripTest` |

**Empirical headline:** **100.0% roundtrip fidelity across 4 corpora** (Apache Commons Lang 3.14.0, Apache Commons IO 2.13.0, Guava 33.3.0-jre — totalling 20,546 methods of synthetic specs, plus 73 real inferrer-generated specs from the inferrer's own model+visitor+processor packages). Bytecode-size overhead 11.76%–13.49%; embedding throughput 10k–28k methods/second; reading throughput 146k–235k methods/second. Negative test (consumer without `@JmlSpec`) passes.

**Outstanding for full Phase 2A:**
- 7 protocol libraries unvalidated (Apache Commons Math, jOOL, Vavr, jsoup, JFreeChart, JUnit, AssertJ) — mechanical
- JDK version sweep (8, 11, 17 — currently JDK 21 only)
- ProGuard / R8 obfuscation tolerance — design only
- REST extension validated by construction; no real Spring service tested end-to-end
- JmlCanonicaliser scope-aware quantifier alpha-renaming (currently no-op)

---

### RQ3 — Compositional inference + test generation (Article 3)

**Status:** scaffold + four behavioural extensions delivered; **Article 3 not started**.

**Phase 2B.1 (the hardest task — 10 weeks budgeted in the plan):**

| Component | Status |
|---|---|
| Two-pass driver, SCC-based via Tarjan's algorithm | ✅ |
| Per-call-site precondition substitution with `\b`-word-boundary replace | ✅ |
| Branch-lifting (if-then, else, nested, side-effect rejection) | ✅ |
| Polymorphic dispatch via class hierarchy | ✅ |
| Termination tracking with conservative auto-detector | ✅ |
| Strict-extension empirical demonstration | ✅ (15 tests green) |
| Side-effecting argument substitution (`\let` binding) | ❌ |
| Aliasing tracking | ❌ |
| Loop lifting through compositional WP | ❌ |
| Predicate-language fragment restriction | ❌ |

**Outstanding — substantial:**
- **Phase 2B.2 EvoSuite bridge** (4 weeks budgeted) — not started
- **Phase 2B.3 benchmark selection** (Defects4J + microservices, 3 weeks) — not started
- **Phase 2B.4 mutation-testing pipeline** (PIT, 2 weeks) — not started
- **Phase 2B.5 statistical analysis** (Cliff's δ, Bonferroni, 1 week) — not started
- **No end-to-end verification.** All 15 compositional tests are analysis-level; nothing has been run through OpenJML to confirm the composed specs actually verify.
- **Article 3** — not drafted

This is the principal scope gap remaining in the thesis.

---

### RQ4 — CI/CD integration in Agile workflows (Article 4)

**Article 4 status:** drafted; 11 pages; builds clean. Honest about scope: claims design + reference implementation + self-test, **not** empirical evaluation.

**Phase 3 milestones (delivered + planned):**

| Phase | Plan budget | Status |
|---|---|---|
| 3.1 Reference workflow design | 3 weeks | ✅ |
| 3.2 GitHub Actions prototype | 4 weeks | ✅ working YAML, dogfooded against this repo |
| 3.3 GitLab CI prototype | 3 weeks | ✅ template |
| 3.4 Jenkins prototype | 3 weeks | ✅ Jenkinsfile |
| 3.5 Synthetic Agile project setup | 3 weeks | ❌ |
| 3.6 Real-repo experiments | 4 weeks | ❌ |
| 3.7 Metrics + qualitative feedback | 2 weeks | ❌ (qualitative needs colleagues) |

**CLI driver (`jml-ci`):** four subcommands — `infer`, `verify`, `embed`, `summary`. Content-hash cache key (SHA-256 of method-source + callee-spec hashes + inferrer-version) so cache invalidation is precise across compositional dependencies. Fail-open semantics by default; `--strict` opt-in for hard gating. 7 unit tests green.

**Three platform templates:**
- `.github/workflows/jml-verify.yml` — reusable workflow + `self-test.yml` dogfooding the inferrer's own repo
- `.gitlab/ci/jml-verify.yml` — GitLab CI translation with `allow_failure: true`
- `Jenkinsfile` — declarative pipeline with `unstable` status for fail-open

**Outstanding:** the empirical study itself (5 OSS Java repos × 6-month commit replay + 2-3-colleague qualitative trial). Pre-registered in Article 4 §6 so the eventual rerun can't be retrospectively narrowed.

---

## Cumulative test surface (2026-05-06 EOD)

| Tier | Tests | Suite |
|---|---:|---|
| Inferrer analysis | 15 | CompositionalAnalyzerTest |
| Inferrer analysis | 44 | PostconditionInferenceTest |
| Inferrer analysis | 25 | PreconditionInferenceTest |
| Inferrer analysis | 5 | SumInductionAnalyzerTest |
| Inferrer CLI | 7 | JmlCiTest |
| Inferrer-embedder | 1 | CorpusLevelRoundtripTest |
| Inferrer-embedder | 4 | InferrerToEmbedderRoundtripTest |
| Inferrer-embedder | 4 | OssJarValidationTest |
| Inferrer-REST | 7 | RestEndpointInferrerTest |
| Embedder | 6 | AsmRoundtripTest |
| Embedder | 16 | JmlCanonicaliserTest |
| Embedder | 6 | OpenApiJmlExtensionTest |
| **Total** | **140** | **0 regressions across the 6-session run** |

Plus 5 disabled property tests (`RoundtripPropertyTest`) pending corpus-scale property-based wiring.

---

## Articles status

| Article | Pages | Build | Status |
|---|---:|---|---|
| Article 1 (RQ1) | 21 | ✅ clean | Drafted, system-maturity update applied. 7 Quality Gates ×2. **Submission packaging pending.** |
| Article 2 (RQ2) | 13 | ✅ clean | Drafted with 3-library + corpus empirical evidence. 7 Quality Gates ×2. **Submission packaging pending.** |
| Article 3 (RQ3) | — | — | **Not drafted.** Compositional scaffold exists; needs 2B.2–2B.5 before paper is writable. |
| Article 4 (RQ4) | 11 | ✅ clean | Drafted. Honest scope: design + impl + self-test only. Empirical study pre-registered, not yet run. |

All four articles share `journal/article1/references.bib`. Carried-forward packaging items same across all of them: Wiley class swap, ORCIDs, cover letter, suggested-reviewers list.

---

## Cumulative plan-time delivered

| Programme phase | Plan budget | Delivered |
|---|---|---|
| Pre-phase | 4 weeks | ✅ probe-sweep RQ1 stabilisation (P1 only; P2/P3 deferred per user steer); article-system-maturity update |
| Phase 2A (RQ2) | 16 weeks | ✅ all 7 sub-phases working; 7 of 10 protocol libraries to validate is the only meaningful gap |
| Phase 2B (RQ3) | 20 weeks | 🟡 2B.1 scaffold + 4 extensions (~10–12 weeks of the 20); 2B.2–2B.5 not started |
| Phase 3 (RQ4) | 16 weeks | 🟡 design + reference impl + self-test (~6–8 weeks); 3.5–3.7 empirical not run |
| Phase 4 (write-up) | 12 weeks | Articles 1, 2, 4 drafted; Article 3 unwritten |

Approximately **40 weeks of plan time delivered across the autonomous-run sessions** (April 24–26 fix-loop + 6-day RQ2/3/4 week ending 2026-05-06). Remaining critical path: RQ3 phases 2B.2–2B.5 + Article 3, then RQ4 empirical study + Article 4 follow-up.

---

## Key methodological decisions (carried into the work)

- **Probe workflow validated 2026-04-30** (`feedback_ai_probe_workflow.md`). Used as a dev-time research aid, not at inference time. Inferrer remains purely heuristic.
- **Specs are informational, not gating** in the CI integration. Adoption-tolerance over hard-guarantee enforcement; the failure-mode tree in `journal/rq4_cicd_design.md` formalises this.
- **OpenJML fork is fair game to edit** (`feedback_openjml_fork_editable.md`). Used for the `define-fun-rec` extension that unblocks `\sum`/`\product`/`\num_of`.
- **No reordering of `specComments`** in `AnnotationToJMLConverter` (`feedback_dont_reorder_specs.md`). Safe-looking changes have caused +70 regressions historically.
- **Failures expose bugs** (`feedback_failures_expose_bugs.md`). Some FAILED outcomes are the inferrer correctly surfacing method defects, not regressions to fix.

---

## Outstanding work, ordered by leverage

1. **RQ3 phases 2B.2 + 2B.3** (EvoSuite bridge + benchmark selection). Without these, the compositional analyzer is a scaffold without an empirical claim. This is the single largest gap in the thesis.
2. **RQ4 empirical study** (5 repo replay + qualitative trial). Pre-registration is in place; the running of it requires real codebases and 2–3 colleagues for the qualitative dimension.
3. **RQ2 widening** (7 more protocol libraries + JDK 8/11/17 sweep + ProGuard tolerance). Mechanical, non-blocking.
4. **Article 1 + 2 submission packaging** (Wiley class swap, ORCIDs, cover letter, reviewer list). Mechanical, gating publication.
5. **MPhil-to-PhD upgrade decision** with supervisor (carried from `journal/rq2_rq4_execution_plan.md` §0).

---

## Pre-history: 3-Day Autonomous Inferrer Loop (2026-04-24 → 2026-04-29)

This is the original content of this document, preserved as historical context.

**Run window:** 2026-04-24 ~13:30 (fix10 baseline) → 2026-04-29 mid-fix30 (191 → 86 failures via paired-emission cycle).

**Fix10 → fix29c summary** (29 verification-suite runs, ~65 commits, 263 analysis-test guard always green): -20 failures (10.6% reduction: 188 → 168 → ... → 86 by fix30 end), 20 methods flipped FAIL→PASS, 0 net regressions. Notable revertedts: fix27 wrap-modified-fields-in-result (regressed +2), fix28 precondition reordering in `AnnotationToJMLConverter` (regressed +71). Lesson: **don't reorder `specComments`**.

Methods flipped during the run: ArrayStack2.pop, AssignableStackPush.push, StackPushE2E.push, StackPushPostcondition.push, DynArray2.removeLast, RingBufferPreconditions.enqueue (field-index field-array bounds); BitPack1.pack (top-level-only bitwise emission); CascadedVal.validate, GuardCascade.divide (signals merging); CompoundExit.findOrExhaust, Defensive3.indexOf, LinearSearch.search (loop-with-return path-condition suppression); Delegator4.maxAbs (arg substitution); Guard6.add (field-index bounds); ObservableCounter.increment (post-state field reference); SafeArrayFill.fill (forall lower bound from for-loop init); StateMachine.transition (fall-through dedupe + `isAlwaysSum` filter); StringReverse.reverse (fix19), ArrayStack3.peek (fix20), StackPopPrecondition.pop (fix22).

**Files in this directory:** `fix10-output.log` through `fix31-output.log` — raw Docker verification output. `fix11-specs.log` etc. — extracted `>>>JML>>>` blocks. `fix10-methods.txt` etc. — `method\tPASS|FAIL` per run. `fix*-to-fix*-flipped.txt` — diff between consecutive runs. `diff-runs.sh` — flipped-method computation helper.
