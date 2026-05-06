# RQ2–RQ4 Execution Plan

**Author:** Brendan Edmonds (with Claude as engineering / drafting collaborator)
**Date drafted:** 2026-04-30
**Target submission:** 2027 Q3 (per confirmation report Gantt chart)
**Status:** draft for review

This plan operationalises the three remaining research questions from the confirmation report into a concrete, dated, milestone-driven schedule. Each phase has sub-tasks, deliverables, a Claude-vs-user task split, a decision point, and a risk register. Where the report's schedule is in tension with realistic effort estimates, the tension is flagged.

---

## 0. Schedule overview

| Phase | Dates | Duration | Focus | Output |
|---|---|---|---|---|
| **Pre-phase** | May 2026 | 4 weeks | Stabilise RQ1 prototype, ship Article 1, panel feedback follow-up | Inferrer at <5% verification-failure rate; Article 1 submitted; confirmation feedback addressed |
| **Phase 2A — RQ2** | Jun–Sep 2026 | 4 months | Spec embedding in Java bytecode + REST APIs | Bytecode embedder/extractor; OpenAPI extension; empirical validation; **paper draft (Article 2)** |
| **Phase 2B — RQ3** | Oct 2026–Feb 2027 | 5 months | Compositional WP/SP inference + test generation | `CompositionalAnalyzer`; EvoSuite/Randoop integration; mutation-testing study; **paper draft (Article 3)** |
| **Phase 3 — RQ4** | Mar–Jun 2027 | 4 months | CI/CD integration | GitHub Actions / GitLab CI / Jenkins pipelines; synthetic + real-repo experiments; **paper draft (Article 4)** |
| **Phase 4 — Writeup** | Jul–Sep 2027 | 3 months | Thesis assembly, viva prep | Final thesis; revised papers; replication package |

Total: 17 months → submission Q3 2027.

This compresses the report's Gantt by ~3 months (the report's "Phase 2" and "Phase 3" both run longer). The compression is achievable **only** if (a) Article 1 is genuinely submitted by end of May 2026 — not in revision indefinitely — and (b) Phase 2A and 2B do not stack delays. Realistic contingency: assume one slip of ~2 months somewhere; submission falls to Q4 2027.

### MPhil-vs-PhD note

The confirmation report is for MPhil. Three observations:

1. **The schedule is PhD-length** (3.5 years). UQ MPhil is typically 1.5–2 years full-time.
2. **The four-RQ scope is PhD-shaped.** A typical MPhil delivers RQ1 plus light coverage of one of RQ2–4.
3. **At confirmation, raise upgrade-to-PhD with the supervisor.** The work in this plan, if executed, is a PhD by publication: four papers (RQ1 + RQ2 + RQ3 + RQ4) plus a unifying thesis.

This plan is written assuming PhD upgrade. If MPhil is held, scope down to RQ1 + RQ2 (drop RQ3, RQ4) and target submission Q1 2027.

---

## 1. Pre-phase (May 2026)

**Goal:** clear the runway. Phase 2A starts on solid ground.

### 1.1 Sub-tasks

| Task | Effort | Owner | Deliverable |
|---|---|---|---|
| Run AI probe-workflow sweep across all failing verification tests (per `project_2026_05_01_probe_sweep.md`) | 1 week | Claude + user | Inferrer at <5% verification-failure rate (baseline 86 → target ≤40) |
| Submit Article 1 to target venue (JSEP / TOSEM / ASE journal) | 1 week | User (Claude drafts revisions) | Submission confirmation |
| Address confirmation panel feedback | 1 week | User | Updated proposal / scope refinement |
| Set up GitHub project for tracking RQ2–4 milestones | 1 day | Claude | Project board with this plan's milestones |

### 1.2 Decision point

End of May 2026: is the inferrer stable enough to be the foundation for RQ2's embedding work? Concretely: does it emit consistent JML across repeated runs on the same source? If not, fix that before RQ2 starts (RQ2 depends on roundtrip determinism).

---

## 2. Phase 2A — RQ2: Spec embedding in compiled artifacts and REST APIs (Jun–Sep 2026)

**RQ2 (verbatim):** Is it feasible to represent and distribute formal specifications in compiled or interface-only environments, such as Java libraries or RESTful APIs, where source code is unavailable?

### 2.1 Sub-task breakdown

#### 2A.1 Survey existing embedding mechanisms (2 weeks, June W1–W2)

- Java bytecode annotations (`RuntimeVisibleAnnotations` attribute, ASM `AnnotationVisitor`)
- Class-file attributes (custom attributes per JVMS §4.7)
- JML stub/specification files (`.jml`, `.refines-jml`)
- OpenAPI / Swagger extensions (`x-*` properties)
- Pact / consumer-driven contract testing
- Java records and sealed types as carriers
- Maven/Gradle artifact metadata

**Deliverable:** comparison table — expressiveness, tooling support, byte overhead, JVM compatibility, stability across compilers.

**Owner:** Claude (research + table) → user reviews and chooses primary candidate.

#### 2A.2 Design the bytecode embedding format (2 weeks, June W3–W4)

Two viable designs to evaluate:

**Design A — Annotation carrier.** Define a `@JmlSpec` runtime annotation type with string-valued elements (`requires`, `ensures`, `assignable`, `loop_invariant`). One annotation per method. JML preserved verbatim in strings.

- Pros: standard JVM mechanism, IDE-friendly, reflection-readable.
- Cons: string parsing required at consumption, no semantic check at the JVM level.

**Design B — Class attribute carrier.** Define a custom class-file attribute `JmlContract` (per JVMS §4.7.1) holding a structured binary encoding of JML clauses.

- Pros: smaller bytecode, no annotation pollution.
- Cons: invisible to standard reflection, requires custom reader, IDEs don't surface it.

**Recommendation:** Design A first (annotations), Design B as future optimisation. Annotation-based aligns with how Spring, Lombok, JUnit ship metadata and is the path of least resistance.

**Deliverable:** specification document (8–12 pages) + skeleton Java module `jml-embedding-spec/` with the `@JmlSpec` type.

**Owner:** Claude drafts, user reviews and approves.

#### 2A.3 Implement bytecode embedder (3 weeks, July W1–W3)

- New module `jml-embedder/` with ASM dependency.
- Tool: `JmlEmbedder.embed(input.jar, output.jar, MethodSpecification[])` — transforms each `.class` file by attaching `@JmlSpec` annotations to methods.
- Roundtrip property: `extract(embed(jar, specs)) == specs` (verified by a JUnit suite).
- Configuration: opt-out per method, opt-in per class.

**Deliverable:** `jml-embedder` Maven module, ≥30 unit tests, integration test on a non-trivial JAR.

**Owner:** Claude implements, user reviews architecture decisions.

#### 2A.4 Implement bytecode extractor / spec reader (2 weeks, July W4–Aug W1)

- New module `jml-extractor/` (or part of `jml-embedder`).
- Tool: `JmlExtractor.extract(jar) → Map<MethodSig, MethodSpecification>`.
- Plug into existing inference engine: when a callee is a binary-only dependency, the inferrer reads its embedded spec instead of re-inferring.

**Deliverable:** working extractor + integration with `MethodSpecificationInferrer`'s callee-spec lookup.

**Owner:** Claude.

#### 2A.5 Design REST API spec format (2 weeks, Aug W2–W3)

- Extension to OpenAPI 3.x: per-operation properties `x-jml-requires`, `x-jml-ensures`, `x-jml-assignable`.
- Or alternative: separate sidecar JSON (`<service>.contract.json`) with an explicit JSON Schema.
- Decide between the two based on tooling momentum (openapi-generator extensions vs. greenfield).

**Recommendation:** OpenAPI extension — it inherits the existing tooling ecosystem.

**Deliverable:** JSON Schema for the OpenAPI extension + design doc.

**Owner:** Claude drafts, user reviews.

#### 2A.6 Implement REST API spec embedder/extractor (3 weeks, Aug W4–Sep W2)

- Reads Spring `@RestController` / JAX-RS endpoints, runs the inference engine on each handler, produces an extended OpenAPI document.
- Reverse: given an extended OpenAPI document, reconstruct `MethodSpecification` for each endpoint so a downstream consumer (verifier, test generator) can use them.
- Smoke-test against ≥3 Spring Boot example services.

**Deliverable:** `jml-openapi/` module + working pipeline against 3 sample services.

**Owner:** Claude.

#### 2A.7 Empirical validation (4 weeks, Sep W3–Oct W2)

**Bytecode side:**
- Apply the embedder to ≥10 open-source Java libraries (Apache Commons Lang/IO, Guava `core`, jOOL, Vavr, jsoup, JFreeChart, etc.).
- Measure: bytecode size overhead (%), embedding/extraction throughput (methods/sec), spec roundtrip fidelity (% of inferred specs preserved exactly).
- Negative-test: load a `@JmlSpec`-annotated class in a JVM that doesn't know the annotation type, confirm no startup failure.

**REST side:**
- Apply to ≥5 mock microservices (build these from public Spring Boot tutorials + the user's own scaffolding).
- Measure: OpenAPI document size overhead, generator/parser interop with `openapi-generator`, roundtrip fidelity.

**Deliverable:** experiment report + raw data + statistical summary.

**Owner:** Claude runs experiments, user inspects and approves results.

### 2.2 Decision point (end of September 2026)

Did embedding work robustly on real-world libraries? Specifically:

- Roundtrip fidelity ≥95% on ≥8 of 10 libraries → **proceed to Phase 2B**.
- Roundtrip fidelity <80%, or systematic failure on common patterns (generics, inner classes, lambdas) → **stop, fix, re-evaluate timeline**. Likely overrun is 1–2 months.

### 2.3 Deliverable: Article 2 draft

Title (working): *Embedding Inferred JML Contracts in Java Bytecode and OpenAPI Specifications.*

Target venue: ICSME (tools) or TOSEM (full paper).

Sections: motivation; survey; format design; embedder/extractor implementation; OpenAPI extension; empirical validation; threats; related work; conclusion.

Length: ~10 pages conference / ~25 pages journal.

**Owner:** Claude drafts, user revises.

### 2.4 Risks

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| ASM/bytecode complexity larger than estimated (generics erasure, inner classes, lambda metafactory) | Medium | 3–4 week slip | Start with simple shapes; descope to top-level class bodies first; iterate |
| OpenAPI extension rejected by downstream tooling | Low | Reframe as sidecar | Sidecar fallback design ready in 2A.5 |
| Roundtrip fidelity poor due to JML expression complexity (e.g., `\sum`, `\forall`) | Medium | Spec-string-mangling bug risk | Build a JML-aware printer first; assert exact-string equality on canonical forms |
| Annotation-retention semantics conflict with `class` retention vs `runtime` retention | Low | Design rework | Test both retentions in 2A.3 |

---

## 3. Phase 2B — RQ3: Compositional inference + test generation (Oct 2026–Feb 2027)

**RQ3 (verbatim):** To what extent does compositional specification inference improve automated unit test generation and coverage in distributed systems?

### 3.1 Sub-task breakdown

#### 2B.1 Compositional WP/SP inference algorithm (10 weeks, Oct–Dec 2026) — **the hardest task in the plan**

The current inferrer infers each method's spec in isolation. Compositional inference means: when method `m` calls method `n`, the spec inferred for `m` should incorporate `n`'s spec via weakest-precondition propagation.

**Algorithm sketch:**

1. Topologically sort methods by call graph (caller depends on callee).
2. For each callee `n` with inferred spec `(R_n, E_n, A_n)` (requires/ensures/assignable):
   - The caller `m`'s WP at the call site `n(args)` is `R_n[args/params] ∧ (E_n[args/params] ⇒ WP_after)`.
3. Lift this through `m`'s control flow (sequence, branch, loop, exception).
4. Result: `m`'s requires becomes `WP(m_body, true)`, `m`'s ensures becomes `SP(m_body, m's requires)`.

**Implementation:**

- New analyzer `CompositionalAnalyzer` extending `MethodSpecificationInferrer`.
- Two-pass: pass 1 = bottom-up isolated inference (existing); pass 2 = top-down composition refinement.
- Cycle handling (mutual recursion): use the already-inferred isolated spec as a "stub" and don't re-compose.
- For binary callees: read embedded JML via the `JmlExtractor` from Phase 2A.

**Verification:** for ≥30 multi-method methods, OpenJML must accept the composed spec where it currently rejects the isolated one (or accepts it more efficiently).

**Deliverable:** `CompositionalAnalyzer` shipped; analysis tests; verification tests; performance benchmark vs. isolated inference.

**Owner:** Claude implements; user supplies test cases that expose corner cases.

#### 2B.2 Test generation engine integration (4 weeks, Jan W1–W4)

**Three candidate engines, evaluate in this order:**

1. **EvoSuite (search-based).** Pass inferred preconditions as `org.evosuite.runtime.Assume.assumeThat(...)` filters; pass postconditions as JUnit 5 assertions in a custom `JmlOracle`. Use EvoSuite's `--criterion` flag plus a custom criterion that rewards postcondition coverage.
2. **Randoop (feedback-directed random).** Add inferred specs as `@CheckRep` and contract checks. Easier integration but smaller empirical literature.
3. **Custom symbolic (JBSE-based).** Drive JBSE with the inferred precondition as the path filter, postcondition as the assert. Only if 1 and 2 prove insufficient.

**Recommendation:** start with EvoSuite — strongest empirical literature, active maintenance, test-suite-quality measures already wired in.

**Deliverable:** `jml-evosuite-bridge/` module; pipeline `Java source → JmlInferrer → EvoSuite → JUnit suite with JML oracles`; smoke-test on the same Java Core Library subset used in RQ1.

**Owner:** Claude.

#### 2B.3 Benchmark selection (3 weeks, Jan W4–Feb W2)

**Three benchmark suites:**

1. **Defects4J (real bugs).** 800+ real-bug-introduce/fix pairs across 17 Java projects. Measure: % of bugs surfaced by tests generated from inferred-and-composed specs vs. tests generated without specs vs. EvoSuite default.
2. **Java Core Library subset (continuity with RQ1).** Use the same classes as Article 1 to enable direct comparison.
3. **Synthetic microservice systems.** Build 5 mock services with **known** inter-component contracts (e.g., Order Service ⇄ Inventory Service ⇄ Payment Service). Inject seeded contract violations; measure detection rate.

**Deliverable:** benchmark pack + reproducibility scripts.

**Owner:** Claude builds synthetic systems; user curates Defects4J subset.

#### 2B.4 Mutation testing pipeline (2 weeks, Feb W3–W4)

- PIT (already used in RQ1).
- Three configurations: (a) tests generated from code only, (b) tests from code + isolated inferred specs, (c) tests from code + compositionally inferred specs.
- Metrics: branch coverage, line coverage, mutation score, fault-detection rate (real bugs from Defects4J), redundancy.

**Deliverable:** mutation report + comparative table.

**Owner:** Claude runs, user inspects.

#### 2B.5 Statistical analysis (1 week, Feb W4)

- Paired non-parametric tests (Wilcoxon signed-rank or Mann-Whitney U) for mutation-score differences.
- Effect sizes: Cliff's delta or Vargha-Delaney Â₁₂.
- Multiple-comparisons correction (Bonferroni or Benjamini-Hochberg).
- Power analysis posterior.

**Deliverable:** `analysis.R` or `analysis.py` + statistical summary.

**Owner:** Claude.

### 3.2 Decision point (end of February 2027)

Does the compositional inference *measurably* improve test-generation effectiveness over isolated inference?

- Mutation-score improvement ≥5pp with `p < 0.05` and effect size at least small (Cliff's delta ≥0.15) → **proceed to Phase 3** with confidence.
- Improvement <2pp or not statistically significant → **investigate first** (could be benchmark choice, could be algorithm gap, could be a real null result that itself is publishable). Likely impact on schedule: 1–2 month investigation before continuing.

### 3.3 Deliverable: Article 3 draft

Title (working): *Compositional Specification Inference for Spec-Driven Test Generation in Java Microservices.*

Target venue: ICSE (full paper) or ESEC/FSE.

Length: ~12 pages conference.

**Owner:** Claude drafts, user revises.

### 3.4 Risks

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Compositional WP/SP algorithm runs into Houdini-style fixpoint blow-up on real code | Medium | 1–2 month overrun | Bound iterations; cache per-method composed specs; degrade gracefully to isolated inference |
| EvoSuite oracle integration unstable (it's an active research tool) | Medium | Switch to Randoop | Have Randoop fallback ready by Jan 2027 |
| Defects4J results show *no* improvement or *negative* improvement (composed specs over-constrain test inputs and reduce diversity) | Medium | Reframe as null result + analysis | This is itself publishable; pivot framing rather than scope |
| Synthetic microservice benchmark seen as toy | High | Reviewer-2 ammunition | Augment with at least one real microservice trace (e.g. open-source Spring PetClinic Reactive), document realistic limitations |

---

## 4. Phase 3 — RQ4: CI/CD integration (Mar–Jun 2027)

**RQ4 (verbatim):** How can formal methods, particularly specification inference and verification, be integrated into Agile software development workflows without introducing significant overhead or workflow disruption?

### 4.1 Sub-task breakdown

#### 3.1 Reference Agile workflow design (3 weeks, Mar W1–W3)

Document a reference workflow combining:

- Trunk-based development with short-lived feature branches
- Pull-request reviews
- Automated build + test + verification pipeline
- Spec inference at three trigger points: per-commit (incremental), per-PR (full diff), per-merge (release-candidate)
- Cache strategy: don't re-infer methods whose AST hasn't changed (content-hash keyed)
- Failure handling: spec inference timeout → degrade to existing tests, don't block the merge

**Deliverable:** workflow specification doc + diagram + decision tree for failure modes.

**Owner:** Claude drafts, user reviews.

#### 3.2 GitHub Actions prototype (4 weeks, Mar W4–Apr W3)

- Reusable workflow (`uses: jml-inferrer/.github/workflows/verify.yml@v1`).
- Action 1: `jml-infer` — runs the inferrer on changed files.
- Action 2: `jml-verify` — runs OpenJML on inferred specs.
- Action 3: `jml-test-gen` — emits a JUnit suite via EvoSuite + inferred specs.
- Action 4: `jml-pr-comment` — posts spec/verification status to the PR as a comment.
- Caching: GitHub Actions cache action keyed on the AST hash of touched methods.

**Deliverable:** GitHub Actions repository + working demo on a test repo.

**Owner:** Claude.

#### 3.3 GitLab CI prototype (3 weeks, Apr W4–May W2)

Adapt the GitHub Actions pipeline to GitLab. Use Merge Request pipelines, GitLab cache, and the GitLab-specific MR-comment API.

**Deliverable:** `.gitlab-ci.yml` template + demo project.

**Owner:** Claude.

#### 3.4 Jenkins prototype (3 weeks, May W3–Jun W1)

Declarative-pipeline `Jenkinsfile` plus a small Jenkins shared library wrapping the inferrer/verifier/test-gen stages.

**Deliverable:** `Jenkinsfile` + shared library + demo.

**Owner:** Claude.

#### 3.5 Synthetic Agile project setup (3 weeks, Jun W1–W3, parallel with 3.4)

- Build 3 synthetic projects, each with 6 simulated sprints of commits.
- Spec churn: each sprint adds/removes/refactors ≥10% of methods.
- Multiple-developer pattern: alternate authors, occasional merge conflicts.

**Deliverable:** 3 GitHub repositories with full commit history simulating 6 sprints each.

**Owner:** Claude.

#### 3.6 Real-repo experiments (4 weeks, Jun W4–Jul W3) — **schedule slip into Phase 4**

- Pick 5 active open-source Java repos with mature CI (Apache Commons Lang, jOOL, Caffeine, Vavr, Resilience4j).
- Replay last 6 months of commits through the inferrer pipeline.
- Measure: cumulative pipeline time, frequency of inferred-spec changes per commit, churn (spec-line-add/remove/modify counts), build-time overhead (with vs. without inferrer).

**Deliverable:** experiment report + raw data + statistical summary.

**Owner:** Claude runs, user spot-checks results.

#### 3.7 Metrics and analysis (2 weeks, Jul W4–Aug W1)

Metrics from the report's RQ4 spec:

- Pipeline performance overhead (median/p95/p99 build-time delta)
- Frequency and size of inferred spec changes (per commit, per sprint)
- Stability and maintainability of verification artefacts over multiple sprints
- Ease of integration (lines of YAML/Jenkinsfile required, comparison across CIs)

Plus a qualitative dimension: ergonomic feedback from developers (the user, plus 2–3 colleagues if available — *this is the only phase that benefits from real human input*).

**Deliverable:** RQ4 results section + comparison table across CIs.

**Owner:** Claude analyses, user gathers qualitative feedback.

### 4.2 Decision point (end of July 2027)

Does the integration meet the "minimal overhead" claim?

- p95 build-time overhead <30% on real repos → strong story.
- p95 build-time overhead 30–60% → defensible with caching argument.
- p95 build-time overhead >60% → re-architect inferrer for incremental analysis (1–2 month task) before submission.

### 4.3 Deliverable: Article 4 draft

Title (working): *Specification Inference in Continuous Integration: An Empirical Study of Overhead, Stability, and Adoption Friction.*

Target venue: ESEC/FSE Industrial Track, ICSE-SEIP, or empirical-software-engineering journal (EMSE).

**Owner:** Claude drafts, user revises.

### 4.4 Risks

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Build-time overhead too high to claim "minimal disruption" | Medium-High | Re-architect for incremental | Build content-hash cache early (3.1); profile aggressively |
| Real-repo experiments fail because target projects evolve | Low | Pin to specific commits | Document experimental setup with exact SHAs |
| Qualitative dimension thin (only the user's feedback) | High | Cite as a stated threat | Recruit ≥2 supervisor-network developers for a one-week trial; budget 2 weeks for this |
| GitHub/GitLab/Jenkins each demand idiosyncratic integration patterns | Medium | Schedule slip | Stop at GitHub Actions if time-constrained; document the others as design exercises |

---

## 5. Phase 4 — Final writeup (Jul–Sep 2027)

### 5.1 Sub-tasks

| Task | Effort | Owner |
|---|---|---|
| Thesis structure: introduction + 4 paper-chapters + unifying conclusion | Decide in Jun 2027 | User decides, Claude drafts |
| Chapter integration (cross-references, consistent notation) | 4 weeks | Claude |
| Replication package (Docker, scripts, datasets) | 3 weeks | Claude |
| External examiner suggestions | 1 week | User |
| Viva preparation (mock viva, anticipated questions) | 2 weeks | User + Claude as adversarial reviewer |
| Submission | 1 week | User |

### 5.2 Thesis structure proposal

```
Chapter 1: Introduction and motivation (10 pages)
Chapter 2: Background and literature review (40–50 pages, draws on the lit review just compiled)
Chapter 3: Heuristic AST-based JML inference (RQ1) — based on Article 1
Chapter 4: Embedding specs in compiled artefacts (RQ2) — based on Article 2
Chapter 5: Compositional inference and test generation (RQ3) — based on Article 3
Chapter 6: Specification inference in CI/CD (RQ4) — based on Article 4
Chapter 7: Synthesis and discussion (15–20 pages)
Chapter 8: Conclusion and future work (5–10 pages)
References + Appendices (replication, raw data tables)
Total: ~250 pages
```

---

## 6. Tools and infrastructure (set up in pre-phase)

| Tool | Purpose | Setup status |
|---|---|---|
| GitHub Actions on the inferrer repo | CI for the inferrer itself + canary for RQ4 patterns | Already exists |
| Docker Compose | Reproducible OpenJML runs | Already exists |
| GitHub Project board | Milestone tracking | New; create in pre-phase |
| LaTeX repository | Articles 1–4 + thesis | `journal/article1/` exists; add `article2/`, `article3/`, `article4/` |
| Replication-package template | Per-paper data + scripts | New; create in 2A |
| Statistical analysis (R or Python) | Mutation-testing comparisons, CI-overhead analysis | New |
| Defects4J | RQ3 benchmark | Install in 2B |
| EvoSuite | RQ3 test generation | Install in 2B |
| PIT | Mutation testing | Already used in RQ1 |

---

## 7. Claude-vs-user task split

| Activity | Claude | User |
|---|---|---|
| Algorithm design | Drafts and prototypes | Approves and provides domain insight |
| Implementation | Lead | Reviews architecture decisions |
| Empirical experiments | Runs, collects data | Inspects, sanity-checks results |
| Statistical analysis | Drafts | Confirms inference is sound |
| Paper drafting | Lead drafter | Lead reviser, intellectual framing |
| Literature positioning | Drafts | Confirms / re-frames |
| Decision points | Surfaces options + tradeoffs | Decides |
| Pivots and scope cuts | Suggests | Decides |
| Confirmation/viva defence | (Cannot help here) | Owns |
| AI-use disclosure | Drafts statement | Submits |
| Supervisor relationship | (Cannot help) | Owns |

The thesis-level intellectual contribution must remain the user's. Claude is a force multiplier on engineering and writing; the framing, judgment calls, and synthesis are not delegable.

---

## 8. AI-use disclosure (must not be skipped)

UQ has a policy on the use of AI tools in research outputs. Before any paper is submitted:

1. Confirm the current UQ policy at the time of submission.
2. Declare AI use in each paper's acknowledgements and methods sections.
3. Keep a log of significant AI-generated content in a private notebook (e.g. `journal/ai-use-log.md`) with dates, prompts, and what was used vs. what was discarded.
4. The intellectual contribution stays with the user; AI is acknowledged as a tool.

The current memory `feedback_ai_probe_workflow.md` covers dev-time use; that should be cited as the methodology when describing how the inferrer was *developed*, not when describing how the inferrer *operates*.

---

## 9. Decision points summary (for tracking)

| Date | Question | If yes | If no |
|---|---|---|---|
| End May 2026 | Inferrer roundtrip-deterministic on the same input? | Phase 2A | Stabilise first |
| End Sep 2026 | Bytecode embedding ≥95% fidelity on ≥8/10 libraries? | Phase 2B | Fix or descope |
| End Feb 2027 | Compositional ≥5pp mutation improvement, p<0.05? | Phase 3 | Investigate, possibly null-result paper |
| End Jul 2027 | RQ4 build overhead p95 <30% on real repos? | Submit | Re-architect for incremental |
| End Sep 2027 | Thesis ready for submission? | Submit | Three-month extension |

---

## 10. What to do this week (May 2026 W1)

1. **User:** raise the MPhil-to-PhD upgrade question with the supervisor at confirmation.
2. **User:** confirm Article 1's submission target venue (the lit review's Appendix B suggests JSEP/TOSEM).
3. **Claude:** kick off the AI probe-workflow sweep (already planned in `project_2026_05_01_probe_sweep.md`).
4. **Claude + user:** triage open issues / failing tests; aim for ≤40 verification failures by end of May.
5. **User:** decide whether this plan should be shared with the supervisor for input before Phase 2A starts.

This document is a living plan. Revise after each decision point.
