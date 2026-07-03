# RQ3 — Compositional Specification Inference: Design Notes

**Drafted:** 2026-05-06 (autonomous probe-sweep week, day 1)
**Status:** working draft — informs `CompositionalAnalyzer` implementation in October 2026
**Source plan:** `journal/rq2_rq4_execution_plan.md` §3

---

## 1. What the inferrer already does

`InterproceduralAnalyzer` propagates the callee's pre/postconditions into the caller's spec set:

- **Preconditions:** for each call site, look up the callee's cached spec; substitute formal parameters for actual arguments; add the substituted preconditions to the caller's set. (`InterproceduralAnalyzer.analyzeMethodCallPreconditions`, line 25.)
- **Postconditions:** symmetric path — substitute and add. (`analyzeMethodCallPostconditions`, line 228.)
- **Standard library:** `StandardLibrarySpecs` provides hardcoded specs for `String`, `Math`, `List`, `Map`, etc.; falls back to those when the AST-resolved callee has no inferred spec.

This is **not yet compositional**. It is a single-pass, propagation-only mechanism: the caller's spec gathers the callee's clauses verbatim. A genuinely compositional analysis computes the caller's spec by transforming its body **with the callee's spec substituted at the call site**, not by appending the callee's clauses to the caller's set.

The gap is what RQ3 must close.

---

## 2. The compositional algorithm in detail

Sketched in the execution plan §3.1 2B.1; expanded here.

### 2.1 Pass 1 — bottom-up isolated inference (existing)

Topologically sort methods by call graph; analyse each in dependency order. Mutual recursion: break the cycle with the existing isolated spec as a stub. Output: a `MethodSpecification` per method (the current `SpecificationCache` content).

### 2.2 Pass 2 — top-down compositional refinement (new)

For each method `m` in **reverse** topological order:

1. **Walk `m`'s body in WP fashion**, accumulating the weakest precondition required for each statement to satisfy `m`'s postcondition.
2. At each call site `n(args)`:
   - Substitute `args` for `n`'s formal parameters in `n`'s `requires`, `ensures`, and `assignable` clauses.
   - The WP-transformer at the call site is `R_n[args/params] ∧ (E_n[args/params] ⇒ WP_after)`, where `WP_after` is the WP of the rest of `m`'s body.
3. Lift through control-flow constructs (sequence, branch, loop, try/catch).
4. Output: `m`'s refined `requires` is `WP(m_body, m's existing ensures)`; `m`'s refined `ensures` is `SP(m_body, m's refined requires)`.

### 2.3 Implementation surface

A new analyzer `CompositionalAnalyzer` in `com.jml.inferrer.analysis`. Two-phase entrypoint:

```java
public class CompositionalAnalyzer {
    public CompositionalAnalyzer(SpecificationCache cache, CallGraph callGraph) { ... }
    public MethodSpecification refine(MethodDeclaration m, MethodSpecification isolatedSpec);
}
```

Called from `MethodSpecificationInferrer` after the bottom-up pass completes:

```java
// existing
for (MethodDeclaration m : sortedMethods) {
    MethodSpecification s = inferIsolated(m);
    cache.put(signature(m), s);
}
// new
for (MethodDeclaration m : sortedMethods.reversed()) {
    MethodSpecification refined = compositional.refine(m, cache.get(signature(m)));
    cache.put(signature(m), refined);
}
```

The reversed traversal in Pass 2 is critical: caller's WP depends on the callee's already-inferred isolated spec, not on the callee's refined spec. Pass 2 produces the refined spec but does not feed it back into other methods within the same pass — the algorithm is a single fixpoint iteration, not a chaotic relaxation.

### 2.4 Cycles

**Direct recursion:** the call graph self-edge is broken at Pass 1; Pass 2 sees the isolated spec at the recursive call site. The refined spec may differ; if so, an optional fixpoint loop iterates Pass 2 until specs stabilise. Bound iteration count to a small constant (5) and degrade gracefully — see §6.

**Mutual recursion:** Pass 1 breaks the strongly-connected component using the lexically-first method's isolated spec. Pass 2 sees that stub at every call site within the SCC. Fixpoint iteration applies as for direct recursion.

### 2.5 Polymorphic dispatch

A virtual call `obj.foo()` may dispatch to any method `foo` in any subclass of `obj`'s static type. The compositional analyzer must:

1. Resolve the static type of `obj`.
2. Find all methods in the class hierarchy that may be the dispatch target.
3. Compute the **disjunction** of their preconditions (any of the dispatch targets' preconditions are sufficient) and the **conjunction** of their postconditions (all dispatch targets' postconditions hold).

This is sound only if all subtypes' specs are known (closed-world assumption). For library-only callees with no embedded `@JmlSpec`, fall back to "uninterpreted callee" semantics (the existing approach).

### 2.6 Library calls

If the callee is a binary-only dependency, look up its spec via:

1. `StandardLibrarySpecs` (existing, hardcoded core JDK).
2. The Phase 2A `JmlSpecReader` (new, reads embedded `@JmlSpec` from the JAR's bytecode).
3. The Maven classifier sidecar (also Phase 2A).

If none yields a spec, treat the call as uninterpreted: the call may throw, may modify accessible heap, returns an unconstrained value. The existing inferrer already does this at the propagation step; the compositional pass inherits it.

---

## 3. Algorithmic risks (priority-ordered)

### 3.1 Houdini-style fixpoint blow-up *(plan risk register, medium)*

Iterating Pass 2 to a fixpoint can diverge on real code if the predicate language is too expressive (the verifier turns into a theorem prover). Mitigations:

- **Bounded iteration count:** cap at 5 iterations; emit the most recently stable spec. (Pre-empted by `feedback_propagation_focus.md` — the user has already flagged WP/SP propagation as the next focus area.)
- **Domain restriction:** restrict the transformer's predicate language to a fragment Z3 can decide quickly (linear arithmetic + uninterpreted functions + array theory). Reject clauses outside the fragment with a warning.
- **Per-method timeout:** budget 5 seconds of compositional refinement per method; degrade to isolated spec on timeout.

### 3.2 Non-termination on indirect recursion through library callees

A call into the JDK that itself calls back into user code (`Comparator.compare`, `Iterable.iterator`) introduces a cycle the call graph builder doesn't see. Mitigations:

- Treat all library callees as cycle endpoints: do not transform through them.
- Document this as a known limit; verifier-side OpenJML invocations will fall back on the user-provided JDK specs from `StandardLibrarySpecs`.

### 3.3 Branch explosion with conditional postconditions

Existing `\result == ... ==> ...` clauses (`PostconditionAnalyzer.analyzeBranchConditionalReturns`) can multiply through call sites. A method with five branches that each call a method with five conditional postconditions yields 25 clauses pre-simplification. Mitigations:

- Algebraic simplification (the current SymbolicExecutor path-condition simplifier) before emission.
- Cap on conditional postcondition count per method (default 8); spill to a single guarded `\true` clause beyond the cap.

### 3.4 Side-effecting argument expressions

A call `f(p++)` is unsound to treat as `f(p)` since the argument has a side effect. Mitigations:

- Detect side-effecting argument expressions (UnaryExpr `++`/`--`, AssignExpr, MethodCallExpr to non-pure callees).
- Before propagating the callee's spec, substitute a fresh ghost variable for the side-effecting argument and emit a `\let` binding in the propagated clause.
- If the inferred fragment doesn't support `\let`, emit a class-level invariant capturing the side effect's net change and refer to it in the propagated postcondition.

### 3.5 Aliasing through shared receiver

`a.f(); b.g();` where `a == b` — the postcondition of `a.f()` constrains `b`'s state too. The compositional analyzer can soundly ignore this only if it tracks aliasing. Mitigations:

- Default: assume no aliasing. Document as a known limit.
- Optional: a lightweight intra-procedural alias analysis (escape analysis without inheritance) — defer until the experimental results show aliasing-sensitive bugs.

### 3.6 Non-terminating callees

The compositional WP transformer is sound only if the callee terminates. Without a termination proof, the postcondition `E_n` is conditional on termination. Mitigations:

- Carry an implicit `terminates` flag per spec; clauses that depend on the postcondition are propagated only if the callee is marked terminating.
- The existing `loop_decreases` heuristic can populate the flag for simple loop methods; recursive methods need a `decreases` heuristic that the inferrer doesn't yet emit.

---

## 4. Verification benchmark design

The plan §3.1 2B.4 mandates a mutation-testing comparison across three configurations:

(a) tests generated from code only,
(b) tests from code + isolated specs (current inferrer),
(c) tests from code + compositional specs (new).

The hypothesis is that (c) > (b) > (a) on mutation score. The decision criterion is mutation-score improvement ≥5pp with `p < 0.05` and Cliff's delta ≥0.15.

Recommendations not in the plan:

1. **Add a fourth configuration (d):** tests from code + compositional specs **with the OpenJML discharge filter**. If a clause is propagated but OpenJML cannot discharge it, drop the clause from the test-generation prompt. This filters out specs that compose syntactically but are semantically unsound; the empirical question is whether this filter improves test quality further.

2. **Add a fifth configuration (e):** tests from code + compositional specs **plus the `@JmlSpec` annotations on library callees** (i.e., RQ2's embedding mechanism in use). This isolates the contribution of Phase 2A's embedding to test-generation effectiveness.

3. **Stratified sampling.** Defects4J spans multiple project sizes and bug categories. A flat sampling of 30 bugs per project may dilute the comparison. Stratify by bug category (off-by-one, null dereference, exception handling, ...) and report effect sizes per stratum. The aggregate may hide a mixed signal that the per-stratum analysis would surface.

4. **Pre-registration.** The decision criteria (≥5pp, p<0.05, delta≥0.15) should be pre-registered before the experiment runs. Reviewer 2 will ask whether the criteria were chosen post-hoc to support the conclusion. A simple GitHub Issue or OSF registration before kicking off the experiment satisfies the standard.

---

## 5. Test-generator integration: EvoSuite vs Randoop

The plan recommends starting with EvoSuite. Two practical concerns the plan does not foreground:

### 5.1 EvoSuite's contract injection format

EvoSuite passes preconditions to its mutation operators via `Assume.assumeThat(...)` or `@Contract` annotations (which it generates from JML if given the right input format). The integration point is a single `JmlOracleTransformer` that translates a `MethodSpecification` to either:

- An EvoSuite `--criterion` extension (a custom criterion class implementing `org.evosuite.coverage.TestFitnessFunction`).
- A `@JmlContract` annotation on the SUT class that EvoSuite's reflection layer reads pre-generation.

Recommendation: implement the `--criterion` extension first. Custom criteria are first-class in EvoSuite's documentation and avoid the annotation processor's quirks.

### 5.2 Randoop fallback

Randoop's contract checking is documented but not as actively maintained. The plan correctly flags this as a backup. Practical heads-up: Randoop's contract API changed at some point in the 4.x line; pin to a specific Randoop version (4.3.x as of writing) and document the version in the bridge module.

### 5.3 Custom symbolic execution (JBSE)

The plan rates this as a tertiary fallback. Two reasons it is unlikely to be the right primary path: JBSE is research-grade and slow on real Java code; the inferrer's own tests already use OpenJML's symbolic engine, so doubling up adds little marginal capability. Recommendation: explicitly de-scope JBSE unless EvoSuite *and* Randoop both prove insufficient, which would itself be a finding worth reporting.

---

## 6. Performance budget

The plan does not specify per-method analysis time for the compositional pass. Operating constraint: the inferrer's current 88 ms/file should not regress by more than 2× on Article 1 corpus.

Cost model for Pass 2 per method:

- WP-transformer walk: O(statements × predicate-size). Predicate size is bounded by the canonical-form size of the propagated clauses.
- Call site lookup: O(1) per call (cached spec). Number of call sites per method: ~3 (median across Article 1 corpus, per inferred specs in `inferred-specs.log`).
- Per-method total: O(statements × predicate-size × 3).

Realistic budget: 100 ms/method on a typical Article 1 method. Fixpoint iteration multiplies by the cap (5×), giving 500 ms in the worst case. To stay within the 2× regression bound, fixpoint iteration must be enabled selectively — e.g., only on methods whose isolated spec exhibits a recursive pattern.

Implementation guidance: profile aggressively in the first week. If 100 ms/method holds, fixpoint iteration is affordable everywhere; if not, restrict it.

---

## 7. Open items

1. **Predicate language fragment.** Pin to "linear arithmetic + arrays + uninterpreted functions" before implementation. The existing inferrer's predicate emissions already fit this fragment in practice; document the fragment formally so the compositional algorithm has a fixed target.

2. **Termination tracking.** Decide whether to lift the implicit termination assumption into an explicit `decreases` clause kind, or to track termination outside the spec. Recommendation: outside the spec — a per-method boolean in the cache. Termination proofs are a separate concern and shouldn't pollute the propagated clauses.

3. **Fixpoint convergence criterion.** Two specs converge when their canonical forms are equal. The Phase 2A `JmlCanonicaliser` is the natural tool. Sequence the dependency: Phase 2A.2 design doc must precede the compositional implementation by enough time that the canonicaliser is stable.

4. **Cycle detection in the call graph.** Existing `CallGraphBuilder` does not expose strongly-connected components. Add `CallGraph.scc()` returning `List<Set<MethodSignature>>` so the compositional analyzer can treat each SCC as an atomic unit for the stub-and-iterate dance.

5. **What to do when refinement worsens the spec.** A composed clause may be syntactically smaller (good) or it may be syntactically larger (worse for the LLM consumer in RQ1). Decide a tiebreaker: take the syntactically smaller of `isolated` and `refined`, breaking ties by preferring `refined`. This is a heuristic; the alternative is to leave both and let downstream consumers pick.

---

## 8. Sequencing dependencies

```
Phase 2A.2 (canonicaliser)  ─┐
                             ├─→ Phase 2B.1 (compositional algorithm)  ─→ Phase 2B.2 (test generator)
Phase 2A.4 (extractor)       ─┘                                          ─→ Phase 2B.4 (mutation testing)
```

The compositional algorithm depends on:
- A canonical form (Phase 2A.2 design doc — drafted today).
- The library extractor (Phase 2A.4) for non-source callees.

Both Phase 2A artefacts feed RQ3. Slipping Phase 2A by more than four weeks slips RQ3 by the same.
