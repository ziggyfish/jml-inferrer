# Plan: Migrate JML-Inferrer to WP/SP-Based Inference

Status: **proposal — not started**. Estimated effort: 12–18 months (1 PhD-equivalent FTE) for full migration, or 3–5 months for the hybrid backend (Phase 1 only).

## Goal

Replace heuristic AST pattern matching with a sound weakest-precondition / strongest-postcondition (WP/SP) calculus backed by an SMT solver, while preserving:

1. The current public CLI surface (`java -jar jml-inferrer-...jar <path>`).
2. The OpenJML validation pipeline (it becomes a sanity check on encoding rather than the soundness oracle).
3. Backwards compatibility on emitted JML for the patterns the heuristic engine handles today.

## Strategic Choice: Hybrid First, Replace Later

The honest analysis is that a full WP/SP rewrite competes with KeY, OpenJML's own inference, Frama-C, Why3, Daikon, Houdini, and ICE-learning tools — most with decades of investment. Going hybrid first lets us:

- Get a publishable delta without rebuilding the world.
- Validate the SMT integration on a narrow scope before committing.
- Keep the existing inference engine running in production while the WP/SP layer matures.
- Decide whether full replacement is worth the cost based on real measurements.

The plan therefore proceeds in **four phases**, each independently shippable.

---

## Phase 0: Foundations (1 month)

Prerequisites that any WP/SP work needs.

### 0.1 Choose an SMT integration

- **Recommended:** [JavaSMT](https://github.com/sosy-lab/java-smt) over Z3 (proven, MIT, supports CVC5/MathSAT as alternatives).
- **Alternative:** call OpenJML's existing SMT layer through its API. Lower integration cost, but couples us to OpenJML's release cadence.
- **Decision criteria:** ability to run inside Docker without native-library hell; bitvector + array theories with reasonable timeouts.

### 0.2 Define the expression algebra

Today `SymbolicExpr` is a thin wrapper around JavaParser nodes. We need a closed algebra with:

- Substitution: `e[x ← e']`.
- Normal form: canonical ordering for commutative operators, constant folding.
- Equality and implication checks (delegated to SMT).
- Free-variable computation.

Implementation sketch: a sealed `Term` hierarchy in `com.jml.inferrer.formal.term` independent of JavaParser, with a translation layer `JavaParserToTerm`.

### 0.3 Memory model decision

The single most consequential design choice. Pick one:

- **Field-by-field heap with frame conditions.** Closest to JML's `assignable` semantics. Requires alias analysis or annotation-driven framing.
- **Dynamic frames (à la KeY).** Powerful, but adds a separate region-expression language to the surface JML.
- **Separation logic.** Conceptually cleanest for aliasing, but requires SL-aware SMT support (limited tooling in JavaSMT).

**Recommended:** field-by-field with `assignable \nothing` / `assignable this.f` inferred conservatively. We already infer `@Pure` and assignable clauses heuristically, so this matches our output language.

### 0.4 Java integer semantics

Pick one and document it:

- **Mathematical integers** with overflow checks emitted as side conditions. Easier to reason about; produces stronger specs.
- **Bitvectors** matching JLS two's-complement. Sound by construction; specs become uglier.

**Recommended:** mathematical integers with optional `--bv-arithmetic` flag. Matches OpenJML's default and current heuristic behaviour (we already gate `Math.abs` by return type for the same reason).

### 0.5 Deliverables

- `com.jml.inferrer.formal.term` — Term algebra + tests.
- `com.jml.inferrer.formal.smt` — SMT facade (Z3 backend behind an interface).
- `docs/FORMAL_SEMANTICS.md` — Memory model and arithmetic semantics frozen.
- One end-to-end smoke test: derive WP for a single straight-line method and discharge it through SMT.

---

## Phase 1: Hybrid Backend (3–5 months) — *publishable delta*

Keep the heuristic dispatcher; add an optional SMT-backed *strengthening pass* for selected pattern families. This is the path I'd actually recommend shipping first.

### 1.1 Identify high-value pattern families

Patterns where the heuristic guess is locally well-defined and SMT can sharpen it:

1. **Branch-conditional postconditions** (`SymbolicExecutor` already produces `cond ⇒ post`). SMT can:
   - Check whether path conditions are mutually exclusive (turn `cond ⇒ a` + `¬cond ⇒ b` into the disjunction `result == a ∨ result == b` only when justified).
   - Drop redundant guards.
   - Infer the *strongest* arithmetic postcondition, not just `result == e`.
2. **Accumulator loops.** Today we emit `0 <= i && i <= n` and a heuristic accumulator invariant. SMT can verify candidate invariants against a single iteration step (a la Houdini), strengthening or weakening as needed.
3. **Numeric range postconditions.** Replace `\result >= 0` heuristics with SMT-derived tightest interval bounds.
4. **Std-lib propagation.** Today `StandardLibrarySpecs` substitutes parameters textually; with SMT, we can compose summaries soundly across nested calls.

### 1.2 Architecture

Add a `Strengthener` interface, called *after* the heuristic analyzers run:

```
HeuristicSpec → Strengthener → ValidatedSpec → JML emission
```

Each `Strengthener` is opt-in via the AST node it triggers on. If SMT times out or fails, fall back to the heuristic spec (current behaviour).

Key files to add:
- `com.jml.inferrer.formal.strengthen.BranchConditionalStrengthener`
- `com.jml.inferrer.formal.strengthen.AccumulatorLoopStrengthener`
- `com.jml.inferrer.formal.strengthen.NumericRangeStrengthener`

CLI flag: `--formal-strengthen=<family,...>`, default off. When on, OpenJML pass rates should strictly improve (regression test gate).

### 1.3 Validation

- Add a `FormalStrengtheningVerificationTest` suite to the existing 237-test Docker pipeline.
- For each pattern family, prove on a fixed corpus that the strengthened spec OpenJML-verifies *and* is strictly stronger than the heuristic baseline.
- Measure: % of methods where strengthening produced a non-trivial improvement.

### 1.4 Publishable framing

"Hybrid heuristic + SMT-backed strengthening" is a clean delta against:
- Pure heuristic tools (Jdoctor, current JML-Inferrer) — we're stronger.
- Pure formal tools (KeY, OpenJML inference) — we're cheaper and broader-coverage.

This is the natural follow-up paper to the current article.

---

## Phase 2: WP/SP Core for Straight-Line Code (4–6 months)

Build a real WP/SP engine but only for code without loops or unannotated calls. This is the foundation for everything that follows.

### 2.1 Statement-level WP/SP rules

Implement the textbook rules over the `Term` algebra from Phase 0:

- Assignment: `WP(x := e, Q) = def(e) ∧ Q[x ← e]`
- Sequence: `WP(S1; S2, Q) = WP(S1, WP(S2, Q))`
- Conditional: `WP(if C then S1 else S2, Q) = (C ⇒ WP(S1, Q)) ∧ (¬C ⇒ WP(S2, Q))`
- Return: model as assignment to `\result`.
- Throw: `false` for normal-behaviour specs; tracked separately for `signals` clauses.
- Field assignment: respect the chosen memory model from Phase 0.3.

### 2.2 Definedness conditions

`def(e)` must capture:
- Null-dereference safety.
- Array-index bounds.
- Division by zero.
- Optionally (under `--bv-arithmetic`): overflow.

Each definedness condition contributes to the inferred precondition.

### 2.3 Inference loop

For each method:
1. Compute `Post_normal` = SP-derived postcondition over the body.
2. Compute `Pre_min` = WP of the body w.r.t. `Post_normal`.
3. Simplify both via SMT (entailment-based redundancy elimination).
4. Emit as JML, validate via OpenJML.

### 2.4 Scope limits

**In:** straight-line methods, conditionals (arbitrary nesting), recursion (treated as uninterpreted).
**Out:** loops, unannotated callees (Phase 3), exceptions (Phase 4), concurrency (out of scope).

### 2.5 Migration strategy

Add `--engine=formal|heuristic|hybrid` flag. Default remains `heuristic`. The formal engine fails fast on out-of-scope constructs, falling back to heuristic per-method. Measure coverage on the 312-method corpus; ship when ≥40% coverage with strictly-better specs on those methods.

---

## Phase 3: Procedure Summaries and Loops (4–6 months) — *the hard part*

### 3.1 Procedure summaries

Calls become `assume(callee.pre); havoc(callee.assignable); assume(callee.post)`.

Three cases:
- **Annotated callee:** use the JML contract directly.
- **Inferred callee:** use the previously-inferred spec (we already do bottom-up analysis order in `CodebaseProcessor`).
- **Unannotated, uninferred (e.g. third-party JAR):** havoc all heap, return unconstrained value. Document the soundness gap; offer `--assume-pure-stdlib` as an escape hatch.

### 3.2 Loop invariants

The core open problem. Three strategies, pursued in parallel:

1. **Houdini-style invariant inference** (cheapest). Generate candidate invariants from a template grammar (parameter relationships, accumulator patterns, monotonicity), check each against the loop step via SMT, retain only those that survive.
2. **ICE-learning** (more powerful). Drive an SMT-based learner with positive/negative/implication examples from concrete or symbolic execution.
3. **Inductive abductive reasoning** (most powerful, slowest). Compute the WP of the loop exit, weaken iteratively until inductive.

**Recommended starting point:** Houdini with the template grammar derived from current heuristic invariants. This makes the existing loop-invariant heuristics into a *template source*, not a final answer — a clean reuse of prior work.

### 3.3 Termination

WP analysis assumes termination. Either:
- Emit `decreases` clauses (JML supports them, OpenJML accepts them).
- Restrict to total-correctness only for loops with obvious ranking functions (counter loops); leave others as partial-correctness with a flag in output.

### 3.4 Validation

OpenJML can discharge loop invariants with `--esc-loop-induction`. Our existing 237-test pipeline extends naturally.

---

## Phase 4: Beyond Normal Behaviour (3–4 months)

Once Phases 1–3 are stable, optionally extend to:

- **Exceptional postconditions** (`signals` clauses).
- **Inheritance and dispatch** (subtype contracts via behavioural subtyping).
- **Class invariants** (inferred from constructor + mutator postconditions intersected over all reachable states).
- **Concurrency** (out of scope unless we adopt a concurrency-aware memory model — separate research).

---

## Risks and Open Questions

| Risk | Likelihood | Mitigation |
|---|---|---|
| SMT timeouts dominate runtime | High | Per-method timeout, fallback to heuristic, cache results |
| Java semantics rabbit hole (reflection, dynamic class loading) | High | Document explicitly out-of-scope; flag affected methods |
| Memory model choice locks out future work | Medium | Phase 0.3 freeze; revisit only if blocker emerges |
| Loop invariant inference fails in practice | Medium | Phase 3 has three parallel strategies; can ship with any one |
| Result is "yet another formal tool" without differentiation | Medium | Hybrid framing (Phase 1) is the differentiator; pure WP/SP only justifiable if it materially beats KeY/OpenJML on coverage |
| 12–18 month estimate is wrong | High | Phase 1 alone is publishable and useful; treat phases as independent ship vehicles |

## Decision Points

- **After Phase 0:** Is SMT integration tractable on real Apache Commons Lang code with acceptable per-method runtime (target: <2s/method)? If no, abandon.
- **After Phase 1:** Did hybrid strengthening produce a meaningful (>15pp) OpenJML pass-rate improvement? If yes, ship and publish; if no, the heuristic engine is already near-optimal and Phase 2+ is hard to justify.
- **After Phase 2:** Does the formal engine cover ≥40% of the corpus with strictly-better specs? If no, stay hybrid and stop.
- **After Phase 3:** Does loop-invariant inference work on ≥60% of looping methods? If no, fall back to heuristic invariants under the formal frame.

## What This Plan Does NOT Cover

- A literature review of competing tools (separate doc).
- A specific evaluation protocol for the resulting tool — the current article's Phase P1–P4 design transfers.
- Funding, supervision, or staffing decisions.
- Whether any of this is the right *research* direction vs. e.g. LLM-based spec inference or runtime-validated specs.

---

*Drafted to be picked up later. Not currently scheduled.*
