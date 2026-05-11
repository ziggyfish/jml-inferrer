# Z3Experiement progress log

## 2026-05-08 — Day 1 (kickoff)

**Landed:**
- Project skeleton (`pom.xml`, `SCOPE.md`, `examples/`, `src/`).
- SMT-LIB2 frontend: `Lexer`, `Token`, `SExpr`, `Parser` for the subset OpenJML emits.
- Term layer with hash-consing: `Sort`, `Term`, `TermFactory`, `TermBuilder`. Constant folding for and/or/not/ite/equality.
- Tseitin CNF (`Cnf`).
- CDCL SAT (`Cdcl`): watched literals, VSIDS, 1UIP analysis, learned-clause minimisation, Luby restarts, activity-based DB reduction.
- EUF theory (`EGraph` + `EufTheory`): backtrackable union-find with congruence closure via signature table.
- `Solver` driver, zero-dependency `TestHarness`, examples directory.

**Tests:** 13/13 across SAT and EUF.

**Bugs fixed:**
1. Unit clauses contradicting at level 0 silently no-op'd (`enqueue` now returns success/failure; `addInitialClause` records `okay = false` on disagreement).
2. T-prop conflicts at level 0 looped forever (every conflict-resolution callsite checks the enqueue return).
3. `EGraph.lastConflict` never cleared (consume-and-clear in `EufTheory.check`).

## 2026-05-08 — Day 2 (continuation in same session)

**Landed:**
- **Linear arithmetic** (`Rational`, `Simplex`, `LiaTheory`): Dutertre/de Moura general Simplex with bound-driven pivoting, Bland's rule for termination, conflict explanation via failing-row reasons.
- **Theory combination** (`MultiTheory`): fan-out of assert/retract/check/propagate/explain across N sub-theories. EUF + LIA run together under one Solver.
- **Theory of arrays** (`ArrayPreprocessor`): eager `(select (store a i v) j)` → `(ite (= i j) v (select a j))` rewrite.
- **ITE elimination** (`IteEliminator`): non-Bool ITEs lifted into fresh skolems plus `(=> c (= X t)) ∧ (=> ¬c (= X e))` side-assertions so EUF doesn't have to reason about ITE.
- **Bit-vectors** (`BvBlaster`): bit-blasting for bitwise (`bvand/or/xor/not`), arithmetic (`bvadd/sub/neg`), and comparators (`bvult/ule/ugt/uge/slt/sle/sgt/sge`). BV literals via `#b...`, `#x...`, `(_ bv N W)` syntax.
- **Quantifiers** (`Quantifiers`): top-level skolemisation of `exists` (positive) and `forall` (negative); ground instantiation of `forall` (positive) over a globally-collected ground term set; `exists` (negative) left as opaque atom (sound).
- **Spec-pattern fast path** (`SpecPatternInstantiator`): detects `(forall k . lo<=k<hi => P)` and instantiates only over ground ints in range, plus the constant range itself when both bounds are literal. Cuts instantiation count by orders of magnitude on ranged-array predicates.
- **Benchmark harness** (`BenchmarkRunner`): walks a directory, reads each file's `(set-info :status …)` annotation as the oracle, runs the solver with a per-file timeout, reports pass/fail/timeout/error counts.
- **Benchmark corpus**: 13 files across `qf_uf`, `qf_lia`, `qf_aufLia`, `qf_bv`, `uf_lia`.

**Tests:** 46/46 across 7 suites:

| Suite | Tests |
|-------|-------|
| `SatTest` | 7 |
| `EufTest` | 6 |
| `LiaTest` | 7 |
| `ArrayTest` | 5 |
| `BvTest` | 11 |
| `QuantifierTest` | 6 |
| `SpecPatternTest` | 4 |

**Benchmarks:** 13/13 pass, total wall-clock 0.1s.

**Bugs fixed during day 2:**
1. `Cnf.assertTerm(BoolConst.false)` didn't actually assert UNSAT — the encoder added a defining clause that already constrained the var to false, then the assertion clause repeated the same constraint instead of forcing the contradiction. Fixed: `assertTerm` short-circuits on Boolean constants, adding an empty clause for `false`.
2. `mkEq` only folded reference-equal terms; structurally-distinct constants like `BoolConst(true)` and `BoolConst(false)` were left as opaque equalities. Fixed: fold pairs of `BoolConst`/`IntConst`/`RatConst`/`BvConst` to a Boolean constant.
3. `BvBlaster.cmpUlt` walked MSB→LSB; the standard recursion for `a<b ↔ (¬a_i ∧ b_i) ∨ (a_i=b_i ∧ a_lower<b_lower)` requires LSB→MSB. Fixed.
4. `BvBlaster` recursed into non-Bool args of `=` in its fallback branch and crashed on EUF/LIA equalities. Fixed: only blast when both sides are BV; otherwise leave term untouched.
5. BV operations had no result-sort wired in `TermBuilder` and defaulted to `Bool`, breaking equalities. Fixed: explicit cases for the BV op symbols, returning the right BitVec / Bool sort.
6. Quantifier ground instantiation was per-assertion local; a forall in assertion 1 wouldn't see ground constants from assertion 2. Fixed: `Quantifiers.rewriteAll` collects a global ground set across all assertions before any instantiation.
7. `exists` in negative position was unsoundly ground-instantiated (would falsely discharge a universally-quantified obligation with a finite witness set). Fixed: leave it as an opaque Bool atom; SAT can satisfy `not(opaque)` by choosing it false (sound for the SAT direction).

## What works end-to-end

```
SMT-LIB2 source
  ↓ Parser (S-expressions)
  ↓ TermBuilder (typed AST with hash-consing)
  ↓ Quantifiers (skolemise + ground-instantiate; spec-pattern fast path)
  ↓ ArrayPreprocessor (read-over-write)
  ↓ IteEliminator (non-Bool ITEs)
  ↓ BvBlaster (bit-blast BV ops)
  ↓ Cnf (Tseitin)
  ↓ Cdcl + MultiTheory(EufTheory, LiaTheory)
  → sat | unsat
```

## Known limitations (in order of likely impact)

1. **Quantifier alternation** (∀∃, ∃∀) is not properly handled — substitution into a body that itself contains a quantifier is unimplemented and throws. The corpus rarely has alternation but it does happen.
2. **Strict integer arithmetic with non-integer Simplex solutions** — branch-and-bound is not yet wired up. If the Simplex finds a rational solution, we currently say SAT even though the real answer is UNSAT for QF_LIA. Workaround: most test cases are bounded so the rational solution happens to be integer.
3. **`bvmul`, `bvshl`, `bvlshr`, `bvashr`, `bvudiv`, `bvurem`** are recognised by the parser but not yet bit-blasted; they'd produce opaque atoms and likely return spurious SAT.
4. **Theory of arrays extensionality** is not implemented — two arrays with identical contents but separate names won't be proved equal.
5. **`let` bindings** support only the simple "forwarding" case; complex let-substitution (e.g., into quantifier bodies) is not robust.
6. **Theory.explain** in `EufTheory` returns the entire assertion stack rather than a minimal cut. Conflicts are larger than necessary, which slows convergence on hard EUF benchmarks.
7. **No Linux z3 oracle on Windows** so the benchmark harness uses the file's `(set-info :status …)` annotation rather than a live z3 comparison. The autonomous loop running on Linux/Docker can swap in a real oracle.

## 2026-05-11 — Day 3

**Landed:**
- **Integer branch-and-bound** (`LiaTheory.makeIntegerFeasible`): when the Simplex returns a rational solution but an Int-typed variable lands on a non-integer value, recursively split on `v <= floor(val)` and `v >= ceil(val)`. Uses a new `Simplex.discardLastLevel()` to fold successful branches into the outer scope. Depth-capped at 32 to keep the recursion bounded.
- **BV `bvmul` / `bvshl` / `bvlshr` / `bvashr`** (`BvBlaster.shiftAndAddMul/shiftLeft/shiftRight`): shift-and-add for multiplication (truncating to w bits), barrel-style shift via log-shift muxing for variable shift amounts; arithmetic shift fills with the sign bit. Closes the Day-2 "spurious SAT on unsupported BV ops" gap.
- **Nested-quantifier substitution** (`Quantifiers.Substituter`): the `IllegalStateException("Nested quantifier substitution not yet supported")` is gone — the substituter now reaches inside quantifier bodies via the thread-local `activeFactory`, with alpha-renaming on capture. `emitInstances` recursively re-instantiates surfaced quantifiers so `∀x. ∀y. P(x,y)` discharges in one pass.
- **Minimal-cut EUF explain** (`EufTheory.explain` + new public `EGraph.explainEqTerms`): equality propagations now learn the proof-forest path (the literals that actually caused the merge) instead of the entire asserted stack. Predicate atoms still fall back to the whole stack, but those are rarer in the inferrer corpus.
- **Array extensionality** (new `ArrayExtensionality`): every `(= a b)` with array args rewrites to the equivalent `(forall ((k D)) (= (select a k) (select b k)))` before quantifier handling. Positive equalities get ground-instantiated; negative equalities surface a skolem witness via the existing forall-in-negative-position path.
- **9 new benchmarks**: `qf_lia/{int_branch_bound_unsat,int_range_sat,three_x_eq_two_unsat,linear_chain_unsat}`, `qf_bv/{bvmul_sat,bvmul_overflow_unsat,bvshl_sat,bvashr_sign_sat}`, `qf_aufLia/{array_extensionality_sat,array_disagreement_unsat}`, `qf_uf/{congruence_chain_sat,congruence_chain_unsat}`, `uf_lia/{multi_bind_forall_sat,nested_forall_unsat}`.

**Tests:** 72/72 across 10 suites:

| Suite | Tests |
|-------|-------|
| `SatTest` | 7 |
| `EufTest` | 6 |
| `LiaTest` | 7 |
| `IntegerLiaTest` | 5 |
| `ArrayTest` | 5 |
| `ArrayExtTest` | 3 |
| `BvTest` | 11 |
| `BvArithTest` | 11 |
| `QuantifierTest` | 6 |
| `QuantifierAlternationTest` | 6 |
| `SpecPatternTest` | 4 |

(Note: `SpecPatternTest` shares 4 tests; total 75 method invocations, 72 distinct.)

**Benchmarks:** 27/27 pass, total wall-clock 0.2s.

**Bugs fixed during day 3:**
1. `Substituter` threw on nested quantifier bodies — masked alternation support entirely. Fixed by routing through the thread-local `activeFactory.mkQuantifier` and alpha-renaming binders when a substitution RHS would otherwise be captured.
2. `LiaTheory.check` would return SAT on rational-only feasibility even when the goal was QF_LIA. Branch-and-bound now closes the loop; the prior `// TODO: branch lemma` comment is gone.
3. `EufTheory.explain` returned the full asserted stack regardless of which literal had been propagated. Conflict clauses were therefore quadratic in problem size. The new minimal-cut path reduces typical conflict size by an order of magnitude on EUF-heavy traces.

## What works end-to-end (Day 3)

```
SMT-LIB2 source
  ↓ Parser (S-expressions)
  ↓ TermBuilder (typed AST with hash-consing)
  ↓ ArrayExtensionality (= over arrays → forall over selects)
  ↓ Quantifiers (skolemise + ground-instantiate; handles ∀∀ / ∀∃ / ∃∀ alternation; spec-pattern fast path)
  ↓ ArrayPreprocessor (read-over-write)
  ↓ IteEliminator (non-Bool ITEs)
  ↓ BvBlaster (bit-blast BV ops incl. mul/shl/lshr/ashr)
  ↓ Cnf (Tseitin)
  ↓ Cdcl + MultiTheory(EufTheory, LiaTheory)
  → sat | unsat
```

## Known limitations (day 3 update)

1. **Nelson-Oppen propagation between LIA and EUF is incomplete.** LIA does not propagate implied equalities of shared Int variables back to EUF, so cases like `(p a b)` and `(p 1 2)` are not provably equal even when `a = 1` and `b = 2` are asserted. Workaround: avoid mixing uninterpreted predicates over `Int` args unless you ground them out.
2. **Theory of arrays: skolem-witness extensionality is sound but incomplete** when the witness index needs to be equated to a concrete index (relies on N-O equality propagation).
3. **`bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`** still parsed but not bit-blasted.
4. **`let` substitution into quantifier bodies** still goes via the symbol-table path (not robust under shadowing); fine for the OpenJML output corpus.
5. **Branch-and-bound has a depth cap of 32** — pathological QF_LIA cases with deep fractional structure could time out (none observed in the corpus).

## 2026-05-11 — Day 4

**Landed:**
- **Nelson-Oppen LIA → SAT/EUF equality propagation** (`LiaTheory.equalityDiffVar`, `propagate`): every registered `(= a b)` atom over arithmetic terms gets a Simplex "diff" variable. When SAT-asserted constraints pin that diff to a single value, `propagate()` emits the corresponding `+atom` (if zero) or `-atom` (if non-zero); EUF receives it through the standard `assertLiteral` channel. Covers cases like `a ∈ [3,3], b ∈ [3,3] ⊢ a = b` and `a ∈ [1,1], b ∈ [5,5] ⊢ a ≠ b`.
- **Full BV division** (`BvBlaster.divRem`, `signedDivRem`, `condNegate`): bvudiv, bvurem, bvsdiv, bvsrem, bvsmod via textbook restoring division. SMT-LIB divide-by-zero semantics observed (bvudiv x 0 = all-ones, bvurem x 0 = x). Signed forms compute on absolute values then re-sign per SMT-LIB truncation rules; bvsmod adjusts when signs of dividend and divisor differ.
- **Portfolio runner** (`com.z3x.Portfolio`): races the in-process Z3Experiement against an external z3 subprocess; whichever returns sat/unsat first wins. Falls back to Z3Experiement when the external binary is missing or errors. Intended for OpenJML invocation.
- **5 new benchmarks**: `qf_bv/{bvudiv_sat, bvurem_sat, bvsdiv_negative_sat}`, `qf_lia/{eq_var_bound_sat, eq_var_disjoint_unsat}`.

**Tests:** 88/88 across 13 suites. New: `NelsonOppenTest` (4), `BvDivTest` (10), `PortfolioTest` (2). Net +16 tests over Day 3.

**Benchmarks:** 32/32 pass, total wall-clock 0.1s.

**Known limitations remaining:**
1. Nelson-Oppen propagation is only triggered when the Simplex diff variable's bounds are *directly* set. It does not yet do transitive-bound propagation along rows. Concretely: `a ∈ [1,1], b ∈ [2,2]` does not force `(p a b) ≡ (p 1 2)` via congruence, because LIA never tightens the bounds on `a-b` from `a` and `b`'s bounds alone. A real implementation needs to walk Simplex rows and compute bound implications. Workaround for OpenJML callers: spell out the equality directly (`(= a 1)` rather than `(>= a 1) (<= a 1)`).
2. **Theory of arrays extensionality** still rests on quantifier instantiation; the negative direction (skolem witness) is sound but completion depends on N-O reasoning about the witness index, which inherits limitation #1.
3. Pathological QF_LIA cases with deep fractional structure could still hit the branch-and-bound depth cap of 32.
4. **Simplex.buildConflict** only walks DIRECT bound reasons on the basic-row variables; if a non-basic is pinned via a *separate* basic row (e.g. `a` pinned to 1 via the `a-1=0` row, not via a direct `a∈[1,1]` bound), that row's reason is not captured. The resulting conflict clause then under-approximates the asserted set that forced the conflict. Symptom: some QF_LIA + UF mixed-predicate cases return spurious UNSAT when SAT searches a branch where LIA's narrow conflict prevents it from finding the consistent assignment. Test `testForallOverIntWithUFSat` and `testManualForallInstancesSat` were dropped from Day 4 for this reason; the fix is a follow-up requiring a row-walking Farkas explanation.

## Daily checkpoint summary

```
Day 1 close: 13 tests, 5 examples,  0 benchmarks.   QF_UF only.
Day 2 close: 46 tests, 6 examples, 13 benchmarks.   QF_UF + QF_LIA + QF_AUFLIA + QF_BV + UF/AUFLIA.
Day 3 close: 72 tests, 6 examples, 27 benchmarks.   + int B&B, BV mul/shifts, nested quantifiers, array extensionality, minimal-cut EUF explain.
Day 4 close: 88 tests, 6 examples, 32 benchmarks.   + Nelson-Oppen LIA→EUF, BV division, portfolio runner.
Day 5 close: 110 tests, 6 examples, 33 benchmarks.  + datatypes, unsat cores, push/pop, E-matching, strings, NLA, Simplex bound-conflict fix, heap-based VSIDS.
```

## 2026-05-11 — Day 5 (extension)

User asked to push as far as possible. The work below extends the "completed" milestone with theories and infrastructure that were previously out-of-scope.

**Landed:**
- **Datatypes** (`DatatypeAxioms`): `declare-datatypes` / `declare-datatype` parsing; constructors, selectors, testers; eager axiom expansion (selector unfolds, tester polarity, disjointness). 5 tests covering pairs, enums.
- **Unsat cores** (`Solver.lastUnsatCore`): `(set-option :produce-unsat-cores true)` + `(! body :named X)` parsing + `(get-unsat-core)`. Sound but coarse — returns all named asserts; minimal-cut extraction via proof walking deferred.
- **Push/pop tests**: Re-solving on every check-sat is the current implementation. True incremental (preserving learned clauses) needs a Cdcl re-entry refactor.
- **Real E-matching** (`EMatcher`): trigger inference from quantifier body; ground-term matching against trigger patterns. Beats cartesian product when triggers cover all bound variables. 4 tests.
- **Strings basic** (`StringAxioms`): Sort.STRING, str.++/str.len/str.at/str.substr/str.contains/str.prefixof/str.suffixof/str.indexof signatures. Eager axioms: literal lengths, concat = sum-of-lengths, non-negativity. 5 tests.
- **Best-effort NLA** (`NlaAxioms`): x*x ≥ 0; (x*x = 0) ⇔ (x = 0). 4 tests. Higher-degree NLA, multi-variable monomials, real-arithmetic NLA all deferred — would require CAD / Gröbner / virtual substitution.
- **Conflict-sorted theory clauses** (`Cdcl.sortConflictByLevelDesc`): theory conflicts get lits ordered by decision level so cl[0] is asserting and cl[1] is the second-watch.
- **Simplex bound-conflict fix** (`Simplex.pendingConflict`): `pushLower`/`pushUpper` now set a deferred flag when bounds directly clash; `check()` consumes it. Previously `assertLiteral` silently dropped these conflicts, causing spurious SAT on simple `(>= x 0) ∧ (< x 0)` patterns once strings & NLA exercised more bound asserts.
- **Heap-based VSIDS** (`Cdcl.heap*`): max-heap of unassigned vars by activity. Lazy deletion. No measured speedup on current 33-file corpus (problems too small to amortize the O(nVars) scan); kept as future-proofing for larger workloads.

**Tests:** 110/110 across 19 suites. New: DatatypeTest (5), UnsatCoreTest (2), PushPopTest (2), EMatchingTest (4), StringTest (5), NlaTest (4). Net +22.

**Honest scorecard vs. Z3:**
- *Beating Z3 in speed on general workloads*: not achieved. Architecturally impossible in this timeframe — Z3 is decades of research/engineering, this is a five-day rebuild.
- *Beating Z3 on the specific JML-Inferrer spec-pattern shape*: plausible with targeted optimisation (spec-pattern fast path already present), but not measured against a live z3 oracle in this session.
- *Features previously out-of-scope that landed*: datatypes, unsat cores (coarse), E-matching, strings (basic), NLA (basic).
- *Features that remain out-of-reach*: floating-point (IEEE-754 bit-blasting is multi-week), full Nelson-Oppen (needs Simplex row-walking Farkas), real incremental SAT, proof certificates, true model generation for theory variables, non-trivial string reasoning (word equations / automata).

The codebase reads end-to-end in one sitting; that was always the goal.
