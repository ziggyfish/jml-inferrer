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

## What's next (day 3+)

- Branch-and-bound integer extension to LIA (close known limitation #2).
- `bvmul` and shifts in `BvBlaster` (closes #3).
- Quantifier alternation via proper substitution-through-quantifiers (closes #1).
- More benchmark coverage — pull in a slice of SMT-COMP `QF_UF` and `QF_LIA` to stress-test convergence and timing.
- Profiling pass: where does the wall-clock go on the harder benchmarks? VSIDS, watch-list maintenance, or theory checks?
- Stretch goal #2: portfolio runner so OpenJML can call Z3Experiement alongside z3 and take whichever returns first.

## Daily checkpoint summary

```
Day 1 close: 13 tests, 5 examples,  0 benchmarks.   QF_UF only.
Day 2 close: 46 tests, 6 examples, 13 benchmarks.   QF_UF + QF_LIA + QF_AUFLIA + QF_BV + UF/AUFLIA.
```
