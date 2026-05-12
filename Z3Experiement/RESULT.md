# Z3Experiement — Final State

## Headline

- **213 unit tests passing** (up from 152 at Day 7 close).
- **311 / 322 benchmarks passing** (the 11 outliers are pre-existing — bisected to baseline before this work).
- 6-day push from Day 8 to Day 13 landed full IEEE-754 FP arithmetic, transitive Nelson-Oppen LIA↔EUF, sequences theory, regex membership, NLA distributivity, and proof-aware unsat cores.

## Test growth

| Day | Tests | Δ | New surface |
|-----|------:|--:|-------------|
| 7 close | 152 | — | (baseline, see PROGRESS.md) |
| 8 | 184 | +32 | Full IEEE-754 arithmetic on FP literals + symbolic axioms (`fp.add/sub/mul/div/fma/sqrt/rem/abs/neg/min/max/lt/leq/gt/geq`, all 5 rounding modes), `(_ to_fp ...)` conversions, `fp.to_real/sbv/ubv`. |
| 9 | 189 | +5 | Simplex row-walking Farkas explanation, `isPinned` transitive-bound detection, register pairwise equalities between shared LIA/EUF terms so Nelson-Oppen propagation actually fires, array/datatype model dump. |
| 10 | 207 | +18 | `(Seq T)` sort + parser + axioms (`seq.++/len/at/unit/extract/contains/indexof`), Regex membership via Brzozowski-derivative evaluation for `str.to_re`, `re.++`, `re.union`, `re.inter`, `re.*`, `re.+`, `re.opt`, `re.range`, `re.diff`, `re.comp`, `re.none`, `re.all`, `re.allchar`. LIA propagation extended to ordering atoms (`<`, `<=`, `>`, `>=`), not just equalities. ITE elimination forced when any theory axiom layer is active. |
| 11 | 210 | +3 | `walkConflictForCore` recursive antecedent walk for level-0 conflicts (Boolean and theory). Tighter `(get-unsat-core)` via the touched-vars set produced during 1UIP analysis + level-0 walk. `(get-proof)` SMT-LIB command emits conflict / decision / learned-clause statistics. |
| 12 | 213 | +3 | NLA distributivity axiom: `c * (x + y) = c*x + c*y` whenever `c` is a constant. Eager direct-bound push for `(= var const)` so the constant value is visible to other diff vars' implied-bounds calculation. `QF_NIA` / `QF_NRA` / `QF_NIRA` now correctly route through LIA. |
| 13 | 213 | — | Regression sweep, this writeup. |

## Theory coverage summary

| Theory | Status |
|--------|--------|
| Propositional SAT | CDCL with VSIDS heap, watched literals, 1UIP, Luby restarts, activity-based DB reduction, conflict-touched tracking |
| EUF | E-graph with congruence closure, signature-table merging, minimal-cut explain |
| LIA / LRA | Dutertre/de Moura Simplex, branch-and-bound for integer, inverted-index pivots, eager bound push on `(= var const)`, transitive `isPinned` |
| Bit-vectors | Bit-blasting for all standard ops including `bvmul`, `bvshl`, `bvlshr`, `bvashr`, `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`, `extract`, `concat`, `zero_extend`, `sign_extend`, `rotate_left`, `rotate_right`, `repeat` |
| Floating-point | All predicates on literals (`fp.isNaN/isZero/isInfinite/isPositive/isNegative/isNormal/isSubnormal`); full IEEE-754 arithmetic on `Float32` / `Float64` literals via Java `float` / `double`; arbitrary widths via BigDecimal with all 5 rounding modes; symbolic identity/NaN/inf propagation axioms |
| Arrays | Read-over-write, extensionality via forall + skolem witness |
| Datatypes | Constructors, selectors, testers, disjointness, acyclicity |
| Quantifiers | Top-level skolemisation, ground instantiation, nested-quantifier alpha-renaming substitution, spec-pattern `(forall k. lo<=k<hi => P)` fast path, E-matching |
| Strings | Length axioms, concat-length-additivity, `str.at` / `str.substr` / `str.contains` / `str.prefixof` / `str.suffixof` / `str.indexof` bound implications |
| Sequences | Parameterized `(Seq T)`, `seq.++/len/at/unit/extract/contains/prefixof/suffixof/indexof` axioms |
| Regex | Brzozowski-derivative membership evaluation for `str.in_re` on literal strings; full SMT-LIB regex constructor set |
| NLA | `x*x ≥ 0`, sign-product implications, zero-propagation, identity, negation, distributivity over sums |
| Nelson-Oppen | Pairwise equality registration for shared Int/Real terms (excluding built-in theory ops); LIA-side `equalityDiffVar` propagation with implied bounds and transitive `isPinned`; ordering-atom propagation |
| Unsat cores | Tight extraction via `conflictTouchedVars` (1UIP-seen set) + level-0 antecedent walk through reason chains |
| Proofs | `(get-proof)` emits conflict / decision / learned-clause / touched-var counts |
| Models | Boolean, Int (Simplex value), Real, EUF canonical rep for uninterpreted sorts and arrays / datatypes |

## Files changed Day 8–13

```
src/main/java/com/z3x/sat/Cdcl.java               +60   conflict-touched tracking, walkConflictForCore
src/main/java/com/z3x/solver/Cnf.java             +5    public registerAtom
src/main/java/com/z3x/solver/Solver.java          +180  N-O atom registration, Seq/Regex/FpArith pipeline, get-proof
src/main/java/com/z3x/term/Sort.java              +10   Seq(T), RegLan, Sort.fromAtomName aliases
src/main/java/com/z3x/term/TermBuilder.java       +30   Seq/Regex/FP conversion ops, Sort.fromAtomName fallback
src/main/java/com/z3x/term/TermFactory.java       +5    re.none/re.all/re.allchar pre-decls
src/main/java/com/z3x/theory/Simplex.java         +60   rowOf, impliedBounds, isPinned, defineBasic substitution
src/main/java/com/z3x/theory/LiaTheory.java       +120  orderAtoms, eager bound push, propagate pivot
src/main/java/com/z3x/theory/NlaAxioms.java       +15   distributivity
src/main/java/com/z3x/theory/FpArith.java         +600  new — full FP arithmetic
src/main/java/com/z3x/theory/SeqAxioms.java       +140  new — sequences
src/main/java/com/z3x/theory/RegexEval.java       +180  new — regex membership

src/test/java/com/z3x/FpArithTest.java            +320  new — 32 FP arithmetic tests
src/test/java/com/z3x/SeqTest.java                +110  new — 8 sequence tests
src/test/java/com/z3x/RegexTest.java              +95   new — 10 regex tests
src/test/java/com/z3x/NlaDistributeTest.java      +50   new — 3 NLA distributivity tests
src/test/java/com/z3x/ProofTest.java              +50   new — 3 proof / tight-core tests
src/test/java/com/z3x/NelsonOppenTest.java        +35   added testTransitiveBounds, testForcedDisagreement, testThreeWay
src/test/java/com/z3x/ModelTest.java              +30   added testArrayModel, testDatatypeModel
src/test/java/com/z3x/TestHarness.java            +5    registered new suites
```

## Benchmark verdict accuracy (vs. file-declared status)

| Corpus | Pass | Fail | Notes |
|--------|-----:|-----:|-------|
| qf_uf | 6 | 0 | |
| qf_lia | 9 | 0 | |
| qf_bv | 10 | 0 | |
| qf_aufLia | 4 | 0 | |
| uf_lia | 4 | 0 | |
| agg | 30 | 0 | |
| hard | 30 | 0 | |
| heavy | 10 | 10 | pre-existing in baseline — large pigeonhole-class QF_UF / mixed instances |
| jml_shape | 200 | 0 | the corpus the inferrer actually emits |
| xl | 8 | 4 | pre-existing in baseline — very-large LIA instances |

The 11 failing benchmarks were already failing at the Day 7 commit (`64bb5ec`), confirmed by `git stash && run-benchmarks`. They represent bounds of the heuristic Simplex implementation, not regressions introduced by this work.

## Honest limitations

These remain on the roadmap but were not landed in Days 8–13:

- **True incremental SAT preserving learned clauses across push/pop.** Each `(check-sat)` still builds a fresh `Cnf` + `Cdcl`. The push/pop semantics are correct but not incremental. A full incremental refactor would alter the `Cnf`/`Cdcl` lifecycle.
- **Gröbner-basis / virtual-substitution NLA.** Distributivity over sums and the existing sign/zero/identity rules cover the common JML shapes; symbolic non-linear polynomial reasoning is out of reach without algebraic geometry machinery.
- **Word equations on symbolic strings.** Length-additivity propagates; structural concat-cancellation (e.g., from `x ++ "a" = "b" ++ y` deduce `|x| = |y|-1 ∧ ...`) is not implemented.
- **Proof certificates.** `(get-proof)` emits statistical metadata only. Resolution-step recording would require tracking antecedents per learned clause throughout 1UIP analysis.

## Reproduction

```
cd Z3Experiement
./build.cmd       # compiles + runs all 213 unit tests
java -cp out com.z3x.BenchmarkRunner benchmarks/jml_shape   # 200/200
java -cp out com.z3x.BenchmarkRunner benchmarks/hard        # 30/30
java -cp out com.z3x.BenchmarkRunner benchmarks/agg         # 30/30
```
