# Z3Experiement progress log

## 2026-05-08 (day 1, kickoff session)

**Landed:**
- Project skeleton: pom.xml, SCOPE.md, examples/, src tree.
- SMT-LIB2 frontend: `Lexer`, `Token`, `SExpr`, `Parser` covering the subset OpenJML emits (declare-sort/fun/const, assert, check-sat, push/pop, set-logic, set-info/option).
- Term layer with hash-consing: `Sort`, `Term`, `TermFactory`, `TermBuilder`. Built-in simplification for and/or/not/ite/equality/arithmetic constants.
- Tseitin CNF transformation in `Cnf`: each Boolean subterm gets a propositional variable; theory atoms are tagged.
- CDCL SAT solver in `Cdcl`: watched literals, VSIDS branching, 1UIP conflict analysis, Luby restarts, learned-clause activity-based DB reduction.
- Theory hook interface: `TheoryHook` with assert/retract/check/propagate/explain.
- EUF theory: `EGraph` with backtrackable union-find + congruence closure via signature table; `EufTheory` glues atoms (equality and Boolean predicates) to the E-graph.
- Solver driver: `Solver` reads SMT-LIB2 commands, runs check-sat through CDCL+EUF.
- Test harness: zero-dependency `TestHarness` runs all SatTest/EufTest methods via reflection.

**Test results: 13 passed, 0 failed.**

| Suite | Tests | Time |
|-------|-------|------|
| SatTest | 7 | < 25ms total |
| EufTest | 6 | < 5ms total |

Examples verified end-to-end:
- `sat-trivial.smt2`, `unsat-trivial.smt2` ✓
- `euf-congruence.smt2`, `euf-sat.smt2` ✓
- `pigeonhole-3-2.smt2` ✓ (UNSAT via CDCL alone)

**Bugs found and fixed during the kickoff:**

1. *Unit-clause level-0 conflicts not detected.* When two contradictory unit clauses [+v] and [-v] were both added during initial loading, the second `enqueue` silently no-oped because `value[v]` was already set, and the SAT solver never saw the conflict. **Fix:** `enqueue` now returns `boolean`; `addInitialClause` records `okay = false` on disagreement; `solve()` returns UNSAT immediately on `!okay`.

2. *Theory propagation conflict at level 0 looped forever.* When the theory propagated a literal that disagreed with a level-0 assignment, we'd learn a clause and call `enqueue(asserting, ...)`, but the asserting literal was already falsified, so enqueue silently failed and the next solve iteration re-detected the same propagation. **Fix:** every enqueue at the conflict-resolution callsites checks the return value and surfaces UNSAT when the disagreement is at level 0.

3. *`EGraph.lastConflict` never cleared.* Once set by an assertion failure, every subsequent `theory.check()` returned the stale conflict clause forever. **Fix:** `EufTheory.check()` consumes-and-clears.

**What's next (day 2):**

- Wire up `LiaTheory` (Simplex over rationals, Dutertre/de Moura). Branch-and-bound for integers.
- Theory-combination harness so EUF + LIA can both run under one Solver instance.
- Build a benchmark runner that compares verdicts against a `z3` oracle on QF_UF and QF_LIA SMT-LIB benchmarks.
- Expand SMT-LIB frontend to handle `let`, `forall`/`exists` (parse-only for now, error if asserted).

**Known limitations carried into day 2:**

- Theory.explain is conservative (returns whole assertion stack rather than a minimal cut). This makes learned clauses larger than necessary and slows convergence on hard EUF benchmarks. Replace with a proof-tree walk along the `proofParent` edges.
- Boolean variables are routed through EUF when no logic is set, which is wasteful — change `Solver.logicNeedsEuf` to actually inspect the assertions for theory atoms before paying the cost.
- DB reduction code path for handling the `firstLearned` boundary is suspect — it works on the test suite because we don't trigger reduction yet, but should be reviewed before benchmarks.
