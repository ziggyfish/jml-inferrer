# Z3Experiement — 4-day autonomous scope

Started 2026-05-08. Target end 2026-05-12.

## Honest framing

This is **not** an attempt to beat Z3 on a general workload — that gap is decades of research and engineering. The realistic positive outcome is a coherent, working SMT solver that:

1. Demonstrates the full DPLL(T) architecture end-to-end.
2. Could plausibly be **tuned** to match or beat Z3 on the narrow shape of VCs that OpenJML emits for the JML-Inferrer corpus (lots of `\forall int k; lo <= k < arr.length; arr[k] PRED`, array reads, linear bounds, equality reasoning).
3. Stays small enough to read end-to-end, so future work can target specific optimisations.

If I produce a polished general solver that's 10-100× slower than Z3, that's a **success** for this experiment.

## In-scope (priority order)

1. **SMT-LIB2 frontend** (Lexer, Parser, command driver) — covering the subset OpenJML emits.
2. **Term layer** (sorts, hash-consing, simplification).
3. **CNF / Tseitin** transformation.
4. **CDCL SAT core**: watched literals, VSIDS, 1UIP conflict analysis, learned-clause minimisation, Luby restarts, phase-saving.
5. **Theory of equality + uninterpreted functions** (congruence closure with E-graph; backtrackable trail).
6. **Theory of linear arithmetic over Q** (Simplex with bound propagation; Dutertre & de Moura style).
7. **Integer extension**: branch-and-bound + Gomory cuts (best-effort).
8. **Theory combination** (Nelson-Oppen via equality propagation across shared variables).
9. **Theory of arrays** (read-over-write, extensionality lemmas on demand).
10. **Bit-vectors** (bit-blasting; preprocessing rewrites for masks/shifts).
11. **Quantifier instantiation** (E-matching with basic trigger inference; only ground unit instances).
12. **Driver** for SMT-COMP-style files (`set-logic`, `assert`, `check-sat`, `get-model`, `push`/`pop`, `exit`).

## Out-of-scope

- Non-linear arithmetic.
- Strings, sets, datatypes.
- Proofs / unsat cores (could be added as a stretch).
- Concurrency / parallel solving.
- Becoming faster than Z3 generally.

## Stretch goals (if everything above lands solidly)

- **Spec-pattern specialisation**: a fast path for the specific quantifier shapes OpenJML emits, bypassing general E-matching.
- **Portfolio runner** integration: harness so OpenJML can call Z3Experiement alongside z3 and take whichever returns first.
- **Benchmarking harness** running QF_UF, QF_LIA, QF_AUFLIA SMT-LIB benchmarks with z3 as oracle.

## Daily checkpoints

The autonomous loop should, at the end of each firing:

1. Run `mvn test` and confirm zero failures (or commit to a branch and note flaky tests).
2. Run the benchmark harness (once it exists) and record pass/fail/time per benchmark in `benchmarks/results-YYYY-MM-DD.txt`.
3. Update `PROGRESS.md` with what landed today and what's blocked.
4. Commit progress with a message starting `Z3Exp: <what landed>`.

## Anti-patterns to avoid

- **Do not** add features without tests — every theory module needs at least one positive (sat) and one negative (unsat) test.
- **Do not** silently weaken correctness for speed — better a slower correct solver than a faster wrong one. Soundness > completeness > speed.
- **Do not** spend more than half a session debugging a single benchmark; if blocked, file it as a known-bad in `benchmarks/known-failures.txt` and move on.
- **Do not** copy code from Z3 / cvc5 / MathSAT — license incompatibility. Re-derive from textbook references (Kroening & Strichman, Bradley & Manna, de Moura & Bjørner papers).

## Reference papers (re-derive from these, do not copy code)

- Marques-Silva & Sakallah, *GRASP: A Search Algorithm for Propositional Satisfiability* (CDCL).
- Eén & Sörensson, *An Extensible SAT-solver* (MiniSat — watched literals).
- Nieuwenhuis, Oliveras, Tinelli, *Solving SAT and SAT Modulo Theories* (DPLL(T)).
- Detlefs, Nelson, Saxe, *Simplify: A Theorem Prover for Program Checking* (E-graph).
- Dutertre & de Moura, *A Fast Linear-Arithmetic Solver for DPLL(T)* (Simplex variant).
- de Moura & Bjørner, *Efficient E-matching for SMT Solvers*.
