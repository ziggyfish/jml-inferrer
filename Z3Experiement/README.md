# Z3Experiement

A from-scratch SMT solver, built as a 4-day pedagogical experiment (2026-05-08 — 2026-05-12).

**This is not a competitor to Z3.** Z3 is the product of two decades of theoretical and engineering work; the gap on a general workload is multiple orders of magnitude. This project exists to:

1. Implement the full DPLL(T) architecture end-to-end so the components can be read in one sitting.
2. Provide a sandbox for *targeted* optimisations specific to the JML-Inferrer's verification corpus (forall-int over array element predicates + linear bounds).

Read [`SCOPE.md`](SCOPE.md) for the full goal definition, daily checkpoints, and anti-patterns. Read [`PROGRESS.md`](PROGRESS.md) for what's landed each day.

## Architecture

```
SMT-LIB2 source
  ↓ Lexer / Parser / TermBuilder           (com.z3x.parser, com.z3x.term)
  ↓ ArrayExtensionality                    (com.z3x.theory.ArrayExtensionality)
  ↓ Quantifiers (skolemise + instantiate)  (com.z3x.theory.Quantifiers)
  ↓ ArrayPreprocessor (read-over-write)    (com.z3x.theory.ArrayPreprocessor)
  ↓ IteEliminator                          (com.z3x.theory.IteEliminator)
  ↓ BvBlaster (bit-blast BV ops)           (com.z3x.theory.BvBlaster)
  ↓ Cnf (Tseitin)                          (com.z3x.solver.Cnf)
  ↓ Cdcl + MultiTheory(EUF, LIA)           (com.z3x.sat, com.z3x.theory)
  → sat | unsat
```

## What works (Day 4 / final)

- SMT-LIB2 parser covering the subset OpenJML emits.
- Hash-consed term representation with Boolean and arithmetic operator simplification.
- Tseitin CNF transformation.
- CDCL SAT solver: watched literals, VSIDS, 1UIP conflict analysis, learned-clause minimisation, Luby restarts, activity-based DB reduction.
- Theory of equality + uninterpreted functions via backtrackable congruence closure; minimal-cut proof-forest explanations.
- Linear arithmetic over Q (Simplex with bound-driven pivoting, Bland's rule, Farkas-style conflict explanations).
- Integer feasibility via branch-and-bound.
- Nelson-Oppen LIA→EUF equality propagation (when Simplex bounds directly pin a diff variable).
- Theory of arrays with read-over-write *and* extensionality (negative direction via skolemised witness).
- Bit-vectors: full set including `bvmul`, `bvshl`, `bvlshr`, `bvashr`, `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`.
- Quantifier instantiation: skolemisation, ground instantiation with cartesian product, **alternation** (∀∀ / ∀∃ / ∃∀), spec-pattern fast path for ranged ∀ shapes.
- Benchmark harness comparing verdicts against each file's `(set-info :status …)` annotation.
- Portfolio runner racing Z3Experiement against an external z3 subprocess.
- **88 tests passing across 13 suites; 32 benchmarks passing.**

See [`PROGRESS.md`](PROGRESS.md) for the day-by-day commit log and known limitations.

## Run

Compile and run the example suite:

```bash
# from inside Z3Experiement/
./build.cmd     # Windows
./build.sh      # Unix
```

The build script compiles `src/main/java/**` then `src/test/java/**`, and executes `com.z3x.TestHarness`. To solve a single file instead:

```bash
java -cp out com.z3x.Main examples/euf-congruence.smt2
```

To run the benchmark harness against the corpus:

```bash
java -cp out com.z3x.BenchmarkRunner benchmarks 10000
```

To race against z3 in a portfolio:

```bash
java -cp out com.z3x.Portfolio my-file.smt2 z3 30000
```

The test harness is intentionally Maven-free so it runs anywhere with a JDK 21. (A Maven `pom.xml` is also present for IDE integration.)

## Files of interest

- `src/main/java/com/z3x/sat/Cdcl.java` — the CDCL SAT solver (single file, watched-literal core).
- `src/main/java/com/z3x/theory/EGraph.java` — the e-graph with backtrackable congruence closure.
- `src/main/java/com/z3x/theory/Simplex.java` — Dutertre/de Moura general Simplex.
- `src/main/java/com/z3x/theory/Quantifiers.java` — instantiation with the spec-pattern fast path.
- `src/main/java/com/z3x/theory/BvBlaster.java` — every bit-vector operation in one file.
