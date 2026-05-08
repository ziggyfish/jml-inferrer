# Z3Experiement

A from-scratch SMT solver, built as a 4-day pedagogical experiment (2026-05-08 — 2026-05-12).

**This is not a competitor to Z3.** Z3 is the product of two decades of theoretical and engineering work; the gap on a general workload is multiple orders of magnitude. This project exists to:

1. Implement the full DPLL(T) architecture end-to-end so the components can be read in one sitting.
2. Provide a sandbox for *targeted* optimisations specific to the JML-Inferrer's verification corpus (forall-int over array element predicates + linear bounds).

Read [`SCOPE.md`](SCOPE.md) for the full goal definition, daily checkpoints, and anti-patterns. Read [`PROGRESS.md`](PROGRESS.md) for what's landed each day.

## What works (day 1)

- SMT-LIB2 parser (subset OpenJML emits).
- Hash-consed term representation with Boolean and arithmetic operator simplification.
- Tseitin CNF transformation.
- CDCL SAT solver with watched literals, VSIDS, 1UIP conflict analysis, Luby restarts, learned-clause DB reduction.
- Theory of equality with uninterpreted functions via backtrackable congruence closure.
- 13/13 tests passing across SAT and EUF suites.

## What's coming

- Linear integer arithmetic via Simplex (Dutertre & de Moura).
- Theory of arrays.
- Bit-vectors via bit-blasting.
- E-matching for quantifier instantiation.
- Benchmark harness against z3 as oracle.
- Stretch: spec-pattern fast path for the JML-Inferrer corpus.

## Run

Compile and run the example suite:

```bash
# from inside Z3Experiement/
mkdir -p out
find src/main/java -name "*.java" > sources.txt
javac --release 21 -d out @sources.txt
java -cp out com.z3x.Main examples/euf-congruence.smt2
```

Compile and run the test harness:

```bash
find src/test/java -name "*.java" > tests.txt
javac --release 21 -cp out -d out @tests.txt
java -cp out com.z3x.TestHarness
```

(If Maven becomes available: `mvn package` produces an executable JAR with `com.z3x.Main` as entry point. The test harness is intentionally Maven-free so it runs anywhere with a JDK 21.)
