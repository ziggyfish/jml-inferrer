# Strictly verifying a real specification for `NumberUtils.isCreatable`

The inferrer punts on `isCreatable` with `ensures true` (no behavioural
postcondition). This is a hand-crafted, **strictly verified** specification that
is meaningfully stronger, established through the project's OpenJML ESC pipeline
under the strict flag configuration.

## The verified specification

```java
//@ requires true;
//@ ensures (str == null || str.length() == 0) ==> !\result;
//@ ensures \result ==> (str != null && str.length() > 0);
//@ assignable \nothing;
public static boolean isCreatable(final String str) { ... }
```

plus three loop invariants required to discharge array-access safety:

```java
//@ maintaining start + 2 <= i && i <= chars.length;   // hex-digit loop
//@ maintaining start + 1 <= i && i <= chars.length;   // octal-digit loop
//@ maintaining start <= i && i <= sz + 1;             // main scan loop
//@ maintaining sz == chars.length - 1;
```

What this guarantees, beyond `ensures true`:
- **null/empty ⇒ false** (a real behavioural postcondition);
- **result true ⇒ the string was non-empty** (its contrapositive);
- **purity** (`assignable \nothing`); and, the non-trivial part,
- **no `ArrayIndexOutOfBoundsException`** on any `chars[i]` access, under strict
  bounds checking — which is exactly what the loop invariants establish and what
  the inferrer never produced (it emitted no loop invariants and punted to
  `ensures true`).

## Strict configuration

`--esc --code-math=safe --spec-math=bigint --arithmetic-failure=hard
--nullable-by-default` (the project's `OpenJMLInvoker` configuration).

## Results

| Solver | Good spec | Negative control (false postcond.) |
|---|---|---|
| **z3-4.7.1** | **VERIFIED** (exit 0, zero findings) | **FAILS** correctly: "prover cannot establish Postcondition at `return false`" (exit 6) |
| z3-4.13.4 (project default) | validity unknown / Z3 broken pipe (timeout) | — |
| z3-4.16.0 | validity unknown — "model is not available" (possible timeout) | — |

**The specification is strictly verified by z3-4.7.1**, and the negative
control proves the check is non-vacuous: replacing the null/empty postcondition
with the false claim `(str == null || str.length() == 0) ==> \result` is
rejected at the `return false` statement.

**Solver sensitivity (honest caveat).** The project's heavier default solvers
(z3-4.13.4, z3-4.16.0) time out / fail to produce a model on this method's
verification conditions — the complex disjunctive main-loop bound generates SMT
queries they cannot close within the budget, whereas z3-4.7.1 closes them. For
`isCreatable`, z3-4.7.1 is the solver that discharges the proof. This mirrors
the project's documented experience that solver choice is load-bearing on hard
methods.

## Significance

This is the AI-probe workflow applied to `isCreatable`: hand-craft a verifiable
spec, prove it strictly, and use it as a back-port target. The verified spec
shows the inferrer leaves recoverable ground on `isCreatable` in two places it
could be taught:
1. the **null/empty guard postcondition** (a generalisable heuristic: a leading
   `if (guard) return C;` yields `ensures guard ==> \result == C`); and
2. **loop invariants of the form `lo <= i && i <= bound`** for counter loops
   over arrays, which would let the bounds-safety discharge automatically.
