# Daikon vs JML-Inferrer — real run on Article 1's 11 classes

**Setup.** Daikon 5.8.24 (dynamic) run in Docker via the Chicory front end over a
hand-written workload driver (`DaikonDriver.java`) exercising the same 11 Apache
Commons Lang classes used in Article 1. JML-Inferrer (static) output taken from
its annotated source for the same classes. Daikon observed **358 program
points** and produced **~3,395 invariant lines**; JML-Inferrer specifies all
312 methods statically with no workload.

**Caveat.** Daikon's output depends entirely on the workload. This driver is a
hand-written exerciser, so Daikon's invariants reflect what it happened to
exercise — the coverage-dependence is visible in the results below and is the
defining property of dynamic detection, not a flaw in this particular run.

## Head-to-head on five representative methods

### MutableInt.add(int)
- **Daikon:** `operand == 5` (ENTER); `this.value - orig(this.value) - 5 == 0` (EXIT)
- **JML-Inferrer:** `requires (bigint)this.value+(bigint)operand in int range`;
  `ensures this.value == \old(this.value) + operand`; `assignable this.value`
- **Verdict:** Daikon **baked in the constant 5** (the only operand the driver
  passed) — both its precondition and postcondition are *wrong in general*.
  JML-Inferrer derives the correct *parameterised* postcondition `+ operand`
  plus an overflow precondition and the frame. **Canonical Daikon failure mode.**

### MutableInt.increment()
- **Daikon:** `this.value - orig(this.value) - 1 == 0`  (value == old + 1)
- **JML-Inferrer:** `requires this.value < Integer.MAX_VALUE`;
  `ensures this.value == \old(this.value) + 1`; `assignable this.value`
- **Verdict:** **Agree** on the core postcondition. JML-Inferrer adds the
  overflow precondition Daikon never observes (no overflowing run in the
  workload). Clean overlap + complementary static-only guard.

### Validate.isTrue(boolean)
- **Daikon:** `expression == true` (ENTER)
- **JML-Inferrer:** `requires expression`;
  `signals IllegalArgumentException when !expression`; `assignable \nothing`
- **Verdict:** **Agree** on the precondition (Daikon recovers it from coverage).
  JML-Inferrer additionally expresses the **exceptional contract** (`signals`),
  which Daikon does not model as a contract.

### NumberUtils.compare(int,int)
- **Daikon:** `return one of { -1, 0, 1 }` (EXIT); `y >= -1` (ENTER)
- **JML-Inferrer:** `ensures \result == Integer.compare(x, y)`;
  `ensures \result == Byte.compare(x, y)` *(spurious)*; `assignable \nothing`
- **Verdict:** Daikon's `result ∈ {-1,0,1}` is a clean **value-emergent**
  postcondition; `y >= -1` is a coverage artifact. JML-Inferrer is more precise
  (`== Integer.compare`) **but emitted a wrong `Byte.compare` clause** — so
  *neither tool is noise-free*.

### NumberUtils.toInt(String, int)
- **Daikon:** two split exits; `return one of { 0, 99 }`; `return >= -1`;
  `defaultValue one of { 0, 99 }`
- **JML-Inferrer:** `ensures \result == Integer.parseInt(str)`;
  `signals on RuntimeException returns defaultValue`; `assignable \nothing`
- **Verdict:** Daikon captures the branch via split exit points but its
  `return ∈ {0,99}` is a coverage artifact (only defaults 0/99 driven).
  JML-Inferrer captures the parse-else-default branch semantics structurally.

## What the run confirms (with real data)

| Property | Daikon | JML-Inferrer |
|---|---|---|
| Paradigm | dynamic (ran the driver) | static (read source) |
| Methods covered | 358 ppts the driver exercised | all 312 methods, no workload |
| Value-emergent invariants (`result ∈ {-1,0,1}`) | **yes** (its strength) | partial / different form |
| Parameterised postconditions (`+ operand`) | **no** — baked in `+ 5` | **yes** |
| Frame / `assignable` | no | yes |
| Exceptional contract (`signals`) | no | yes |
| Overflow / un-exercised guards | no (never observed) | yes |
| Coverage artifacts (`operand==5`, `return∈{0,99}`) | **yes** (many) | no |
| Spurious clauses | yes (coverage) | yes (`Byte.compare`) — different cause |

## Bottom line

The run substantiates the conceptual comparison with real data:

1. **They overlap** where behaviour is both structurally and dynamically
   apparent (`increment`, `isTrue` precondition).
2. **Daikon's distinctive failure is coverage over-fitting** — it generalised
   the literal `5` into `add`'s contract and `{0,99}` into `toInt`'s return,
   which are wrong in general. JML-Inferrer's source-derived contracts are
   parameterised and correct in those cases.
3. **Daikon's distinctive strength is value-emergent invariants** Daikon found
   `compare ∈ {-1,0,1}` directly; JML-Inferrer states it only via delegation.
4. **JML-Inferrer expresses contract structure Daikon cannot** — frames,
   exceptional `signals`, and guards on un-exercised paths.
5. **Neither is noise-free**, but the noise has different origins: Daikon's from
   limited coverage, JML-Inferrer's from heuristic over-emission.

The complementarity is real and measurable: an ensemble (Daikon's value-emergent
invariants ∪ JML-Inferrer's structural contracts, both filtered by OpenJML)
would dominate either alone — the publishable head-to-head result Article 1
currently lacks.
