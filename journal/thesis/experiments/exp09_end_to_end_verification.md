# Experiment 09 — End-to-End Client-Against-Dependency Verification

**Strengthens:** RQ3 — makes the "verification across dependencies without the
source" capability concrete rather than asserted.
**Tier:** 3.

---

## 1. What it tests

The distribution chapter establishes that inferred contracts can be embedded in a
compiled library losslessly, and argues this lets a consumer verify client code
against the dependency's contract without the dependency's source. That last step
is argued, not shown. This experiment performs it: it takes a real client that
uses a dependency, embeds inferred contracts in the dependency's compiled JAR,
and verifies the client against those embedded contracts with OpenJML — with no
access to the dependency's source.

**Hypotheses.**

- **H1 (verification works from embedded contracts).** OpenJML can verify a
  client against a dependency using only the contracts recovered from the
  dependency's embedded bytecode, producing the same verdicts it would from
  hand-written stubs.
- **H2 (it finds real client-side obligations).** The verification surfaces
  genuine client-side preconditions/assertions — e.g. a client that may pass an
  argument violating the dependency's inferred precondition — that are invisible
  without the dependency's contract.

**Research question.** *Can a client be formally verified against a dependency
using only the contracts embedded in the dependency's compiled artefact, and does
doing so reveal real client-side obligations?*

---

## 2. How it would be tested

**Subjects.** One or two dependency/client pairs: a library with good inferred
specs (e.g. Commons Lang) as the dependency, and a small but real client that
calls it in ways that exercise the dependency's inferred preconditions (an
existing downstream project, or a focused client harness).

**Procedure.**

1. Infer specs for the dependency from its source; embed them into the
   dependency's compiled JAR with `AsmJmlSpecWriter`.
2. **Discard the dependency source.** From here only the embedded JAR is used.
3. Recover the dependency's contracts from the embedded JAR with
   `AsmJmlSpecReader`, and convert them into the form OpenJML consumes as the
   assumed specifications of the called methods (JML stub files / the sidecar
   `.jmlspec` format the embedder already emits).
4. Run OpenJML ESC on the *client* against those recovered contracts.
5. **H1:** confirm the verdicts match those obtained when OpenJML is given the
   dependency's hand-written/source-derived stubs (a controlled comparison).
6. **H2:** identify client sites where verification fails because the client may
   violate a dependency precondition, and confirm by inspection that these are
   genuine obligations (e.g. an unchecked argument passed to a method requiring
   non-null / in-range).

**Metrics.** Agreement between embedded-contract verification and
source-stub verification (H1 — should be identical); count and validity of
client-side obligations surfaced (H2); any contracts that fail to round-trip into
a verifiable form (should be zero, given the chapter's 100% lossless result).

**Analysis.** H1 is a correctness check (embedded ≡ source-derived contracts for
verification purposes); H2 is the value demonstration (real obligations found).
A worked example — a client bug or latent precondition violation caught via the
embedded dependency contract — is the deliverable that makes the capability
tangible.

---

## 3. How it would be added to the inferrer tool

The embedding, reading, and OpenJML pieces all exist; the work is the
recover-and-verify glue.

**New harness `com.jml.inferrer.eval.ClientVerificationRunner`.**
Pipeline: (1) infer + embed dependency (`CodebaseProcessor` + `AsmJmlSpecWriter`),
(2) read contracts back (`AsmJmlSpecReader`), (3) materialise them as OpenJML
`.jmlspec` stub files keyed by class internal name — the embedder *already* emits
this sidecar format for the un-embeddable case, so reuse `SidecarWriter`/the stub
emitter, (4) invoke OpenJML ESC on the client with the stubs on the specs path,
(5) collect verdicts.

**Contract-to-stub materialiser.**
If not already factored out, extract the sidecar `.jmlspec` generation into a
reusable `com.jml.inferrer.embed.StubMaterialiser` so contracts recovered from
*bytecode* (not just from source) can be written as stubs OpenJML reads. This is
the one genuinely new piece; it bridges the reader to the verifier.

**Controlled comparison mode.**
A `--baseline source-stubs` flag that runs the same client verification using
stubs generated directly from the dependency source, so H1's equivalence check is
automated.

**Reuse.** `AsmJmlSpecWriter`/`Reader`, the sidecar stub format, the Docker
OpenJML ESC pipeline, and `FormalVerificationTestBase` are all in place.

---

## Threats and pitfalls

- **OpenJML specs-path ergonomics.** Getting OpenJML to consume recovered stubs
  as assumed callee contracts for a separately-compiled client may need
  classpath/specspath configuration care; pilot on a one-method client first.
- **Scope creep into full verification.** The goal is to demonstrate
  verification *using embedded contracts*, not to verify a whole application;
  keep the client small and the claim narrow (the contracts are usable; real
  obligations are found), not "the client is fully verified".
- **Inferred-contract gaps.** Where the dependency's inferred contract is
  incomplete (the RQ1 recall gap), the client verification will be
  correspondingly weaker; report this as inherited, not new.
- **Single worked example risk.** One example is anecdote; aim for a handful of
  client sites across one or two dependencies so H2 is more than a single case.

## Effort

Low–medium. The `StubMaterialiser` bridge ≈ 1 week; the harness and the
controlled comparison ≈ 1 week; finding/constructing a client that exercises real
obligations ≈ 1 week. Most components exist.

## Deliverables

A demonstration that a client verifies against a dependency using only embedded
contracts (with verdict-equivalence to source-derived stubs), plus a worked
example of a real client-side obligation surfaced this way — turning the
distribution chapter's "enables verification across dependencies" from assertion
into demonstration.
