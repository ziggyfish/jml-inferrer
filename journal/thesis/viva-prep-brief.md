# Viva / Oral-Examination Preparation Brief — MPhil

**Thesis:** *From inference to integration: Formal specifications as the verification
spine of AI-native software development.*
**Candidate:** Brendan Edmonds · **Advisors:** Prof. Mark Utting (principal),
Dr Guowei Yang (associate) · **Degree:** MPhil (traditional monograph, 46 body pp).

> Rewritten 2026-07-02 for the MPhil restructure (three contributions / three RQs).
> Supersedes the earlier 5-study PhD brief. **Candidate rehearsal still required** —
> this is a preparation scaffold, not a substitute for practising aloud.

---

## 1. The 60-second thesis pitch

Formal specifications make behaviour machine-checkable, but they are rarely written
because authoring them by hand is costly. The machinery to *check* contracts is
mature; the *supply* of contracts is the gap. This thesis shows that specifications
inferred automatically from code are (i) good enough to be useful, (ii) composable
into a static analysis of library version-compatibility, and (iii) able to serve as
the verification layer that current agentic, natural-language development lifecycles
lack. One instrument — the JML-Inferrer — runs through all three. The arc is
*inference → integration*: making specifications cheap, then load-bearing.

## 2. The three contributions and their evidence status

| # | Contribution | Chapter | RQ | Evidence status |
|---|---|---|---|---|
| 1 | Heuristic static inference yields sound, verifiable JML that measurably improves LLM test generation | 3 | RQ1 | **Measured** (controlled comparison; OpenJML discharge) |
| 2 | A compositional WP pass strictly extends inference and enables behavioural version-compat reasoning | 4 | RQ2 | **Measured** (corpus count) + **design validated by instantiation** (blast-radius) |
| 3 | Inferred contracts as the contract layer + verification loop of AI-native lifecycles | 5 | RQ3 | **Designed, not deployed** — reference architecture from validated parts |

**Own this distinction unprompted.** The single most likely examiner probe is
"what did you *measure* vs *propose*?" Answer crisply: Chapters 3–4 carry data;
Chapter 5 is a reference architecture whose *components* are evidenced by 3–4 but
whose end-to-end deployment is future work. The thesis says so explicitly
(§ "Designed versus measured").

## 3. Anticipated examiner questions with grounded answers

**Q. Your headline compositional figure — 18,854 preconditions. Are they verified?**
No, and the thesis never claims so. They are **well-formed**: syntactically valid
and entry-scope-satisfiable, but not separately discharged by OpenJML. I keep
"verified" (checker-discharged) and "well-formed" strictly separate throughout; the
well-formedness filter is itself a guard that excludes vacuous clauses (e.g.
`ensures true`). An earlier, looser count (45,740) was cut to 18,854 precisely by
enforcing entry-state well-formedness.

**Q. P2 (edge-case guidance) produced more tests than P3 (specifications) yet a
lower mutation score. Explain.** Quantity of tests is a poor proxy for oracle
quality. P2 enumerates near-duplicate edge cases with weak assertions
(`assertNotNull`) that compile and pass but do not kill mutants; P3's tests are
concentrated on inferred clauses, giving higher mutant-kill density. P3 scores
81.8% vs P2's 68.2% (13.6 pp higher) with ~12% fewer tests. The four phases are
monotonic in information richness: P1 27.5 < P2 68.2 < P3 81.8 < P4 94.8.

**Q. The test-generation result depends on a language model. Is it reproducible?**
The inference is deterministic (a function of the AST), which is the sharp contrast
with prompting a model to emit JML. The LLM *consumer* is stochastic; the study
uses a paired design (same prompts with/without the contract), so non-determinism
is shared across conditions and the treatment effect is isolated. It establishes
direction and plausibility, not a universal effect size — a single model family was
used. *[CANDIDATE: state the exact model + version + sampling settings here before
the viva — currently unnamed in Ch 3.]*

**Q. How general is this beyond Java/JML/OpenJML/Z3?** Deliberately bounded. The
quantitative results rest on Apache Commons Lang and similar production Java, not a
random sample of all Java, and the toolchain is one language / one spec language /
one verifier / one solver. I state this as an external-validity threat and do not
let the synthesis imply method-general results. Multi-corpus replication is named
future work.

**Q. Is heuristic inference not just unsound guessing?** The heuristics are
unapologetically partial and may be individually unsound, but soundness is enforced
*externally*: a candidate clause is admitted only once OpenJML discharges it. An
unproven guess costs a failed proof, not a false guarantee. So the recovered
fragment is sound where emitted-and-verified; I never claim completeness.

**Q. Where does the verifier let you down?** Z3 is the substrate and the logic is
undecidable: timeouts on multiplicative arithmetic, quantified array theories, and
rich preconditions. Where the solver cannot decide, the pipeline reports
*unverified* — never a false guarantee. For the compatibility analysis this makes
the reading asymmetric: an alarm is trustworthy, silence is not a guarantee of
compatibility.

**Q. Why an MPhil-scale contribution — is this enough?** Three connected, individually
defensible results: a validated inference-and-utility result, a measured
compositional-extension result with a version-compatibility application, and a
reference architecture that unifies them. The connective argument (the *same*
call-graph edges that build specifications propagate contract changes) is the
integrative core, not five stapled papers.

## 4. Limitations to own (say them before the examiner does)

- Verified vs well-formed — the 18,854 figure is well-formed, not verified.
- Heuristic partiality — fidelity is a rate over *emitted* contracts, not coverage
  of all behaviour.
- SMT boundaries — some true specifications are beyond mechanical discharge.
- Single principal corpus — establishes effects in a realistic setting, not their
  generality.
- Chapter 5 is designed, not deployed — no controlled end-to-end trial.
- LLM study — single model family; model/version to be stated for reproducibility.

## 5. Candidate to-do before the oral

- [ ] Rehearse the pitch and the "measured vs designed" answer aloud.
- [ ] Insert the exact LLM model + version + sampling settings into Ch 3.
- [ ] Confirm whether UQ mandates the oral for a traditional MPhil (policy §3 cl. 9
      targets theses *including publications*; this is a monograph — confirm with the
      Graduate School).
- [ ] Be ready to sketch the WP call-graph propagation on a whiteboard.
