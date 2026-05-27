# Strengthening Experiments

Detailed plans for ten experiments that would strengthen the thesis
*Configuring Formal Methods for Industry*. Each plan states **what it tests**,
**how it would be tested**, and **how it would be built into the JML-Inferrer
tool**, plus threats, effort, and the thesis claim it shores up.

The experiments are tiered by how directly they support the thesis's *central*
claims (adoption, and the library-compatibility capability), which are currently
the most argued-rather-than-measured.

| # | Experiment | Strengthens | Tier |
|---|------------|-------------|------|
| [01](exp01_version_compatibility.md) | Version-to-version compatibility detection | Compatibility capability (RQ4) — keystone | 1 |
| [02](exp02_breaking_change_benchmark.md) | Breaking-change benchmark (precision/recall) | Compatibility rigour (RQ4) | 1 |
| [03](exp03_semver_correlation.md) | Semantic-versioning correlation | Compatibility + "industry" framing | 1 |
| [04](exp04_mutation_propagated_specs.md) | Mutation-coverage of propagated specs (P3 vs P3C) | Downstream value of propagation (RQ2/RQ4) | 2 |
| [05](exp05_discharge_propagated_clauses.md) | OpenJML discharge of propagated clauses at scale | Soundness of RQ4 output | 2 |
| [06](exp06_multimodel_replication.md) | Multi-model replication of the LLM study | External validity of RQ2 | 2 |
| [07](exp07_cost_study.md) | Specification cost: manual vs infer-and-review | The adoption premise itself | 3 |
| [08](exp08_heterogeneous_corpus.md) | Heterogeneous corpus (application/framework code) | External validity of RQ1 / adoption | 3 |
| [09](exp09_end_to_end_verification.md) | End-to-end client-against-dependency verification | RQ3 capability, made concrete | 3 |
| [10](exp10_developer_study.md) | Developer study of inferred-spec usefulness | The adoption claim, with humans | 3 |

## Shared infrastructure these plans assume

All plans build on the existing tool and harnesses:

- **Build:** `./mvnw clean package` → `target/jml-inferrer-1.0.0-jar-with-dependencies.jar`.
- **Inference pipeline:** `com.jml.inferrer.processor.CodebaseProcessor(collectMetrics, withCompositional)` →
  `JMLInferenceVisitor` → `MethodSpecificationInferrer` → `AnnotationToJMLConverter`.
- **Compositional pass:** `com.jml.inferrer.analysis.CompositionalAnalyzer.refineAll()` over a populated
  `SpecificationCache` and `CallGraph` (`CallGraphBuilder.buildFromCompilationUnits`).
- **LLM experiments:** `com.jml.inferrer.experiment.ExperimentRunner --phases ... --runs N --model M`.
- **Embedding:** `AsmJmlSpecWriter` / `AsmJmlSpecReader`, `MethodSpec`, `WriterConfig`.
- **Formal validation:** OpenJML ESC via Docker (`docker compose run --rm test`), `FormalVerificationTestBase`,
  `inferAndVerify()`; the forked OpenJML in `openjml-dev/`.
- **Mutation testing:** PIT (`mvn pitest:mutationCoverage`) in `experiment/commons-test-project`.
- **Corpora:** source jars resolved from the local Maven cache, as in
  `CompositionalAnalyzerCommonsLangExperimentTest`.

A new top-level package `com.jml.inferrer.experiment.*` (or a sibling
`evaluation/` module) is the natural home for the new harnesses; each plan names
the concrete classes it would add.
