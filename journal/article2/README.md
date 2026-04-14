# Article 2: Specification-Guided LLM Test Generation for Service-Boundary Code

**Status:** planned follow-up study. Not yet started.

## Premise

Article 1 (`../article1/`) demonstrates that inferred JML specifications materially improve LLM-generated unit tests on a general-purpose Java corpus (Apache Commons Lang). This follow-up tests whether the same claim holds, or compounds, on **service-boundary code**: methods that call REST endpoints or RPC stubs.

The hypothesis is that the gain reported in Article 1 is *larger* in this setting because:

1. The oracle problem is most acute at service boundaries — signatures convey nothing about status codes, retry semantics, idempotency, or failure modes.
2. Signature-only LLM test generation collapses into mock-the-call assertions that test the wrapper, not the contract.
3. Inferred specifications can capture status-code preconditions, exception hierarchies, retry assumptions, and timeout behaviour that are otherwise invisible to the model.

## Required Prerequisites

This article cannot be written until the following are in place:

1. **A distributed-systems subject corpus.** Candidates: a Spring Boot REST client library, an OpenFeign-based client, a gRPC-Java sample service, or an Apache Dubbo client. Selection criteria: real service-call code, not toy examples; sufficient method count for statistical analysis; permissive licence; existing test suite for baseline comparison.

2. **Engine extensions to JML-Inferrer** for service-boundary patterns:
   - HTTP status-code preconditions (`@RequestMapping`, `@GetMapping`, `ResponseEntity`)
   - JAX-RS / Spring MVC parameter constraints (`@PathVariable`, `@RequestParam`, `@RequestBody`)
   - Exception hierarchies (`RestClientException`, `TimeoutException`, gRPC `StatusRuntimeException`)
   - Idempotency markers and retry assumptions
   - Mock-friendly postconditions for service stubs

3. **A re-run of the P1--P4 evaluation** on the new corpus, with mutation operators that include service-relevant mutations (status-code substitution, retry-count alteration, exception-type swapping).

## Open Questions for the Study

- Does the P1 baseline collapse further on service-call code (i.e.\ does the relative gain grow)?
- Are domain-specific specifications (status codes, retry policies) more valuable than general specifications, or do they add comparable lift?
- How does the LLM handle mocked vs.\ real service calls when given specifications?
- Does the OpenJML validation layer transfer cleanly, or do service-call patterns break it?

## Estimated Effort

Roughly 2--4 months from corpus selection to a draftable manuscript, contingent on the engine extensions in (2) being non-trivial.

## Relationship to Article 1

Article 1 establishes the general claim and the methodology (P1--P4 design, mutation testing, Cohen's $d$ analysis); Article 2 inherits both and applies them to the service-boundary setting. Article 1 should be submitted, and ideally accepted, before Article 2 is started --- the second paper's contribution is sharper if it can cite a published version of the first.
