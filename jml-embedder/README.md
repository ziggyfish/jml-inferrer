# jml-embedder

Embeds and extracts JML specifications in:
- Java bytecode via the `@JmlSpec` annotation type (working)
- Maven classifier sidecar JARs in JML stub format (working)
- OpenAPI 3.x via `x-jml-*` extensions (forthcoming, Phase 2A.6)

**Status:** working ASM-based embedder/reader plus sidecar writer; 6/6 roundtrip tests green. The 5 corpus property tests in `RoundtripPropertyTest` remain disabled until Phase 2A.4 wires the inferrer's output through the embedder.

## Layout

```
jml-embedder/
  pom.xml                        Maven build descriptor
  src/main/java/com/jml/spec/
    JmlSpec.java                 the @JmlSpec annotation type (per-clause)
    JmlSpecs.java                container annotation for repeated @JmlSpec
    Kind.java                    enum of clause kinds
    MethodKey.java               record (className, methodName, descriptor)
    MethodSpec.java              record holding the per-method spec
    SignalsClause.java           record (exceptionType, condition)
    JmlCanonicaliser.java        canonical-form printer / parser (skeleton)
    read/JmlSpecReader.java      reader interface
    read/AsmJmlSpecReader.java   ASM-based bytecode reader (working)
    write/JmlSpecWriter.java     writer interface
    write/AsmJmlSpecWriter.java  ASM-based bytecode + sidecar writer (working)
  src/test/java/com/jml/spec/
    AsmRoundtripTest.java        roundtrip tests against in-memory class files (6/6 green)
    RoundtripPropertyTest.java   corpus-scale property tests (5/5 disabled — Phase 2A.4)
```

## Build (skeleton only)

The skeleton compiles cleanly under JDK 21 with `mvn -f jml-embedder/pom.xml compile`. Tests are `@Disabled` until the implementation lands.

This module is intentionally not added to the parent `jml-inferrer` build. Activation is deferred until Phase 2A.3 begins so that an in-progress skeleton does not break the inferrer's existing CI.

## Design references

- Format: `journal/rq2_embedding_design.md`
- Carrier survey: `journal/rq2_embedding_survey.md`
- Execution plan: `journal/rq2_rq4_execution_plan.md` §2A
