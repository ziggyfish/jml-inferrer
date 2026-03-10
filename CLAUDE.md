# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

JML Specification Inferrer - A Java 21 application that automatically analyzes Java codebases and generates JML (Java Modeling Language) specifications by analyzing the Abstract Syntax Tree (AST) using JavaParser.

## Build and Development Commands

### Build the project
```bash
mvn clean package
```
Creates two JARs in `target/`:
- `jml-inferrer-1.0.0.jar` - Standard JAR
- `jml-inferrer-1.0.0-jar-with-dependencies.jar` - Executable JAR with all dependencies

### Run the application
```bash
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar <path-to-java-codebase>
```

### Quick test with example
```bash
./run-example.sh   # Unix/Linux/Mac
run-example.bat    # Windows
```
This builds the project and runs it on the `experiment/sample_code/` directory.

### Running tests
```bash
mvn test
```

## Architecture Overview

### Processing Flow
The application follows a visitor pattern-based pipeline:

1. **JMLInferrerApp** (entry point) → receives target codebase path
2. **CodebaseProcessor** → recursively walks directory tree, finds all `.java` files
3. **JavaParser** → parses each file into CompilationUnit (AST)
4. **JMLInferenceVisitor** → traverses AST, visits each MethodDeclaration
5. **MethodSpecificationInferrer** → analyzes method to infer specifications
6. **MethodSpecification** → stores inferred preconditions, postconditions, loop invariants
7. **JMLInferenceVisitor** → injects JML as Javadoc comments back into AST
8. **CodebaseProcessor** → writes modified AST back to original file

### Key Components

**Analysis Package** (`com.jml.inferrer.analysis`)
- `MethodSpecificationInferrer`: Core inference engine that analyzes method AST nodes
  - Contains inner visitor classes: `NullCheckVisitor` and `LoopInvariantVisitor`
  - Uses heuristic-based pattern matching on AST nodes to detect constraints
  - Infers three types of specifications:
    - **Preconditions**: from parameter types, null checks, numeric comparisons, early validation
    - **Postconditions**: from return statements, field modifications, return type patterns
    - **Loop invariants**: from for/while/foreach loop bounds and accumulator patterns

**Visitor Package** (`com.jml.inferrer.visitor`)
- `JMLInferenceVisitor`: AST traversal coordinator
  - Extends `VoidVisitorAdapter<Void>` from JavaParser
  - Checks if methods should be processed (skips abstract, no-body, already-annotated)
  - Delegates to `MethodSpecificationInferrer` for analysis
  - Formats and injects JML as JavadocComment nodes
  - Preserves existing Javadoc comments by appending to them

**Processor Package** (`com.jml.inferrer.processor`)
- `CodebaseProcessor`: File system and parsing orchestrator
  - Configures JavaParser with Java 21 language level
  - Uses `Files.walk()` for recursive directory traversal
  - Tracks modifications via `JMLInferenceVisitor.hasModifications()`
  - Only writes files back if modifications occurred

**Model Package** (`com.jml.inferrer.model`)
- `MethodSpecification`: Simple data holder with three lists
  - Preconditions, postconditions, loop invariants
  - No logic, just accumulation and retrieval

### Development Philosophy

**This is a research product.** Always prefer the correct solution over the easy solution. When inference produces invalid JML:
- **Fix the inference to produce valid JML**, don't just delete the inference code
- If a pattern can't be expressed in JML, replace it with the closest valid JML expression (e.g., replace natural language with a valid JML property that captures part of the intent)
- Only remove inference as a last resort when no valid JML can be generated for the pattern
- Every inferred specification must be syntactically valid JML — no natural language, no undefined variables, no expressions that are false at loop exit

### Important Design Decisions

**Non-destructive**: Only adds JML to methods without existing specifications. Methods with `@requires`, `@ensures`, or `@loop_invariant` are skipped.

**Heuristic-based**: Uses pattern matching on AST nodes rather than formal program analysis. Specifications may need manual review.

**In-place modification**: Directly modifies source files in the codebase path. No backup is created automatically.

**Java 21 required**: Uses JavaParser configured for Java 21 language features (switch expressions, pattern matching, etc.).

### Extending the Inference Engine

To add new inference capabilities:

1. Add analysis methods in `MethodSpecificationInferrer.java`
2. Create new visitor classes if traversing specific AST node types (see `NullCheckVisitor`, `LoopInvariantVisitor`)
3. Update `inferPreconditions()`, `inferPostconditions()`, or `inferLoopInvariants()` to call new analyzers
4. Test with various Java code patterns in `experiment/sample_code/`

### Testing Requirements

**Every code change must include verification tests.** When fixing bugs or adding features to the inference engine, always add tests that verify the inferred specifications are correct. There are two tiers of tests:

- **Analysis tests** (`src/test/java/com/jml/inferrer/analysis/`): Unit tests that call `MethodSpecificationInferrer` directly and assert on the inferred preconditions, postconditions, loop invariants, and assignable clauses. Use `InferrerTestBase` as the base class. These run without OpenJML.
- **Verification tests** (`src/test/java/com/jml/inferrer/verification/`): End-to-end tests that run the full pipeline (infer → annotate → convert → OpenJML ESC) and verify that OpenJML accepts the inferred specifications. Use `FormalVerificationTestBase` as the base class. These require OpenJML (run via Docker: `docker compose run test`).

When changing inference logic:
1. Write an analysis test that checks the inferred spec content (e.g., assert a precondition contains `arr != null`)
2. Write a verification test using `inferAndVerify()` that proves the inferred spec is formally valid via OpenJML
3. If fixing an invalid inference bug, add a regression test in `InvalidInferenceRegressionTest.java` that asserts the invalid spec is no longer generated
4. Prefer `inferAndVerify()` over `verifyMethod()` — the tool's purpose is to **infer** specifications from code, so tests should exercise the full inference pipeline, not bypass it with hand-written JML
5. Keep each test class to **30 tests or fewer**. When a suite grows beyond 30 tests, split it into multiple classes by logical grouping (e.g., `PreconditionInferenceTest` → `PreconditionNullCheckTest`, `PreconditionBoundsTest`)

### Logging

Uses SLF4J with Logback:
- Console: INFO level progress messages
- File: DEBUG level detailed logs in `jml-inferrer.log`
- Configuration: `src/main/resources/logback.xml`
