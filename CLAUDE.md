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

### File Size Limits

**No source file should exceed 500 lines.** When a file grows beyond this limit, split it into multiple files by logical grouping. For the inference engine specifically:
- Split large classes into focused sub-classes (e.g., `PreconditionAnalyzer`, `PostconditionAnalyzer`, `LoopInvariantAnalyzer`)
- Use composition or delegation rather than monolithic classes
- When refactoring a large file, break it into smaller files first before making structural changes

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

## Journal Article Quality Gates

**Trigger:** every time any file under `journal/article1/` or `journal/article2/` is modified (any `.tex`, `.bib`, `.cls`, or referenced figure file), all seven publication-readiness passes below must be run before reporting completion to the user. The user has explicitly accepted the cost.

The user has been told this will take ~2 hours per edit. Honour the directive — do not skip passes for being expensive, slow, or apparently unnecessary. If a pass returns identical output to a recent run, say so explicitly rather than silently skipping.

For each pass, report: (a) what was checked, (b) what was found, (c) what was fixed automatically vs.\ flagged for the user. End the overall response with a one-line summary: `[passes 1-7 complete; N issues found, M fixed, K flagged]`.

### Pass 1 — Build integrity

- Run `pdflatex` + `bibtex` + `pdflatex` + `pdflatex` from the article directory
- Confirm: zero LaTeX warnings (not just zero errors), zero BibTeX warnings, no undefined citations / references / labels, no multiply-defined labels, all `\input{}` files exist
- Report final page count

### Pass 2 — Internal consistency

- Every figure and table is referenced in text via `\ref` (no orphan figures/tables)
- Every figure and table is referenced *before* it appears physically
- Every numeric claim in the abstract appears in the body with the same value
- Every numeric claim in the conclusion appears in the body with the same value
- Section ordering matches what the introduction promises
- Every `\ref{sec:...}` points where the surrounding prose claims
- Every section is reached from at least one navigational reference, or has a clear independent purpose

### Pass 3 — Bibliographic integrity

- Every `\cite{}` key resolves to a `references.bib` entry
- Every `references.bib` entry is cited at least once (no orphans)
- Author lists complete (flag any `and others` for paper-of-record entries)
- For every entry: title, year, venue match the actual publication (verify via web for entries added or modified since the last Pass 3 run)
- DOIs resolve where present
- No citations to predatory venues or retracted papers
- Citation style consistent with target venue (Wiley/JSEP)

### Pass 4 — Register and prose audit

- One spelling convention throughout (British English for this article)
- Tense consistency within sections (past for completed work, present for the article's claims)
- Every acronym defined on first use
- "the tool" / "we" / "JML-Inferrer" / "the system" usage consistent
- No colloquialisms or marketing language ("seamlessly", "powerful", "leverage", "robust")
- No bold for emphasis in body text where italic is the convention
- No double spaces, em-dash overuse, or LaTeX-rendered straight quotes ("...")
- Title, abstract, introduction, and conclusion all answer the same question with the same framing

### Pass 5 — Empirical defensibility

- Every statistical claim has effect size, confidence interval, p-value, and (where multiple comparisons) correction
- Sample size justified or power-analysed
- Variance / standard deviation reported alongside means
- Baselines described in enough detail to reproduce
- Random seeds, model versions, temperature, and full prompts disclosed (or pointed to in supplementary material)
- Threats-to-validity section addresses the obvious counterarguments
- Categorisation criteria are operational

Report: missing items only. Do not vouch for whether the experiment was sound — that is outside scope.

### Pass 6 — Reviewer red-team

Read the article as an adversarial reviewer. Produce a list of likely Reviewer 2 objections, ordered by severity (Critical / Major / Minor). For each:
- The objection in one sentence
- Where in the article it would land
- What the rebuttal would need to say
- Whether the rebuttal needs new experiments or can be addressed by editing alone

This pass produces text only. Do not edit the article in response unless explicitly asked.

### Pass 7 — Submission packaging

- Conforms to target venue's LaTeX class (Wiley template for JSEP)
- Author affiliations and ORCIDs present
- Conflict-of-interest statement present
- Author contributions (CRediT taxonomy) present
- Data accessibility statement present
- Acknowledgments and funding present
- Anonymisation done correctly if double-blind submission
- Replication package is referenced and the URL resolves
- Cover letter present in the article directory (or flagged as missing)
- Suggested reviewers / non-reviewers list present (or flagged as missing)
