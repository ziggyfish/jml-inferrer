# JML Specification Inferrer

A Java application that automatically analyzes Java codebases and generates JML (Java Modeling Language) specifications. The tool uses AST-based pattern matching to infer behavioral contracts including preconditions, postconditions, and loop invariants.

## Key Features

### Automated Specification Inference
- **Precondition Inference**: Detects parameter constraints, null checks, value ranges, and validation patterns
- **Postcondition Inference**: Analyzes return values, field modifications, side effects, and result properties
- **Loop Invariant Inference**: Identifies invariants in for, while, and foreach loops

### Interprocedural Analysis
- **Two-Pass Analysis**: First pass builds specification cache, second pass propagates specifications
- **Specification Propagation**: Automatically inherits contracts from called methods
- **Transitive Inference**: Propagates specifications through multiple levels of method calls

### Runtime Annotations
- **Compiled Specifications**: Specifications encoded as Java annotations with `@Retention(RUNTIME)`
- **Bytecode Integration**: Specifications compiled into .class files and JAR artifacts
- **Reflection Support**: Queryable at runtime for dynamic verification

## Requirements

- Java 21 or higher
- Maven 3.6 or higher

## Building the Project

```bash
mvn clean package
```

This creates two JARs in `target/`:
- `jml-inferrer-1.0.0.jar` - Standard JAR
- `jml-inferrer-1.0.0-jar-with-dependencies.jar` - Executable JAR with all dependencies

## Usage

### Basic Usage

Run on any Java codebase:

```bash
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar <path-to-java-codebase>
```

### Example

```bash
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar /path/to/your/project/src
```

The tool will:
1. Scan all `.java` files recursively
2. Load existing specifications from compiled `.class` files (if available)
3. **Pass 1**: Analyze each method and build specification cache
4. **Pass 2**: Re-analyze with interprocedural propagation
5. Add runtime annotations to source files

## JML Annotations Generated

### Preconditions (`@Requires`)

Inferred from:
- **Null checks**: `if (param == null) throw ...` → `@Requires("param != null")`
- **Numeric constraints**: `if (value < 0) throw ...` → `@Requires("value >= 0")`
- **String requirements**: `str.charAt(0)` → `@Requires("str.length() > 0")`
- **Array/Collection bounds**: `arr[i]` → `@Requires("arr.length > i")`
- **Parameter relationships**: `if (a > b) throw ...` → `@Requires("a <= b")`

### Postconditions (`@Ensures`)

Inferred from:
- **Non-null returns**: Always returns non-null → `@Ensures("\result != null")`
- **Numeric properties**: `return Math.abs(x)` → `@Ensures("\result >= 0")`
- **Result relationships**: `return a + b` → `@Ensures("\result == a + b")`
- **String properties**: `return s.toUpperCase()` → `@Ensures("\result.length() == s.length()")`
- **Collection sizes**: Filtering → `@Ensures("\result.size() <= input.size()")`
- **Field modifications**: `this.count = value` → `@Ensures("this.count == value")`
- **Builder pattern**: `return this` → `@Ensures("\result == this")`

### Loop Invariants (`@LoopInvariant`)

Inferred from:
- **Loop counters**: `for (int i = 0; i < n; i++)` → `@LoopInvariant("i >= 0 && i <= n")`
- **Array traversal**: `for (String s : array)` → `@LoopInvariant("s is element of array")`
- **Accumulators**: Growing values → `@LoopInvariant("sum >= 0")`

## Example: Interprocedural Analysis

**Input Code:**

```java
public class MathUtils {
    // Helper method
    public int abs(int value) {
        if (value < 0) {
            return -value;
        }
        return value;
    }

    // Uses helper
    public int distance(int a, int b) {
        int diff = a - b;
        return abs(diff);
    }
}
```

**Generated Output:**

```java
public class MathUtils {
    @com.jml.inferrer.annotations.Requires("value < 0")
    @com.jml.inferrer.annotations.Ensures("\\result >= 0")
    public int abs(int value) {
        if (value < 0) {
            return -value;
        }
        return value;
    }

    @com.jml.inferrer.annotations.Ensures("\\result >= 0")  // Inherited from abs()
    public int distance(int a, int b) {
        int diff = a - b;
        return abs(diff);
    }
}
```

## Project Structure

```
src/
├── main/
│   ├── java/
│   │   └── com/jml/inferrer/
│   │       ├── JMLInferrerApp.java              # Main entry point
│   │       ├── annotations/                      # Runtime annotations
│   │       │   ├── Requires.java
│   │       │   ├── Ensures.java
│   │       │   └── LoopInvariant.java
│   │       ├── analysis/
│   │       │   ├── MethodSpecificationInferrer.java    # Core inference
│   │       │   ├── SpecificationCache.java             # Interprocedural cache
│   │       │   └── ClassFileSpecificationReader.java   # Bytecode reader
│   │       ├── model/
│   │       │   └── MethodSpecification.java     # Specification data model
│   │       ├── processor/
│   │       │   └── CodebaseProcessor.java       # Two-pass processing
│   │       └── visitor/
│   │           └── JMLInferenceVisitor.java     # AST visitor
│   └── resources/
│       └── logback.xml                          # Logging configuration
├── test/
│   └── java/
├── experiment/                                   # Evaluation on Apache Commons Lang
│   ├── commons-lang-subset/                     # Annotated source files
│   └── sample_code/                             # Example Java files
└── paper/                                        # Research paper
    └── journal/                                  # Journal article LaTeX source
```

## Research Paper

A comprehensive research paper is included in the `paper/journal/` directory, covering:
- Theoretical foundation (Weakest Precondition and Strongest Postcondition logic)
- Implementation details and algorithm specification
- Evaluation results using mutation testing
- Comparison of LLM-based test generation with JML specifications

To compile the paper:
```bash
cd paper/journal
pdflatex journal_article.tex
bibtex journal_article
pdflatex journal_article.tex
pdflatex journal_article.tex
```

## How It Works

### Architecture Overview

```
┌─────────────────────────────────────────────────────────┐
│  Phase 0: Load Existing Specifications                  │
│  - Scan target/classes, build/classes for .class files │
│  - Use reflection to read @Requires/@Ensures            │
│  - Populate specification cache                         │
└─────────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────────┐
│  Phase 1: Intraprocedural Analysis                      │
│  - Parse each method's AST                              │
│  - Infer specs from code patterns (null checks, etc.)   │
│  - Cache specifications by method signature             │
└─────────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────────┐
│  Phase 2: Interprocedural Propagation                   │
│  - For each method call, lookup callee specs            │
│  - Propagate preconditions to caller parameters         │
│  - Propagate postconditions to caller results           │
└─────────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────────┐
│  Phase 3: Annotation Generation                         │
│  - Add @Requires/@Ensures/@LoopInvariant                │
│  - Write modified AST back to source files              │
│  - Specifications compile into bytecode                 │
└─────────────────────────────────────────────────────────┘
```

### Theoretical Foundation

The tool is grounded in **Hoare logic**:

**Weakest Precondition (WP)**: Given postcondition Q and statement S, find the most general precondition P:
```
{P} S {Q}  where P = wp(S, Q)
```

**Strongest Postcondition (SP)**: Given precondition P and statement S, find the most specific postcondition Q:
```
{P} S {Q}  where Q = sp(P, S)
```

Example:
```java
// Statement: if (x < 0) throw new Exception()
// Desired postcondition: true (no exception)
// Inferred precondition: wp(if..., true) = (x >= 0)
// Generated: @Requires("x >= 0")
```

## Evaluation

The tool was evaluated on **Apache Commons Lang 3.17.0** with mutation testing using PiTest.

### Specification Inference Results

| Metric | Value |
|--------|-------|
| Total Methods Analyzed | 312 |
| Preconditions Inferred | 258 |
| Postconditions Inferred | 141 |
| Loop Invariants Inferred | 138 |
| Total Annotations | 3,140 |
| Processing Time | < 10 seconds |

### LLM Test Generation with JML Specifications

| Prompt Strategy | Mutation Score |
|-----------------|----------------|
| P1: Baseline (no context) | 26% |
| P2: Source + Guidance | 89% |
| P3: Source + JML Specs | 69% |
| P4: Source + JML + Guidance | 100% |

## Limitations

1. **Heuristic-Based**: Uses pattern matching, not complete formal verification
2. **No Aliasing Analysis**: Doesn't track pointer aliasing for mutable parameters
3. **Basic Loop Analysis**: Complex multi-variable loops need manual review
4. **No Exception Specs**: Doesn't infer `signals` clauses yet

## Advanced Usage

### Customizing Inference Rules

Edit `src/main/java/com/jml/inferrer/analysis/MethodSpecificationInferrer.java`:

```java
// Add custom precondition inference
private void analyzeCustomPattern(MethodDeclaration method, Set<String> preconditions) {
    // Your custom logic here
}
```

### Integrating with Build Systems

**Maven** (`pom.xml`):
```xml
<build>
    <plugins>
        <plugin>
            <groupId>org.codehaus.mojo</groupId>
            <artifactId>exec-maven-plugin</artifactId>
            <executions>
                <execution>
                    <phase>generate-sources</phase>
                    <goals>
                        <goal>java</goal>
                    </goals>
                    <configuration>
                        <mainClass>com.jml.inferrer.JMLInferrerApp</mainClass>
                        <arguments>
                            <argument>${project.basedir}/src/main/java</argument>
                        </arguments>
                    </configuration>
                </execution>
            </executions>
        </plugin>
    </plugins>
</build>
```

**Gradle** (`build.gradle`):
```gradle
task inferJML(type: JavaExec) {
    classpath = files('path/to/jml-inferrer-1.0.0-jar-with-dependencies.jar')
    main = 'com.jml.inferrer.JMLInferrerApp'
    args = ["${projectDir}/src/main/java"]
}

compileJava.dependsOn inferJML
```

## Contributing

Contributions are welcome. To extend the tool:

1. **Add Inference Heuristics**: Modify `MethodSpecificationInferrer.java`
2. **Improve Propagation**: Enhance `analyzeMethodCallPreconditions()` and `analyzeMethodCallPostconditions()`
3. **Add Annotation Types**: Create new annotations in `annotations/` package
4. **Test on Real Libraries**: Run on popular open-source projects and report results

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

## License

This project is licensed under the Apache License 2.0. See [LICENSE](LICENSE) for details.

## Citation

If you use this tool in academic research:

```bibtex
@article{jmlinferrer2025,
  title={Automated JML Specification Inference via Pattern Matching for Enhanced LLM-Based Test Generation},
  author={JML-Inferrer Contributors},
  year={2025},
  note={Available at: https://github.com/ziggyfish/jml-inferrer}
}
```

---

**Built with**: JavaParser, SLF4J, Java 21

**Evaluated on**: Apache Commons Lang 3.17.0
