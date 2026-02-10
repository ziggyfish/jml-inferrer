# Contributing to JML Specification Inferrer

Thank you for your interest in contributing to the JML Specification Inferrer project.

## Getting Started

1. Fork the repository at https://github.com/ziggyfish/jml-inferrer
2. Clone your fork: `git clone https://github.com/YOUR_USERNAME/jml-inferrer.git`
3. Create a feature branch: `git checkout -b feature/your-feature-name`
4. Make your changes
5. Run tests: `mvn test`
6. Commit your changes with a descriptive message
7. Push to your fork and submit a pull request

## Development Setup

### Prerequisites
- Java 21 or higher
- Maven 3.6 or higher

### Building
```bash
mvn clean package
```

### Running Tests
```bash
mvn test
```

### Testing with Examples
```bash
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar experiment/sample_code/
```

## Code Style

- Follow standard Java naming conventions
- Use meaningful variable and method names
- Add Javadoc comments for public methods
- Keep methods focused and reasonably sized

## Areas for Contribution

### Adding New Inference Patterns

The core inference logic is in `MethodSpecificationInferrer.java`. To add a new pattern:

1. Identify the code pattern you want to detect
2. Add an analysis method in `MethodSpecificationInferrer`
3. Call your new method from `inferPreconditions()`, `inferPostconditions()`, or `inferLoopInvariants()`
4. Add test cases in the `examples/` directory
5. Update documentation if the pattern is significant

### Improving Interprocedural Analysis

The specification cache and propagation logic can be enhanced:
- `SpecificationCache.java` - Stores method specifications
- `analyzeMethodCallPreconditions()` - Propagates caller requirements
- `analyzeMethodCallPostconditions()` - Propagates result properties

### Adding New Annotation Types

To add new JML-style annotations:

1. Create annotation class in `com.jml.inferrer.annotations`
2. Use `@Retention(RUNTIME)` for bytecode persistence
3. Add inference logic in `MethodSpecificationInferrer`
4. Update `JMLInferenceVisitor` to generate the annotation

### Testing on New Codebases

We welcome reports of running the tool on open-source projects:
- Document any crashes or incorrect specifications
- Submit issues with reproduction steps
- Share successful results and interesting findings

## Submitting Issues

When submitting an issue, please include:
- Java version (`java -version`)
- Maven version (`mvn -version`)
- Operating system
- Steps to reproduce
- Expected behavior
- Actual behavior
- Relevant code snippets or error messages

## Pull Request Guidelines

- Keep pull requests focused on a single change
- Include tests for new functionality
- Update documentation as needed
- Ensure all tests pass before submitting
- Write a clear PR description explaining the changes

## Questions

For questions about the codebase or contributing, please open a GitHub issue with the "question" label.

## License

By contributing, you agree that your contributions will be licensed under the Apache License 2.0.
