package com.jml.inferrer.analysis;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.BeforeEach;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Base class providing shared test infrastructure for MethodSpecificationInferrer tests.
 */
abstract class InferrerTestBase {

    protected MethodSpecificationInferrer inferrer;
    protected JavaParser parser;

    @BeforeEach
    void setUp() {
        inferrer = new MethodSpecificationInferrer();
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        parser = new JavaParser(config);
    }

    /**
     * Parses the given class source and returns the MethodDeclaration with the specified name.
     */
    protected MethodDeclaration parseMethod(String classSource, String methodName) {
        ParseResult<CompilationUnit> result = parser.parse(classSource);
        assertTrue(result.isSuccessful(), "Parsing failed: " + result.getProblems());
        CompilationUnit cu = result.getResult().orElseThrow();
        Optional<MethodDeclaration> method = cu.findAll(MethodDeclaration.class).stream()
                .filter(m -> m.getNameAsString().equals(methodName))
                .findFirst();
        assertTrue(method.isPresent(), "Method '" + methodName + "' not found in parsed source");
        return method.get();
    }

    /**
     * Parses and infers specifications for a method in the given class source.
     */
    protected MethodSpecification infer(String classSource, String methodName) {
        return inferrer.inferSpecification(parseMethod(classSource, methodName));
    }

    /**
     * Checks if any string in the list contains all the given substrings.
     */
    protected boolean anyContainsAll(List<String> specs, String... substrings) {
        return specs.stream().anyMatch(s -> {
            for (String sub : substrings) {
                if (!s.contains(sub)) return false;
            }
            return true;
        });
    }

    /**
     * Checks if any string in the list contains none of the given substrings.
     */
    protected boolean noneContains(List<String> specs, String substring) {
        return specs.stream().noneMatch(s -> s.contains(substring));
    }
}
