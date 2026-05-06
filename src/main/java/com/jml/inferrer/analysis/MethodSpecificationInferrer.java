package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Infers JML specifications (preconditions, postconditions, loop invariants) for methods.
 * Supports interprocedural analysis by using specifications from called methods.
 *
 * This class acts as a facade, delegating to specialized sub-analyzers.
 */
public class MethodSpecificationInferrer {

    private static final Logger logger = LoggerFactory.getLogger(MethodSpecificationInferrer.class);

    private final SpecificationCache cache;
    private final CallGraph callGraph;

    // Sub-analyzers
    private final PreconditionAnalyzer preconditionAnalyzer;
    private final PostconditionAnalyzer postconditionAnalyzer;
    private final LoopInvariantAnalyzer loopInvariantAnalyzer;
    private final PurityAnalyzer purityAnalyzer;
    private final ExceptionAnalyzer exceptionAnalyzer;
    private final AssignableAnalyzer assignableAnalyzer;
    private final ComplexityAnalyzer complexityAnalyzer;
    private final SwitchBitwiseAnalyzer switchBitwiseAnalyzer;
    private final InterproceduralAnalyzer interproceduralAnalyzer;
    private final OverflowPreconditionAnalyzer overflowPreconditionAnalyzer;
    private final BinarySearchPatternAnalyzer binarySearchPatternAnalyzer;

    /**
     * Creates a new inferrer with a specification cache and call graph for interprocedural analysis.
     *
     * @param cache The specification cache
     * @param callGraph The call graph for inheritance analysis (may be null)
     */
    public MethodSpecificationInferrer(SpecificationCache cache, CallGraph callGraph) {
        this.cache = cache != null ? cache : new SpecificationCache();
        this.callGraph = callGraph;

        // Initialize sub-analyzers
        this.interproceduralAnalyzer = new InterproceduralAnalyzer(this.cache);
        this.preconditionAnalyzer = new PreconditionAnalyzer();
        StringAnalyzer stringAnalyzer = new StringAnalyzer();
        CollectionAnalyzer collectionAnalyzer = new CollectionAnalyzer();
        ReturnValueAnalyzer returnValueAnalyzer = new ReturnValueAnalyzer();
        SymbolicExecutor symbolicExecutor = new SymbolicExecutor();
        this.postconditionAnalyzer = new PostconditionAnalyzer(
                stringAnalyzer, collectionAnalyzer, returnValueAnalyzer,
                interproceduralAnalyzer, symbolicExecutor);
        this.loopInvariantAnalyzer = new LoopInvariantAnalyzer();
        this.purityAnalyzer = new PurityAnalyzer();
        this.exceptionAnalyzer = new ExceptionAnalyzer();
        this.assignableAnalyzer = new AssignableAnalyzer();
        this.complexityAnalyzer = new ComplexityAnalyzer();
        this.switchBitwiseAnalyzer = new SwitchBitwiseAnalyzer();
        this.overflowPreconditionAnalyzer = new OverflowPreconditionAnalyzer();
        this.binarySearchPatternAnalyzer = new BinarySearchPatternAnalyzer();
    }

    /**
     * Creates a new inferrer with a specification cache for interprocedural analysis.
     *
     * @param cache The specification cache
     */
    public MethodSpecificationInferrer(SpecificationCache cache) {
        this(cache, null);
    }

    /**
     * Creates a new inferrer without interprocedural analysis.
     */
    public MethodSpecificationInferrer() {
        this(new SpecificationCache(), null);
    }

    /**
     * Infers specifications for a given method.
     *
     * @param methodDecl The method declaration to analyze
     * @return The inferred method specification
     */
    public MethodSpecification inferSpecification(MethodDeclaration methodDecl) {
        MethodSpecification spec = new MethodSpecification();

        // Single-pass AST collection — all sub-analyzers share this collector
        ASTCollector collector = ASTCollector.collect(methodDecl);

        // Basic JML specifications
        preconditionAnalyzer.inferPreconditions(methodDecl, spec, interproceduralAnalyzer, collector);
        overflowPreconditionAnalyzer.inferOverflowPreconditions(methodDecl, spec, collector);
        postconditionAnalyzer.inferPostconditions(methodDecl, spec, collector);
        loopInvariantAnalyzer.inferLoopInvariants(methodDecl, spec);
        // Binary-search bounds: emits 0 <= lo, lo <= hi + 1, hi <= arr.length - 1
        // for the canonical mid = lo + (hi - lo) / 2 shape. Runs after the generic
        // loop-invariant pass so it can append to existing invariants without
        // duplicating them (MethodSpecification.addLoopInvariant deduplicates).
        binarySearchPatternAnalyzer.analyze(methodDecl, spec);
        postconditionAnalyzer.promoteLoopInvariantsToPostconditions(methodDecl, spec);

        // Phase 1: Method properties
        purityAnalyzer.inferMethodPurity(methodDecl, spec, collector);
        exceptionAnalyzer.inferExceptionSpecifications(methodDecl, spec, collector);

        // Phase 2: Frame conditions and advanced specifications
        assignableAnalyzer.inferAssignableClauses(methodDecl, spec, collector);

        // Phase 3: Advanced properties
        complexityAnalyzer.inferComplexity(methodDecl, spec, collector);
        complexityAnalyzer.inferThreadSafety(methodDecl, spec, collector);

        // Phase 3: Stream API analysis
        inferStreamSpecifications(methodDecl, spec, collector);

        // Phase 3: Inheritance propagation
        propagateInheritedSpecifications(methodDecl, spec);

        // Phase 3: Generic type constraint analysis
        inferGenericTypeConstraints(methodDecl, spec);

        // Phase 4: Switch and bitwise analysis
        switchBitwiseAnalyzer.analyzeSwitchStatements(methodDecl, spec, collector);
        switchBitwiseAnalyzer.analyzeBitwiseOperations(methodDecl, spec, collector);

        // RQ3: Termination detection. Conservative: any direct self-recursion
        // or explicit infinite loop pattern flags the method as
        // potentially non-terminating. The CompositionalAnalyzer reads this
        // flag before propagating postconditions.
        spec.setTerminates(inferTermination(methodDecl));

        // Calculate overall confidence
        spec.calculateOverallConfidence();

        return spec;
    }

    /**
     * RQ3: conservative termination detection. Returns false if the method
     * contains direct self-recursion (an unbounded recursive call) or an
     * obvious infinite loop ({@code while(true)}, {@code for(;;)},
     * {@code do {} while(true)}). Otherwise returns true.
     *
     * <p>Recursive calls accompanied by an arithmetic decrement on an
     * argument (e.g. {@code factorial(n - 1)}) would benefit from a
     * decreases heuristic; without one, this returns false to stay sound.
     * Future work: integrate a {@code decreases} clause inferrer so
     * termination tracking is finer-grained.</p>
     */
    private boolean inferTermination(MethodDeclaration methodDecl) {
        String methodName = methodDecl.getNameAsString();
        for (com.github.javaparser.ast.expr.MethodCallExpr call
                : methodDecl.findAll(com.github.javaparser.ast.expr.MethodCallExpr.class)) {
            if (call.getNameAsString().equals(methodName)
                    && call.getScope().isEmpty()
                    && call.getArguments().size() == methodDecl.getParameters().size()) {
                return false;
            }
        }
        for (com.github.javaparser.ast.stmt.WhileStmt ws
                : methodDecl.findAll(com.github.javaparser.ast.stmt.WhileStmt.class)) {
            if (ws.getCondition().isBooleanLiteralExpr()
                    && ws.getCondition().asBooleanLiteralExpr().getValue()) {
                return false;
            }
        }
        for (com.github.javaparser.ast.stmt.DoStmt ds
                : methodDecl.findAll(com.github.javaparser.ast.stmt.DoStmt.class)) {
            if (ds.getCondition().isBooleanLiteralExpr()
                    && ds.getCondition().asBooleanLiteralExpr().getValue()) {
                return false;
            }
        }
        for (com.github.javaparser.ast.stmt.ForStmt fs
                : methodDecl.findAll(com.github.javaparser.ast.stmt.ForStmt.class)) {
            if (fs.getCompare().isEmpty()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Infers specifications from Stream API operations.
     */
    private void inferStreamSpecifications(MethodDeclaration methodDecl, MethodSpecification spec,
                                            ASTCollector collector) {
        StreamOperationAnalyzer streamAnalyzer = new StreamOperationAnalyzer();
        Set<String> streamSpecs = streamAnalyzer.inferStreamPostconditions(methodDecl, collector);
        for (String postcond : streamSpecs) {
            spec.addPostcondition(postcond, MethodSpecification.ConfidenceLevel.MEDIUM);
        }
    }

    /**
     * Propagates specifications from parent classes and interfaces.
     */
    private void propagateInheritedSpecifications(MethodDeclaration methodDecl, MethodSpecification spec) {
        if (callGraph == null) {
            return;
        }

        String methodSignature = buildMethodSignatureForCache(methodDecl);
        String overriddenMethod = callGraph.getOverriddenMethod(methodSignature);

        if (overriddenMethod != null) {
            MethodSpecification parentSpec = cache.get(overriddenMethod);

            if (parentSpec != null) {
                String source = extractClassName(overriddenMethod);

                for (String precond : parentSpec.getPreconditions()) {
                    if (!spec.getPreconditions().contains(precond)) {
                        spec.addInheritedPrecondition(precond, source);
                        logger.debug("Inherited precondition from {}: {}", source, precond);
                    }
                }

                for (String postcond : parentSpec.getPostconditions()) {
                    if (!spec.getPostconditions().contains(postcond)) {
                        spec.addInheritedPostcondition(postcond, source);
                        logger.debug("Inherited postcondition from {}: {}", source, postcond);
                    }
                }
            }
        }

        String className = getClassName(methodDecl);
        if (className != null) {
            Set<String> interfaces = callGraph.getAllImplementedInterfaces(className);
            for (String iface : interfaces) {
                String ifaceMethod = iface + "." + methodDecl.getNameAsString();
                MethodSpecification ifaceSpec = cache.get(ifaceMethod);

                if (ifaceSpec != null) {
                    for (String precond : ifaceSpec.getPreconditions()) {
                        if (!spec.getPreconditions().contains(precond)) {
                            spec.addInheritedPrecondition(precond, iface);
                        }
                    }
                    for (String postcond : ifaceSpec.getPostconditions()) {
                        if (!spec.getPostconditions().contains(postcond)) {
                            spec.addInheritedPostcondition(postcond, iface);
                        }
                    }
                }
            }
        }
    }

    /**
     * Analyzes generic type parameters and constraints.
     */
    private void inferGenericTypeConstraints(MethodDeclaration methodDecl, MethodSpecification spec) {
        methodDecl.getTypeParameters().forEach(typeParam -> {
            String typeParamName = typeParam.getNameAsString();

            typeParam.getTypeBound().forEach(bound -> {
                String boundName = bound.asString();
                if (!boundName.equals("Object")) {
                    methodDecl.getParameters().forEach(param -> {
                        String paramType = param.getType().asString();
                        if (paramType.equals(typeParamName) || paramType.equals(typeParamName + "[]")) {
                            spec.addPrecondition(param.getNameAsString() + " instanceof " + boundName,
                                    MethodSpecification.ConfidenceLevel.MEDIUM);
                        }
                    });
                }
            });
        });

        methodDecl.getParameters().forEach(param -> {
            String paramType = param.getType().asString();

            if (paramType.contains("Comparable")) {
                if (!param.getType().isPrimitiveType()) {
                    spec.addPrecondition(param.getNameAsString() + " instanceof Comparable",
                            MethodSpecification.ConfidenceLevel.HIGH);
                }
            }

            if (paramType.matches(".*<\\? extends \\w+>.*") || paramType.matches(".*<\\? super \\w+>.*")) {
                if (!param.getType().isPrimitiveType()) {
                    spec.addPrecondition(param.getNameAsString() + " != null",
                            MethodSpecification.ConfidenceLevel.HIGH);
                }
            }
        });
    }

    private String extractWildcardBound(String type, String keyword) {
        int idx = type.indexOf("? " + keyword + " ");
        if (idx >= 0) {
            int start = idx + 2 + keyword.length() + 1;
            int end = type.indexOf('>', start);
            if (end > start) {
                return type.substring(start, end).trim();
            }
        }
        return null;
    }

    private String buildMethodSignatureForCache(MethodDeclaration methodDecl) {
        StringBuilder sig = new StringBuilder();
        String className = getClassName(methodDecl);
        if (className != null) {
            sig.append(className).append(".");
        }
        sig.append(methodDecl.getNameAsString());
        return sig.toString();
    }

    private String getClassName(MethodDeclaration methodDecl) {
        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(c -> c.getNameAsString())
                .orElse(null);
    }

    private String extractClassName(String methodSignature) {
        int dotIdx = methodSignature.lastIndexOf('.');
        if (dotIdx > 0) {
            return methodSignature.substring(0, dotIdx);
        }
        return methodSignature;
    }
}
