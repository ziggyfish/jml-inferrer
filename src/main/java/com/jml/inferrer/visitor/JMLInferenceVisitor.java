package com.jml.inferrer.visitor;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.jml.inferrer.analysis.*;
import com.jml.inferrer.model.ClassSpecification;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Set of all JML-related annotation names that indicate a method already has specifications.
 * When any of these are present, the method should be skipped to avoid duplicates.
 */

/**
 * AST Visitor that traverses Java classes and methods to infer JML specifications.
 * Performs two-pass analysis for interprocedural specification inference.
 */
public class JMLInferenceVisitor extends VoidVisitorAdapter<Void> {

    private static final Logger logger = LoggerFactory.getLogger(JMLInferenceVisitor.class);

    /**
     * Set of all JML-related annotation names that indicate a method already has specifications.
     * When any of these are present, the method should be skipped to avoid duplicates.
     */
    private static final Set<String> JML_ANNOTATION_NAMES = Set.of(
        // Core JML specifications
        "Requires", "Ensures", "LoopInvariant", "Signals", "Assignable",
        // Method properties
        "Pure", "Observer", "Mutator", "ThreadSafe",
        // Nullability
        "NonNull", "Nullable",
        // Class-level
        "Invariant", "Immutable", "MustCall",
        // Complexity
        "Complexity",
        // Inference control
        "SkipInference",
        // Confidence and inheritance
        "Confidence", "InheritedSpec"
    );

    private final MethodSpecificationInferrer specificationInferrer;
    private final ClassInvariantInferrer classInvariantInferrer;
    private final NullabilityAnalyzer nullabilityAnalyzer;
    private final SpecificationCache cache;
    private final CallGraph callGraph;
    private boolean hasModifications = false;
    private String currentClassName = "";
    private boolean currentClassSkipInference = false;

    // For two-pass analysis
    private final Map<MethodDeclaration, String> methodSignatures = new HashMap<>();
    private boolean isSecondPass = false;

    public JMLInferenceVisitor() {
        this(new SpecificationCache(), null);
    }

    /**
     * Creates a new visitor with a specification cache and optional call graph.
     *
     * @param cache The specification cache for interprocedural analysis
     * @param callGraph The call graph for inheritance and call analysis (may be null)
     */
    public JMLInferenceVisitor(SpecificationCache cache, CallGraph callGraph) {
        this.cache = cache != null ? cache : new SpecificationCache();
        this.callGraph = callGraph;
        this.specificationInferrer = new MethodSpecificationInferrer(this.cache, this.callGraph);
        this.classInvariantInferrer = new ClassInvariantInferrer();
        this.nullabilityAnalyzer = new NullabilityAnalyzer();
    }

    /**
     * Enables second-pass mode for interprocedural analysis.
     * Call this after the first pass to re-analyze methods with cached specifications.
     */
    public void enableSecondPass() {
        this.isSecondPass = true;
        logger.debug("Enabled second-pass interprocedural analysis with {} cached specs", cache.size());
    }

    @Override
    public void visit(ClassOrInterfaceDeclaration classDecl, Void arg) {
        String previousClassName = currentClassName;
        boolean previousSkipInference = currentClassSkipInference;

        currentClassName = classDecl.getNameAsString();
        currentClassSkipInference = hasSkipInferenceAnnotation(classDecl);

        logger.debug("Analyzing class: {}{}", currentClassName,
                currentClassSkipInference ? " (skipped - @SkipInference)" : "");

        // Skip class-level analysis if @SkipInference is present
        if (currentClassSkipInference) {
            super.visit(classDecl, arg);
            currentClassName = previousClassName;
            currentClassSkipInference = previousSkipInference;
            return;
        }

        // Analyze class-level specifications
        if (!isSecondPass) {
            ClassSpecification classSpec = classInvariantInferrer.inferClassSpecification(classDecl);

            if (classSpec.hasSpecifications()) {
                addClassAnnotations(classDecl, classSpec);
                hasModifications = true;
            }

            // Analyze fields
            analyzeFields(classDecl);
        }

        super.visit(classDecl, arg);
        currentClassName = previousClassName;
        currentClassSkipInference = previousSkipInference;
    }

    /**
     * Checks if a class has the @SkipInference annotation.
     */
    private boolean hasSkipInferenceAnnotation(ClassOrInterfaceDeclaration classDecl) {
        return classDecl.getAnnotations().stream()
            .anyMatch(ann -> {
                String name = ann.getNameAsString();
                return name.equals("SkipInference") || name.endsWith(".SkipInference");
            });
    }

    /**
     * Analyze and annotate fields with nullability information.
     */
    private void analyzeFields(ClassOrInterfaceDeclaration classDecl) {
        for (FieldDeclaration field : classDecl.getFields()) {
            for (VariableDeclarator var : field.getVariables()) {
                if (var.getType().isReferenceType()) {
                    NullabilityAnalyzer.NullState nullState =
                            nullabilityAnalyzer.analyzeFieldNullability(field, var);

                    if (nullState == NullabilityAnalyzer.NullState.NON_NULL) {
                        field.addMarkerAnnotation("com.jml.inferrer.annotations.NonNull");
                        hasModifications = true;
                    } else if (nullState == NullabilityAnalyzer.NullState.MAYBE_NULL) {
                        field.addMarkerAnnotation("com.jml.inferrer.annotations.Nullable");
                        hasModifications = true;
                    }
                }

                // Check immutability
                if (field.isFinal() && field.getVariables().stream().allMatch(v -> v.getInitializer().isPresent())) {
                    field.addMarkerAnnotation("com.jml.inferrer.annotations.Immutable");
                    hasModifications = true;
                }
            }
        }
    }

    /**
     * Add class-level annotations.
     */
    private void addClassAnnotations(ClassOrInterfaceDeclaration classDecl, ClassSpecification spec) {
        // Add @Invariant annotations
        for (String invariant : spec.getInvariants()) {
            AnnotationExpr annotation = createAnnotation("com.jml.inferrer.annotations.Invariant", invariant);
            classDecl.addAnnotation(annotation);
        }

        // Add @Immutable if applicable
        if (spec.isImmutable()) {
            classDecl.addMarkerAnnotation("com.jml.inferrer.annotations.Immutable");
        }

        // Add @ThreadSafe if applicable
        if (spec.isThreadSafe()) {
            classDecl.addMarkerAnnotation("com.jml.inferrer.annotations.ThreadSafe");
        }

        // Add @MustCall if applicable
        if (!spec.getMustCallMethods().isEmpty()) {
            // Create array annotation
            NodeList<Expression> methods = new NodeList<>();
            for (String method : spec.getMustCallMethods()) {
                methods.add(new StringLiteralExpr(method));
            }

            ArrayInitializerExpr arrayInit = new ArrayInitializerExpr(methods);
            SingleMemberAnnotationExpr mustCallAnnotation = new SingleMemberAnnotationExpr(
                new Name("com.jml.inferrer.annotations.MustCall"),
                arrayInit
            );
            classDecl.addAnnotation(mustCallAnnotation);
        }

        logger.info("Added class-level annotations to: {}", classDecl.getNameAsString());
    }

    @Override
    public void visit(MethodDeclaration methodDecl, Void arg) {
        logger.debug("Analyzing method: {}", methodDecl.getNameAsString());

        if (shouldProcessMethod(methodDecl)) {
            MethodSpecification specification = specificationInferrer.inferSpecification(methodDecl);

            if (specification.hasSpecifications()) {
                // Build method signature for caching
                String signature = buildMethodSignature(methodDecl);
                methodSignatures.put(methodDecl, signature);

                // First pass: cache the specification and add annotations
                if (!isSecondPass) {
                    cache.put(signature, specification);
                    logger.debug("Cached spec for: {}", signature);
                    addJMLComment(methodDecl, specification);
                    hasModifications = true;
                } else {
                    // Second pass: only update if we have new specs from interprocedural analysis
                    // For now, skip re-adding to avoid duplicates
                    // Future: could compare and update if different
                }
            }
        }

        super.visit(methodDecl, arg);
    }

    /**
     * Builds a method signature for caching.
     *
     * @param methodDecl The method declaration
     * @return A signature string like "ClassName.methodName"
     */
    private String buildMethodSignature(MethodDeclaration methodDecl) {
        String methodName = methodDecl.getNameAsString();

        // Try multiple signature formats for better matching
        if (!currentClassName.isEmpty()) {
            // Use ClassName.methodName as primary signature
            String signature = currentClassName + "." + methodName;

            // Also cache with argument count for overloaded methods
            int paramCount = methodDecl.getParameters().size();
            String signatureWithArgs = methodName + "(" + paramCount + ")";

            return signature;
        }

        return methodName;
    }

    /**
     * Determines if a method should be processed for JML inference.
     *
     * @param methodDecl The method declaration
     * @return true if the method should be processed
     */
    private boolean shouldProcessMethod(MethodDeclaration methodDecl) {
        // Skip if class-level @SkipInference is set
        if (currentClassSkipInference) {
            logger.debug("Method {} skipped - class has @SkipInference", methodDecl.getNameAsString());
            return false;
        }

        // Skip abstract methods
        if (methodDecl.isAbstract()) {
            return false;
        }

        // Skip methods without body
        if (!methodDecl.getBody().isPresent()) {
            return false;
        }

        // Skip if method has @SkipInference annotation
        if (hasMethodSkipInferenceAnnotation(methodDecl)) {
            logger.debug("Method {} has @SkipInference, skipping", methodDecl.getNameAsString());
            return false;
        }

        // Skip if method already has JML specifications
        if (hasExistingJMLSpecification(methodDecl)) {
            logger.debug("Method {} already has JML specifications, skipping", methodDecl.getNameAsString());
            return false;
        }

        return true;
    }

    /**
     * Checks if a method has the @SkipInference annotation.
     */
    private boolean hasMethodSkipInferenceAnnotation(MethodDeclaration methodDecl) {
        return methodDecl.getAnnotations().stream()
            .anyMatch(ann -> {
                String name = ann.getNameAsString();
                return name.equals("SkipInference") || name.endsWith(".SkipInference");
            });
    }

    /**
     * Checks if the method already has JML specifications in its annotations.
     * Uses the comprehensive JML_ANNOTATION_NAMES set to detect any existing specs.
     * Handles both simple names (e.g., "Requires") and fully qualified names
     * (e.g., "com.jml.inferrer.annotations.Requires").
     *
     * @param methodDecl The method declaration
     * @return true if JML specifications are present
     */
    private boolean hasExistingJMLSpecification(MethodDeclaration methodDecl) {
        return methodDecl.getAnnotations().stream()
            .anyMatch(ann -> {
                String name = ann.getNameAsString();
                // Check simple name
                if (JML_ANNOTATION_NAMES.contains(name)) {
                    return true;
                }
                // Check if it's a fully qualified name ending with one of our annotations
                int lastDot = name.lastIndexOf('.');
                if (lastDot >= 0) {
                    String simpleName = name.substring(lastDot + 1);
                    return JML_ANNOTATION_NAMES.contains(simpleName);
                }
                return false;
            });
    }

    /**
     * Adds JML specifications as Java annotations to the method.
     *
     * @param methodDecl The method declaration
     * @param specification The inferred specification
     */
    private void addJMLComment(MethodDeclaration methodDecl, MethodSpecification specification) {
        // Add @Confidence annotation based on overall confidence
        addConfidenceAnnotation(methodDecl, specification);

        // Add @InheritedSpec annotations for inherited specifications
        addInheritedSpecAnnotations(methodDecl, specification);

        // Add @Requires annotations
        for (String precondition : specification.getPreconditions()) {
            AnnotationExpr annotation = createAnnotation("com.jml.inferrer.annotations.Requires", precondition);
            methodDecl.addAnnotation(annotation);
        }

        // Add @Ensures annotations
        for (String postcondition : specification.getPostconditions()) {
            AnnotationExpr annotation = createAnnotation("com.jml.inferrer.annotations.Ensures", postcondition);
            methodDecl.addAnnotation(annotation);
        }

        // Add @LoopInvariant annotations
        for (String loopInvariant : specification.getLoopInvariants()) {
            AnnotationExpr annotation = createAnnotation("com.jml.inferrer.annotations.LoopInvariant", loopInvariant);
            methodDecl.addAnnotation(annotation);
        }

        // Add @Signals annotations (exception specifications)
        for (String exceptionSpec : specification.getExceptionSpecifications()) {
            AnnotationExpr annotation = createAnnotation("com.jml.inferrer.annotations.Signals", exceptionSpec);
            methodDecl.addAnnotation(annotation);
        }

        // Add @Assignable annotations (frame conditions)
        for (String assignable : specification.getAssignableClauses()) {
            AnnotationExpr annotation = createAnnotation("com.jml.inferrer.annotations.Assignable", assignable);
            methodDecl.addAnnotation(annotation);
        }

        // Add @Pure annotation
        if (specification.isPure()) {
            methodDecl.addMarkerAnnotation("com.jml.inferrer.annotations.Pure");
        }

        // Add @Observer annotation
        if (specification.isObserver()) {
            methodDecl.addMarkerAnnotation("com.jml.inferrer.annotations.Observer");
        }

        // Add @Mutator annotation
        if (specification.isMutator()) {
            methodDecl.addMarkerAnnotation("com.jml.inferrer.annotations.Mutator");
        }

        // Add @ThreadSafe annotation
        if (specification.isThreadSafe()) {
            methodDecl.addMarkerAnnotation("com.jml.inferrer.annotations.ThreadSafe");
        }

        // Add @Complexity annotation
        if (specification.getTimeComplexity() != null || specification.getSpaceComplexity() != null) {
            NodeList<MemberValuePair> pairs = new NodeList<>();

            if (specification.getTimeComplexity() != null) {
                pairs.add(new MemberValuePair("time", new StringLiteralExpr(specification.getTimeComplexity())));
            }

            if (specification.getSpaceComplexity() != null) {
                pairs.add(new MemberValuePair("space", new StringLiteralExpr(specification.getSpaceComplexity())));
            }

            NormalAnnotationExpr complexityAnnotation = new NormalAnnotationExpr(
                new Name("com.jml.inferrer.annotations.Complexity"),
                pairs
            );
            methodDecl.addAnnotation(complexityAnnotation);
        }

        logger.info("Added JML annotations to method: {}", methodDecl.getNameAsString());
    }

    /**
     * Creates a single-value annotation expression.
     *
     * @param annotationName Fully qualified annotation name
     * @param value The annotation value
     * @return The annotation expression
     */
    private AnnotationExpr createAnnotation(String annotationName, String value) {
        // Escape quotes in the value
        String escapedValue = value.replace("\"", "\\\"");

        // Create a SingleMemberAnnotationExpr with the value
        return new SingleMemberAnnotationExpr(
            new Name(annotationName),
            new StringLiteralExpr(escapedValue)
        );
    }

    /**
     * Adds a @Confidence annotation based on the specification's overall confidence.
     */
    private void addConfidenceAnnotation(MethodDeclaration methodDecl, MethodSpecification specification) {
        MethodSpecification.ConfidenceLevel level = specification.getOverallConfidence();

        // Only add explicit confidence annotation for non-medium confidence
        if (level != MethodSpecification.ConfidenceLevel.MEDIUM) {
            // Create: @Confidence(Confidence.Level.HIGH) or @Confidence(Confidence.Level.LOW)
            FieldAccessExpr levelExpr = new FieldAccessExpr(
                new FieldAccessExpr(new NameExpr("Confidence"), "Level"),
                level.name()
            );

            SingleMemberAnnotationExpr annotation = new SingleMemberAnnotationExpr(
                new Name("com.jml.inferrer.annotations.Confidence"),
                levelExpr
            );
            methodDecl.addAnnotation(annotation);
        }
    }

    /**
     * Adds @InheritedSpec annotations for specifications inherited from parent classes/interfaces.
     */
    private void addInheritedSpecAnnotations(MethodDeclaration methodDecl, MethodSpecification specification) {
        // Collect all unique sources
        java.util.Set<String> sources = new java.util.LinkedHashSet<>();

        specification.getInheritedPreconditions().values().forEach(sources::add);
        specification.getInheritedPostconditions().values().forEach(sources::add);

        // Add an @InheritedSpec annotation for each source
        for (String source : sources) {
            SingleMemberAnnotationExpr annotation = new SingleMemberAnnotationExpr(
                new Name("com.jml.inferrer.annotations.InheritedSpec"),
                new StringLiteralExpr(source)
            );
            // Need to use NormalAnnotationExpr for the 'from' parameter
            NodeList<MemberValuePair> pairs = new NodeList<>();
            pairs.add(new MemberValuePair("from", new StringLiteralExpr(source)));

            NormalAnnotationExpr inheritedAnnotation = new NormalAnnotationExpr(
                new Name("com.jml.inferrer.annotations.InheritedSpec"),
                pairs
            );
            methodDecl.addAnnotation(inheritedAnnotation);
        }
    }

    public boolean hasModifications() {
        return hasModifications;
    }

    /**
     * Gets the specification cache for loading external specifications.
     *
     * @return The specification cache
     */
    public SpecificationCache getCache() {
        return cache;
    }

    /**
     * Gets the call graph (may be null if not provided).
     *
     * @return The call graph or null
     */
    public CallGraph getCallGraph() {
        return callGraph;
    }
}
