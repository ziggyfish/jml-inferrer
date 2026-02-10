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
 * AST Visitor that traverses Java classes and methods to infer JML specifications.
 * Performs two-pass analysis for interprocedural specification inference.
 */
public class JMLInferenceVisitor extends VoidVisitorAdapter<Void> {

    private static final Logger logger = LoggerFactory.getLogger(JMLInferenceVisitor.class);
    private final MethodSpecificationInferrer specificationInferrer;
    private final ClassInvariantInferrer classInvariantInferrer;
    private final NullabilityAnalyzer nullabilityAnalyzer;
    private final SpecificationCache cache;
    private boolean hasModifications = false;
    private String currentClassName = "";

    // For two-pass analysis
    private final Map<MethodDeclaration, String> methodSignatures = new HashMap<>();
    private boolean isSecondPass = false;

    public JMLInferenceVisitor() {
        this.cache = new SpecificationCache();
        this.specificationInferrer = new MethodSpecificationInferrer(cache);
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
        currentClassName = classDecl.getNameAsString();
        logger.debug("Analyzing class: {}", currentClassName);

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
        if (methodDecl.isAbstract()) {
            return false;
        }

        if (!methodDecl.getBody().isPresent()) {
            return false;
        }

        if (hasExistingJMLSpecification(methodDecl)) {
            logger.debug("Method {} already has JML specifications, skipping", methodDecl.getNameAsString());
            return false;
        }

        return true;
    }

    /**
     * Checks if the method already has JML specifications in its annotations.
     *
     * @param methodDecl The method declaration
     * @return true if JML specifications are present
     */
    private boolean hasExistingJMLSpecification(MethodDeclaration methodDecl) {
        return methodDecl.getAnnotations().stream()
            .anyMatch(ann -> {
                String name = ann.getNameAsString();
                return name.equals("Requires") || name.equals("Ensures") ||
                       name.equals("LoopInvariant");
            });
    }

    /**
     * Adds JML specifications as Java annotations to the method.
     *
     * @param methodDecl The method declaration
     * @param specification The inferred specification
     */
    private void addJMLComment(MethodDeclaration methodDecl, MethodSpecification specification) {
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
}
