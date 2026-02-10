package com.jml.inferrer.analysis;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;

/**
 * Builds a CallGraph by visiting all CompilationUnits in a codebase.
 * This should be run as Pass 0 before specification inference.
 *
 * The builder collects:
 * - Method call relationships
 * - Class hierarchy (extends)
 * - Interface implementations
 * - Method signatures and their containing classes
 */
public class CallGraphBuilder extends VoidVisitorAdapter<CallGraph> {

    private static final Logger logger = LoggerFactory.getLogger(CallGraphBuilder.class);

    private String currentClassName = "";
    private String currentMethodSignature = "";

    /**
     * Builds a call graph from a list of compilation units.
     *
     * @param compilationUnits The list of parsed Java files
     * @return The constructed call graph
     */
    public CallGraph buildFromCompilationUnits(List<CompilationUnit> compilationUnits) {
        CallGraph callGraph = new CallGraph();

        for (CompilationUnit cu : compilationUnits) {
            visit(cu, callGraph);
        }

        logger.info("Call graph built: {}", callGraph.getStatistics());
        return callGraph;
    }

    @Override
    public void visit(ClassOrInterfaceDeclaration classDecl, CallGraph callGraph) {
        String previousClassName = currentClassName;
        currentClassName = classDecl.getNameAsString();

        // Record superclass
        classDecl.getExtendedTypes().forEach(extendedType -> {
            String superclassName = extendedType.getNameAsString();
            if (classDecl.isInterface()) {
                callGraph.addExtendedInterface(currentClassName, superclassName);
            } else {
                callGraph.setSuperclass(currentClassName, superclassName);
            }
            logger.debug("Class {} extends {}", currentClassName, superclassName);
        });

        // Record implemented interfaces
        classDecl.getImplementedTypes().forEach(implementedType -> {
            String interfaceName = implementedType.getNameAsString();
            callGraph.addImplementedInterface(currentClassName, interfaceName);
            logger.debug("Class {} implements {}", currentClassName, interfaceName);
        });

        super.visit(classDecl, callGraph);
        currentClassName = previousClassName;
    }

    @Override
    public void visit(MethodDeclaration methodDecl, CallGraph callGraph) {
        String previousMethodSignature = currentMethodSignature;

        // Build method signature
        currentMethodSignature = buildMethodSignature(methodDecl);

        // Record method in class
        if (!currentClassName.isEmpty()) {
            callGraph.addMethodToClass(currentMethodSignature, currentClassName);
        }

        // Check for @Override annotation to detect override relationships
        boolean hasOverride = methodDecl.getAnnotations().stream()
                .anyMatch(ann -> ann.getNameAsString().equals("Override"));

        if (hasOverride && !currentClassName.isEmpty()) {
            // Try to find the parent method
            String parentMethod = callGraph.findParentMethod(
                    methodDecl.getNameAsString(),
                    methodDecl.getParameters().size(),
                    currentClassName
            );

            if (parentMethod != null) {
                callGraph.addOverride(currentMethodSignature, parentMethod);
                logger.debug("Method {} overrides {}", currentMethodSignature, parentMethod);
            }
        }

        super.visit(methodDecl, callGraph);
        currentMethodSignature = previousMethodSignature;
    }

    @Override
    public void visit(MethodCallExpr methodCall, CallGraph callGraph) {
        if (!currentMethodSignature.isEmpty()) {
            String calleeSignature = buildCalleeSignature(methodCall);
            callGraph.addCall(currentMethodSignature, calleeSignature);
            logger.trace("Call: {} -> {}", currentMethodSignature, calleeSignature);
        }

        super.visit(methodCall, callGraph);
    }

    /**
     * Builds a method signature from a method declaration.
     * Format: ClassName.methodName(paramCount) for simple matching
     * or ClassName.methodName(ParamType1,ParamType2) for precise matching
     */
    private String buildMethodSignature(MethodDeclaration methodDecl) {
        StringBuilder signature = new StringBuilder();

        if (!currentClassName.isEmpty()) {
            signature.append(currentClassName).append(".");
        }

        signature.append(methodDecl.getNameAsString());
        signature.append("(");

        List<Parameter> params = methodDecl.getParameters();
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) {
                signature.append(",");
            }
            // Use simple type name for matching
            String typeName = params.get(i).getType().asString();
            // Remove generics for simpler matching
            if (typeName.contains("<")) {
                typeName = typeName.substring(0, typeName.indexOf('<'));
            }
            signature.append(typeName);
        }

        signature.append(")");
        return signature.toString();
    }

    /**
     * Builds a signature for a method call (callee).
     * Since we may not know the exact class, we use multiple potential signatures.
     */
    private String buildCalleeSignature(MethodCallExpr methodCall) {
        StringBuilder signature = new StringBuilder();

        // Try to get scope (the object/class the method is called on)
        methodCall.getScope().ifPresent(scope -> {
            String scopeStr = scope.toString();
            // Handle common cases
            if (!scopeStr.equals("this") && !scopeStr.equals("super")) {
                // Could be a class name or variable name
                // For now, use as-is
                signature.append(scopeStr).append(".");
            }
        });

        signature.append(methodCall.getNameAsString());

        // Add argument count for basic matching
        signature.append("(").append(methodCall.getArguments().size()).append(")");

        return signature.toString();
    }
}
