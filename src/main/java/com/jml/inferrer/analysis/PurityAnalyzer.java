package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.jml.inferrer.model.MethodSpecification;

/**
 * Infers method purity (@pure, @observer, @mutator).
 */
class PurityAnalyzer {

    void inferMethodPurity(MethodDeclaration methodDecl, MethodSpecification spec) {
        boolean hasFieldWrites = hasFieldWrites(methodDecl);
        boolean hasFieldReads = hasFieldReads(methodDecl);
        boolean performsIO = performsIO(methodDecl);
        boolean callsNonPureMethods = callsNonPureMethods(methodDecl);

        if (!hasFieldWrites && !hasFieldReads && !performsIO && !callsNonPureMethods) {
            spec.setPure(true);
        } else if (hasFieldReads && !hasFieldWrites && !performsIO) {
            spec.setObserver(true);
        } else if (hasFieldWrites) {
            spec.setMutator(true);
        }
    }

    boolean hasFieldWrites(MethodDeclaration methodDecl) {
        return !methodDecl.findAll(AssignExpr.class).stream()
                .filter(assign -> assign.getTarget() instanceof FieldAccessExpr ||
                               (assign.getTarget() instanceof NameExpr &&
                                AnalysisUtils.isFieldReference(methodDecl, assign.getTarget().toString())))
                .toList().isEmpty();
    }

    boolean hasFieldReads(MethodDeclaration methodDecl) {
        return !methodDecl.findAll(FieldAccessExpr.class).isEmpty() ||
               methodDecl.findAll(NameExpr.class).stream()
                       .anyMatch(ne -> AnalysisUtils.isFieldReference(methodDecl, ne.getNameAsString()));
    }

    boolean performsIO(MethodDeclaration methodDecl) {
        return methodDecl.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    String scope = call.getScope().map(Object::toString).orElse("");

                    return methodName.equals("println") || methodName.equals("print") ||
                           methodName.equals("printf") || methodName.equals("read") ||
                           methodName.equals("write") || methodName.equals("readLine") ||
                           scope.contains("System.out") || scope.contains("System.err") ||
                           scope.contains("System.in") || scope.contains("File") ||
                           scope.contains("Stream") || scope.contains("Reader") ||
                           scope.contains("Writer");
                });
    }

    boolean callsNonPureMethods(MethodDeclaration methodDecl) {
        return methodDecl.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    return methodName.equals("random") || methodName.equals("currentTimeMillis") ||
                           methodName.equals("nanoTime") || methodName.equals("nextInt") ||
                           methodName.equals("nextDouble");
                });
    }
}
