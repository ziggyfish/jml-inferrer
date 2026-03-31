package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.jml.inferrer.model.MethodSpecification;

/**
 * Infers method purity (@pure, @observer, @mutator).
 */
class PurityAnalyzer {

    void inferMethodPurity(MethodDeclaration methodDecl, MethodSpecification spec, ASTCollector collector) {
        boolean hasFieldWrites = hasFieldWrites(methodDecl, collector);
        boolean hasFieldReads = hasFieldReads(methodDecl, collector);
        boolean performsIO = performsIO(collector);
        boolean callsNonPureMethods = callsNonPureMethods(collector);

        if (!hasFieldWrites && !hasFieldReads && !performsIO && !callsNonPureMethods) {
            spec.setPure(true);
        } else if (hasFieldReads && !hasFieldWrites && !performsIO) {
            spec.setObserver(true);
        } else if (hasFieldWrites) {
            spec.setMutator(true);
        }
    }

    boolean hasFieldWrites(MethodDeclaration methodDecl, ASTCollector collector) {
        return !collector.assignExprs.stream()
                .filter(assign -> assign.getTarget() instanceof FieldAccessExpr ||
                               (assign.getTarget() instanceof NameExpr &&
                                AnalysisUtils.isFieldReference(methodDecl, assign.getTarget().toString())))
                .toList().isEmpty();
    }

    boolean hasFieldReads(MethodDeclaration methodDecl, ASTCollector collector) {
        return !collector.fieldAccessExprs.isEmpty() ||
               collector.nameExprs.stream()
                       .anyMatch(ne -> AnalysisUtils.isFieldReference(methodDecl, ne.getNameAsString()));
    }

    boolean performsIO(ASTCollector collector) {
        return collector.methodCallExprs.stream()
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

    boolean callsNonPureMethods(ASTCollector collector) {
        return collector.methodCallExprs.stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    return methodName.equals("random") || methodName.equals("currentTimeMillis") ||
                           methodName.equals("nanoTime") || methodName.equals("nextInt") ||
                           methodName.equals("nextDouble");
                });
    }
}
