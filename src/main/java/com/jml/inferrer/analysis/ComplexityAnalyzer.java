package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Infers computational complexity (Big-O) and thread safety.
 */
class ComplexityAnalyzer {

    void inferComplexity(MethodDeclaration methodDecl, MethodSpecification spec, ASTCollector collector) {
        int loopNesting = calculateMaxLoopNesting(methodDecl);
        boolean hasRecursion = hasRecursion(methodDecl, collector);

        String complexity;
        if (loopNesting == 0 && !hasRecursion) {
            complexity = "O(1)";
        } else if (loopNesting == 1 && !hasRecursion) {
            complexity = "O(n)";
        } else if (loopNesting == 2) {
            complexity = "O(n^2)";
        } else if (loopNesting == 3) {
            complexity = "O(n^3)";
        } else if (loopNesting > 3) {
            complexity = "O(n^" + loopNesting + ")";
        } else if (hasRecursion && hasDivideAndConquer(collector)) {
            complexity = "O(n log n)";
        } else if (hasRecursion) {
            complexity = "O(2^n)";
        } else {
            complexity = "O(n)";
        }

        spec.setTimeComplexity(complexity);

        // Space complexity (simplified)
        boolean allocatesArray = collector.arrayCreationExprs.stream()
                .anyMatch(ace -> !ace.getLevels().isEmpty());
        boolean allocatesCollection = collector.objectCreationExprs.stream()
                .anyMatch(oce -> oce.getType().asString().contains("List") ||
                                 oce.getType().asString().contains("Set") ||
                                 oce.getType().asString().contains("Map"));

        if (allocatesArray || allocatesCollection) {
            spec.setSpaceComplexity("O(n)");
        } else if (hasRecursion) {
            spec.setSpaceComplexity("O(log n)");
        } else {
            spec.setSpaceComplexity("O(1)");
        }
    }

    int calculateMaxLoopNesting(MethodDeclaration methodDecl) {
        return calculateLoopNestingRecursive(methodDecl);
    }

    int calculateLoopNestingRecursive(com.github.javaparser.ast.Node node) {
        int maxNesting = 0;

        boolean isLoop = node instanceof ForStmt || node instanceof WhileStmt ||
                        node instanceof ForEachStmt || node instanceof DoStmt;

        if (isLoop) {
            for (com.github.javaparser.ast.Node child : node.getChildNodes()) {
                int childNesting = calculateLoopNestingRecursive(child);
                maxNesting = Math.max(maxNesting, childNesting);
            }
            return maxNesting + 1;
        } else {
            for (com.github.javaparser.ast.Node child : node.getChildNodes()) {
                int childNesting = calculateLoopNestingRecursive(child);
                maxNesting = Math.max(maxNesting, childNesting);
            }
            return maxNesting;
        }
    }

    boolean hasRecursion(MethodDeclaration methodDecl, ASTCollector collector) {
        String methodName = methodDecl.getNameAsString();
        return collector.methodCallExprs.stream()
                .anyMatch(call -> call.getNameAsString().equals(methodName));
    }

    boolean hasDivideAndConquer(ASTCollector collector) {
        return collector.binaryExprs.stream()
                .anyMatch(binExpr -> {
                    if (binExpr.getOperator() == BinaryExpr.Operator.DIVIDE) {
                        String right = binExpr.getRight().toString();
                        return right.equals("2");
                    }
                    return false;
                });
    }

    void inferThreadSafety(MethodDeclaration methodDecl, MethodSpecification spec, ASTCollector collector) {
        boolean isSynchronized = methodDecl.isSynchronized();
        boolean usesSynchronizedBlock = !collector.synchronizedStmts.isEmpty();
        boolean usesLocks = collector.methodCallExprs.stream()
                .anyMatch(call -> call.getNameAsString().equals("lock") ||
                                 call.getNameAsString().equals("unlock"));
        boolean usesConcurrentCollections = collector.objectCreationExprs.stream()
                .anyMatch(oce -> oce.getType().asString().contains("Concurrent") ||
                                 oce.getType().asString().contains("Atomic"));

        boolean onlyFinalFields = checkOnlyFinalFields(methodDecl, collector);

        if (isSynchronized || usesSynchronizedBlock || usesLocks || usesConcurrentCollections || onlyFinalFields) {
            spec.setThreadSafe(true);
        }
    }

    boolean checkOnlyFinalFields(MethodDeclaration methodDecl, ASTCollector collector) {
        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(classDecl -> {
                    List<String> accessedFields = new ArrayList<>();

                    collector.fieldAccessExprs.forEach(fae -> {
                        if (fae.getScope().toString().equals("this")) {
                            accessedFields.add(fae.getNameAsString());
                        }
                    });

                    collector.nameExprs.forEach(ne -> {
                        if (AnalysisUtils.isFieldReference(methodDecl, ne.getNameAsString())) {
                            accessedFields.add(ne.getNameAsString());
                        }
                    });

                    return accessedFields.stream().allMatch(fieldName ->
                        classDecl.getFieldByName(fieldName)
                                .map(field -> field.isFinal())
                                .orElse(false)
                    );
                }).orElse(false);
    }
}
