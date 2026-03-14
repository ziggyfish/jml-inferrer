package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;

import java.util.*;

/**
 * Analyzes Collection/Array return value properties for postcondition inference.
 */
class CollectionAnalyzer {

    void analyzeCollectionReturnProperties(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                // Check for new ArrayList(), new HashSet(), etc.
                if (expr instanceof ObjectCreationExpr) {
                    ObjectCreationExpr creation = (ObjectCreationExpr) expr;
                    String type = creation.getType().asString();
                    if (AnalysisUtils.isCollectionType(type)) {
                        postconditions.add("\\result != null");

                        // Check if it's created empty or with initial capacity
                        if (creation.getArguments().isEmpty()) {
                            postconditions.add("\\result.size() >= 0");
                        }
                    }
                }

                // Check for array creation
                if (expr instanceof ArrayCreationExpr) {
                    postconditions.add("\\result != null");
                    ArrayCreationExpr arrayCreation = (ArrayCreationExpr) expr;
                    arrayCreation.getLevels().forEach(level -> {
                        level.getDimension().ifPresent(dim -> {
                            if (methodDecl.getParameters().stream()
                                    .anyMatch(p -> p.getNameAsString().equals(dim.toString()))) {
                                postconditions.add("\\result.length == " + dim);
                            }
                        });
                    });
                }

                // Analyze collection operations in method body
                analyzeCollectionOperations(methodDecl, expr, postconditions);
            });
        }
    }

    void analyzeCollectionOperations(MethodDeclaration methodDecl, Expression returnExpr, Set<String> postconditions) {
        // Find all local variable declarations that might be the returned collection
        methodDecl.findAll(VariableDeclarationExpr.class).forEach(varDecl -> {
            varDecl.getVariables().forEach(var -> {
                if (returnExpr.toString().equals(var.getNameAsString())) {
                    // This variable is returned, analyze operations on it
                    String varName = var.getNameAsString();

                    // Check for add/remove operations
                    boolean hasAdd = methodDecl.findAll(MethodCallExpr.class).stream()
                        .anyMatch(call -> call.getScope()
                            .map(s -> s.toString().equals(varName))
                            .orElse(false) && call.getNameAsString().equals("add"));

                    boolean hasRemove = methodDecl.findAll(MethodCallExpr.class).stream()
                        .anyMatch(call -> call.getScope()
                            .map(s -> s.toString().equals(varName))
                            .orElse(false) && call.getNameAsString().equals("remove"));

                    // Check if filtering from a parameter
                    methodDecl.getParameters().forEach(param -> {
                        String paramName = param.getNameAsString();
                        if (AnalysisUtils.isCollectionType(param.getType().asString()) || param.getType().asString().contains("[]")) {
                            // Check if we're iterating over the parameter
                            boolean iteratesOverParam = methodDecl.findAll(ForEachStmt.class).stream()
                                .anyMatch(forEach -> forEach.getIterable().toString().equals(paramName));

                            if (iteratesOverParam && hasAdd && !hasRemove) {
                                // Likely a filter operation
                                if (param.getType().asString().contains("[]")) {
                                    postconditions.add("\\result.size() <= " + paramName + ".length");
                                } else {
                                    postconditions.add("\\result.size() <= " + paramName + ".size()");
                                }
                            }
                        }
                    });
                }
            });
        });
    }
}
