package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Infers assignable clauses (frame conditions).
 */
class AssignableAnalyzer {

    void inferAssignableClauses(MethodDeclaration methodDecl, MethodSpecification spec) {
        Set<String> assignedLocations = new LinkedHashSet<>();

        // Find unary increment/decrement on fields
        methodDecl.findAll(UnaryExpr.class).forEach(unary -> {
            if (unary.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                unary.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT ||
                unary.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                unary.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) {
                Expression expr = unary.getExpression();
                if (expr instanceof FieldAccessExpr) {
                    FieldAccessExpr fieldAccess = (FieldAccessExpr) expr;
                    String scope = fieldAccess.getScope().toString();
                    String field = fieldAccess.getNameAsString();
                    if (scope.equals("this")) {
                        assignedLocations.add("this." + field);
                    } else {
                        assignedLocations.add(scope + "." + field);
                    }
                } else if (expr instanceof NameExpr) {
                    String varName = expr.toString();
                    if (AnalysisUtils.isFieldReference(methodDecl, varName)) {
                        assignedLocations.add("this." + varName);
                    }
                }
            }
        });

        // Find all assignments
        methodDecl.findAll(AssignExpr.class).forEach(assign -> {
            Expression target = assign.getTarget();

            if (target instanceof FieldAccessExpr) {
                FieldAccessExpr fieldAccess = (FieldAccessExpr) target;
                String scope = fieldAccess.getScope().toString();
                String field = fieldAccess.getNameAsString();

                if (scope.equals("this")) {
                    assignedLocations.add("this." + field);
                } else {
                    assignedLocations.add(scope + "." + field);
                }
            } else if (target instanceof NameExpr) {
                String varName = target.toString();
                if (AnalysisUtils.isFieldReference(methodDecl, varName)) {
                    assignedLocations.add("this." + varName);
                }
            } else if (target instanceof ArrayAccessExpr) {
                ArrayAccessExpr arrayAccess = (ArrayAccessExpr) target;
                String arrayName = arrayAccess.getName().toString();
                if (AnalysisUtils.isFieldReference(methodDecl, arrayName) ||
                    methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(arrayName))) {
                    assignedLocations.add(arrayName + "[*]");
                }
            }
        });

        if (assignedLocations.isEmpty()) {
            spec.addAssignableClause("\\nothing");
        } else {
            assignedLocations.forEach(spec::addAssignableClause);
        }
    }
}
