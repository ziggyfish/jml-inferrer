package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Infers assignable clauses (frame conditions).
 */
class AssignableAnalyzer {

    void inferAssignableClauses(MethodDeclaration methodDecl, MethodSpecification spec, ASTCollector collector) {
        Set<String> assignedLocations = new LinkedHashSet<>();

        // Collect local-variable names so we can exclude assignments to their fields from
        // `assignable`. A local points at a fresh object (or reassigned reference) that
        // the caller cannot observe — writes through it are not caller-visible side effects.
        Set<String> localVarNames = new LinkedHashSet<>();
        collector.varDeclExprs.forEach(vde -> vde.getVariables()
                .forEach(v -> localVarNames.add(v.getNameAsString())));

        // Find unary increment/decrement on fields
        collector.unaryExprs.forEach(unary -> {
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
                    } else if (localVarNames.contains(scope)) {
                        // local.field — writing through a local is not externally visible
                    } else {
                        assignedLocations.add(scope + "." + field);
                    }
                } else if (expr instanceof NameExpr) {
                    String varName = expr.toString();
                    if (AnalysisUtils.isFieldReference(methodDecl, varName)) {
                        assignedLocations.add("this." + varName);
                    }
                } else if (expr instanceof ArrayAccessExpr aae) {
                    String baseName = extractArrayBase(aae, methodDecl);
                    if (baseName != null) {
                        assignedLocations.add(baseName + "[*]");
                    }
                }
            }
        });

        // Find all assignments
        collector.assignExprs.forEach(assign -> {
            Expression target = assign.getTarget();

            if (target instanceof FieldAccessExpr) {
                FieldAccessExpr fieldAccess = (FieldAccessExpr) target;
                String scope = fieldAccess.getScope().toString();
                String field = fieldAccess.getNameAsString();

                if (scope.equals("this")) {
                    assignedLocations.add("this." + field);
                } else if (localVarNames.contains(scope)) {
                    // local.field — writing through a local is not externally visible
                } else {
                    assignedLocations.add(scope + "." + field);
                }
            } else if (target instanceof NameExpr) {
                String varName = target.toString();
                if (AnalysisUtils.isFieldReference(methodDecl, varName)) {
                    assignedLocations.add("this." + varName);
                }
            } else if (target instanceof ArrayAccessExpr) {
                String baseName = extractArrayBase((ArrayAccessExpr) target, methodDecl);
                if (baseName != null) {
                    assignedLocations.add(baseName + "[*]");
                }
            }
        });

        if (assignedLocations.isEmpty()) {
            spec.addAssignableClause("\\nothing");
        } else {
            assignedLocations.forEach(spec::addAssignableClause);
        }
    }

    /**
     * Returns the canonical base name (e.g. {@code data}, {@code arr}) of an array-access
     * write target, or {@code null} if the array is not a field or parameter we can name.
     * Handles {@code data[i]}, {@code this.data[i]}, and nested arrays like {@code data[i][j]}.
     */
    static String extractArrayBase(ArrayAccessExpr access, MethodDeclaration methodDecl) {
        Expression name = access.getName();
        if (name instanceof ArrayAccessExpr inner) {
            return extractArrayBase(inner, methodDecl);
        }
        if (name instanceof FieldAccessExpr fa) {
            if (fa.getScope().toString().equals("this")) {
                return fa.getNameAsString();
            }
            return fa.toString();
        }
        if (name instanceof NameExpr nameExpr) {
            String varName = nameExpr.getNameAsString();
            if (AnalysisUtils.isFieldReference(methodDecl, varName)) {
                return varName;
            }
            boolean isParam = methodDecl.getParameters().stream()
                    .anyMatch(p -> p.getNameAsString().equals(varName));
            if (isParam) return varName;
        }
        return null;
    }
}
