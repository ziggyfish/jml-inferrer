package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.Type;

import java.util.*;

/**
 * Performs data-flow analysis to track nullability of variables.
 * Infers @NonNull and @Nullable annotations for parameters, returns, and fields.
 */
public class NullabilityAnalyzer {

    /**
     * Analyze parameter nullability.
     * Returns true if parameter can NEVER be null, false if it MAY be null.
     */
    public boolean isParameterNonNull(MethodDeclaration method, String paramName) {
        // Check if there's a null check that throws exception
        boolean hasNullCheck = method.findAll(IfStmt.class).stream()
                .anyMatch(ifStmt -> {
                    Expression condition = ifStmt.getCondition();

                    // Check for: if (param == null) throw ...
                    if (condition instanceof BinaryExpr) {
                        BinaryExpr binExpr = (BinaryExpr) condition;
                        if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS) {
                            boolean isNullCheck = (binExpr.getLeft().toString().equals(paramName) &&
                                                   binExpr.getRight().isNullLiteralExpr()) ||
                                                  (binExpr.getRight().toString().equals(paramName) &&
                                                   binExpr.getLeft().isNullLiteralExpr());

                            if (isNullCheck) {
                                // Check if then branch throws exception
                                return ifStmt.getThenStmt().findFirst(ThrowStmt.class).isPresent();
                            }
                        }
                    }
                    return false;
                });

        // Check if parameter is dereferenced without null check
        boolean hasDereference = method.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> call.getScope().map(s -> s.toString().equals(paramName)).orElse(false));

        boolean hasFieldAccess = method.findAll(FieldAccessExpr.class).stream()
                .anyMatch(fae -> fae.getScope().toString().equals(paramName));

        boolean hasArrayAccess = method.findAll(ArrayAccessExpr.class).stream()
                .anyMatch(aae -> aae.getName().toString().equals(paramName));

        return hasNullCheck || hasDereference || hasFieldAccess || hasArrayAccess;
    }

    /**
     * Analyze return value nullability.
     * Returns NULL_STATE indicating if method can return null.
     */
    public NullState analyzeReturnNullability(MethodDeclaration method) {
        List<ReturnStmt> returns = method.findAll(ReturnStmt.class);

        if (returns.isEmpty()) {
            return NullState.UNKNOWN;
        }

        boolean hasNullReturn = returns.stream()
                .anyMatch(ret -> ret.getExpression()
                        .map(Expression::isNullLiteralExpr)
                        .orElse(false));

        boolean hasNonNullReturn = returns.stream()
                .anyMatch(ret -> ret.getExpression()
                        .map(expr -> !expr.isNullLiteralExpr())
                        .orElse(false));

        if (hasNullReturn && !hasNonNullReturn) {
            return NullState.ALWAYS_NULL;
        } else if (!hasNullReturn && hasNonNullReturn) {
            // Check if all returns are definitely non-null
            boolean allNonNull = returns.stream()
                    .allMatch(ret -> ret.getExpression()
                            .map(this::isDefinitelyNonNull)
                            .orElse(false));

            return allNonNull ? NullState.NON_NULL : NullState.MAYBE_NULL;
        } else if (hasNullReturn && hasNonNullReturn) {
            return NullState.MAYBE_NULL;
        }

        return NullState.UNKNOWN;
    }

    /**
     * Check if an expression is definitely non-null.
     */
    private boolean isDefinitelyNonNull(Expression expr) {
        // Literals (except null) are non-null
        if (expr.isLiteralExpr() && !expr.isNullLiteralExpr()) {
            return true;
        }

        // Object creation is non-null
        if (expr instanceof ObjectCreationExpr) {
            return true;
        }

        // Array creation is non-null
        if (expr instanceof ArrayCreationExpr) {
            return true;
        }

        // this is non-null
        if (expr.isThisExpr()) {
            return true;
        }

        // String literals are non-null
        if (expr.isStringLiteralExpr()) {
            return true;
        }

        // Primitive boxing is non-null
        if (expr instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr) expr;
            String methodName = call.getNameAsString();
            if (methodName.equals("valueOf")) {
                return true; // Integer.valueOf(), etc.
            }
        }

        return false;
    }

    /**
     * Analyze field nullability.
     */
    public NullState analyzeFieldNullability(FieldDeclaration field, VariableDeclarator var) {
        // Check initialization
        if (var.getInitializer().isPresent()) {
            Expression init = var.getInitializer().get();
            if (init.isNullLiteralExpr()) {
                return NullState.MAYBE_NULL;
            } else if (isDefinitelyNonNull(init)) {
                // Need to check if field is ever set to null later
                return NullState.MAYBE_NULL; // Conservative
            }
        }

        // If field is final and initialized to non-null
        if (field.isFinal() && var.getInitializer().isPresent()) {
            if (isDefinitelyNonNull(var.getInitializer().get())) {
                return NullState.NON_NULL;
            }
        }

        return NullState.MAYBE_NULL;
    }

    /**
     * Perform data-flow analysis to track null state through method.
     */
    public Map<String, NullState> analyzeMethodFlow(MethodDeclaration method) {
        Map<String, NullState> nullStates = new HashMap<>();

        // Initialize parameters
        for (Parameter param : method.getParameters()) {
            if (param.getType().isReferenceType()) {
                nullStates.put(param.getNameAsString(), NullState.MAYBE_NULL);
            }
        }

        // Analyze statements to update null states
        if (method.getBody().isPresent()) {
            analyzeStatementBlock(method.getBody().get(), nullStates);
        }

        return nullStates;
    }

    private void analyzeStatementBlock(Statement stmt, Map<String, NullState> nullStates) {
        if (stmt instanceof BlockStmt) {
            BlockStmt block = (BlockStmt) stmt;
            for (Statement s : block.getStatements()) {
                analyzeStatement(s, nullStates);
            }
        } else {
            analyzeStatement(stmt, nullStates);
        }
    }

    private void analyzeStatement(Statement stmt, Map<String, NullState> nullStates) {
        // Handle null checks: if (x == null)
        if (stmt instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) stmt;
            Expression condition = ifStmt.getCondition();

            if (condition instanceof BinaryExpr) {
                BinaryExpr binExpr = (BinaryExpr) condition;

                // Check for x == null
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS) {
                    String varName = null;
                    if (binExpr.getLeft() instanceof NameExpr && binExpr.getRight().isNullLiteralExpr()) {
                        varName = binExpr.getLeft().toString();
                    } else if (binExpr.getRight() instanceof NameExpr && binExpr.getLeft().isNullLiteralExpr()) {
                        varName = binExpr.getRight().toString();
                    }

                    if (varName != null) {
                        // In then branch, variable is null
                        Map<String, NullState> thenStates = new HashMap<>(nullStates);
                        thenStates.put(varName, NullState.ALWAYS_NULL);
                        analyzeStatementBlock(ifStmt.getThenStmt(), thenStates);

                        // In else branch, variable is non-null
                        final String finalVarName = varName;
                        ifStmt.getElseStmt().ifPresent(elseStmt -> {
                            Map<String, NullState> elseStates = new HashMap<>(nullStates);
                            elseStates.put(finalVarName, NullState.NON_NULL);
                            analyzeStatementBlock(elseStmt, elseStates);
                        });

                        return;
                    }
                }
                // Check for x != null
                else if (binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS) {
                    String varName = null;
                    if (binExpr.getLeft() instanceof NameExpr && binExpr.getRight().isNullLiteralExpr()) {
                        varName = binExpr.getLeft().toString();
                    } else if (binExpr.getRight() instanceof NameExpr && binExpr.getLeft().isNullLiteralExpr()) {
                        varName = binExpr.getRight().toString();
                    }

                    if (varName != null) {
                        // In then branch, variable is non-null
                        Map<String, NullState> thenStates = new HashMap<>(nullStates);
                        thenStates.put(varName, NullState.NON_NULL);
                        analyzeStatementBlock(ifStmt.getThenStmt(), thenStates);

                        // In else branch, variable is null
                        final String finalVarName = varName;
                        ifStmt.getElseStmt().ifPresent(elseStmt -> {
                            Map<String, NullState> elseStates = new HashMap<>(nullStates);
                            elseStates.put(finalVarName, NullState.ALWAYS_NULL);
                            analyzeStatementBlock(elseStmt, elseStates);
                        });

                        return;
                    }
                }
            }

            // Default: analyze both branches
            analyzeStatementBlock(ifStmt.getThenStmt(), new HashMap<>(nullStates));
            ifStmt.getElseStmt().ifPresent(elseStmt ->
                analyzeStatementBlock(elseStmt, new HashMap<>(nullStates)));
        }

        // Handle assignments: x = expr
        if (stmt instanceof ExpressionStmt) {
            ExpressionStmt exprStmt = (ExpressionStmt) stmt;
            if (exprStmt.getExpression() instanceof AssignExpr) {
                AssignExpr assign = (AssignExpr) exprStmt.getExpression();
                if (assign.getTarget() instanceof NameExpr) {
                    String varName = assign.getTarget().toString();
                    Expression value = assign.getValue();

                    if (value.isNullLiteralExpr()) {
                        nullStates.put(varName, NullState.ALWAYS_NULL);
                    } else if (isDefinitelyNonNull(value)) {
                        nullStates.put(varName, NullState.NON_NULL);
                    } else {
                        nullStates.put(varName, NullState.MAYBE_NULL);
                    }
                }
            }
        }

        // Handle variable declarations
        stmt.findAll(VariableDeclarationExpr.class).forEach(varDecl -> {
            for (VariableDeclarator var : varDecl.getVariables()) {
                String varName = var.getNameAsString();
                if (var.getInitializer().isPresent()) {
                    Expression init = var.getInitializer().get();
                    if (init.isNullLiteralExpr()) {
                        nullStates.put(varName, NullState.ALWAYS_NULL);
                    } else if (isDefinitelyNonNull(init)) {
                        nullStates.put(varName, NullState.NON_NULL);
                    } else {
                        nullStates.put(varName, NullState.MAYBE_NULL);
                    }
                }
            }
        });
    }

    /**
     * Null state enumeration.
     */
    public enum NullState {
        NON_NULL,       // Definitely non-null
        ALWAYS_NULL,    // Definitely null
        MAYBE_NULL,     // May be null or non-null
        UNKNOWN         // Cannot determine
    }
}
