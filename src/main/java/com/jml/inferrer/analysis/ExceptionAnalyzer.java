package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.List;

/**
 * Infers exception specifications (@signals) and analyzes exception handling patterns.
 */
class ExceptionAnalyzer {

    /**
     * Recovery patterns for exception handling.
     */
    public enum RecoveryPattern {
        RETHROW,
        WRAP_AND_THROW,
        LOG_AND_CONTINUE,
        RETURN_DEFAULT,
        SUPPRESS,
        RECOVER_AND_RETRY,
        FALLBACK
    }

    void inferExceptionSpecifications(MethodDeclaration methodDecl, MethodSpecification spec) {
        // Find all throw statements
        methodDecl.findAll(ThrowStmt.class).forEach(throwStmt -> {
            Expression thrownExpr = throwStmt.getExpression();
            String exceptionType = getExceptionType(thrownExpr);

            throwStmt.findAncestor(IfStmt.class).ifPresent(ifStmt -> {
                String condition = getThrowCondition(ifStmt, throwStmt);
                if (condition != null && !condition.isEmpty()) {
                    spec.addExceptionSpecification(exceptionType + " when " + condition,
                            MethodSpecification.ConfidenceLevel.HIGH);
                } else {
                    spec.addExceptionSpecification(exceptionType);
                }
            });

            if (throwStmt.findAncestor(IfStmt.class).isEmpty()) {
                spec.addExceptionSpecification(exceptionType);
            }
        });

        // Check method signature for declared exceptions
        methodDecl.getThrownExceptions().forEach(thrownType -> {
            spec.addExceptionSpecification(thrownType.asString(),
                    MethodSpecification.ConfidenceLevel.HIGH);
        });

        // Analyze try-catch blocks
        analyzeExceptionHandling(methodDecl, spec);
    }

    void analyzeExceptionHandling(MethodDeclaration methodDecl, MethodSpecification spec) {
        methodDecl.findAll(TryStmt.class).forEach(tryStmt -> {
            tryStmt.getCatchClauses().forEach(catchClause -> {
                RecoveryPattern pattern = identifyRecoveryPattern(catchClause);
                String exceptionType = catchClause.getParameter().getType().asString();

                switch (pattern) {
                    case RETHROW:
                        spec.addExceptionSpecification("propagates " + exceptionType);
                        break;
                    case WRAP_AND_THROW:
                        catchClause.getBody().findAll(ThrowStmt.class).stream()
                            .findFirst()
                            .ifPresent(throwStmt -> {
                                String wrappedType = getExceptionType(throwStmt.getExpression());
                                spec.addExceptionSpecification("wraps " + exceptionType + " in " + wrappedType);
                            });
                        break;
                    case LOG_AND_CONTINUE:
                        spec.addExceptionSpecification("handles " + exceptionType + " (logs and continues)");
                        break;
                    case RETURN_DEFAULT:
                        catchClause.getBody().findAll(ReturnStmt.class).stream()
                            .findFirst()
                            .ifPresent(returnStmt -> {
                                String returnValue = returnStmt.getExpression()
                                        .map(Expression::toString)
                                        .orElse("void");
                                spec.addExceptionSpecification("on " + exceptionType + " returns " + returnValue);
                            });
                        break;
                    case SUPPRESS:
                        spec.addExceptionSpecification("suppresses " + exceptionType);
                        break;
                    case RECOVER_AND_RETRY:
                        spec.addExceptionSpecification("recovers from " + exceptionType + " and retries");
                        break;
                    case FALLBACK:
                        spec.addExceptionSpecification("falls back on " + exceptionType);
                        break;
                }
            });

            tryStmt.getFinallyBlock().ifPresent(finallyBlock -> {
                if (!finallyBlock.getStatements().isEmpty()) {
                    boolean hasClose = finallyBlock.findAll(MethodCallExpr.class).stream()
                            .anyMatch(call -> call.getNameAsString().equals("close"));
                    if (hasClose) {
                        spec.addExceptionSpecification("ensures resources are closed");
                    }
                }
            });
        });
    }

    RecoveryPattern identifyRecoveryPattern(CatchClause catchClause) {
        BlockStmt body = catchClause.getBody();
        List<ThrowStmt> throwStmts = body.findAll(ThrowStmt.class);
        List<ReturnStmt> returnStmts = body.findAll(ReturnStmt.class);
        List<MethodCallExpr> methodCalls = body.findAll(MethodCallExpr.class);

        if (body.getStatements().isEmpty()) {
            return RecoveryPattern.SUPPRESS;
        }

        if (!throwStmts.isEmpty()) {
            ThrowStmt throwStmt = throwStmts.get(0);
            Expression thrownExpr = throwStmt.getExpression();

            if (thrownExpr instanceof NameExpr) {
                String varName = thrownExpr.toString();
                if (varName.equals(catchClause.getParameter().getNameAsString())) {
                    return RecoveryPattern.RETHROW;
                }
            }

            if (thrownExpr instanceof ObjectCreationExpr) {
                ObjectCreationExpr creation = (ObjectCreationExpr) thrownExpr;
                boolean wrapsOriginal = creation.getArguments().stream()
                        .anyMatch(arg -> arg.toString().equals(catchClause.getParameter().getNameAsString()));
                if (wrapsOriginal) {
                    return RecoveryPattern.WRAP_AND_THROW;
                }
                return RecoveryPattern.RETHROW;
            }
        }

        if (!returnStmts.isEmpty()) {
            return RecoveryPattern.RETURN_DEFAULT;
        }

        boolean hasLogging = methodCalls.stream()
                .anyMatch(call -> {
                    String name = call.getNameAsString();
                    String scope = call.getScope().map(Object::toString).orElse("");
                    return name.equals("error") || name.equals("warn") || name.equals("info") ||
                           name.equals("log") || name.equals("printStackTrace") ||
                           scope.contains("log") || scope.contains("LOG") || scope.contains("logger");
                });

        if (hasLogging) {
            boolean hasRetry = methodCalls.stream()
                    .anyMatch(call -> call.getNameAsString().contains("retry"));
            if (hasRetry) {
                return RecoveryPattern.RECOVER_AND_RETRY;
            }
            return RecoveryPattern.LOG_AND_CONTINUE;
        }

        boolean hasFallback = methodCalls.stream()
                .anyMatch(call -> {
                    String name = call.getNameAsString().toLowerCase();
                    return name.contains("fallback") || name.contains("default") ||
                           name.contains("backup") || name.contains("alternate");
                });

        if (hasFallback) {
            return RecoveryPattern.FALLBACK;
        }

        return RecoveryPattern.LOG_AND_CONTINUE;
    }

    String getExceptionType(Expression thrownExpr) {
        if (thrownExpr instanceof ObjectCreationExpr) {
            ObjectCreationExpr objExpr = (ObjectCreationExpr) thrownExpr;
            return objExpr.getType().asString();
        }
        return "Exception";
    }

    String getThrowCondition(IfStmt ifStmt, ThrowStmt throwStmt) {
        Expression condition = ifStmt.getCondition();

        boolean inThenBranch = ifStmt.getThenStmt().containsWithinRange(throwStmt);

        if (inThenBranch) {
            return condition.toString();
        } else {
            return AnalysisUtils.negateCondition(condition);
        }
    }
}
