package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ReturnStmt;

import java.util.*;

/**
 * Analyzes String return value properties for postcondition inference.
 */
class StringAnalyzer {

    void analyzeStringReturnProperties(MethodDeclaration methodDecl, Set<String> postconditions,
                                        ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;

        boolean allReturnsNonNull = PostconditionAnalyzer.alwaysReturnsNonNull(collector);
        if (allReturnsNonNull) {
            postconditions.add("\\result != null");

            // Check if all return statements return string literals of the same length
            List<Integer> stringLengths = new ArrayList<>();
            boolean allStringLiterals = true;
            for (ReturnStmt ret : returnStmts) {
                if (ret.getExpression().isPresent() && ret.getExpression().get() instanceof StringLiteralExpr) {
                    stringLengths.add(((StringLiteralExpr) ret.getExpression().get()).asString().length());
                } else {
                    allStringLiterals = false;
                    break;
                }
            }
            if (allStringLiterals && !stringLengths.isEmpty()) {
                int firstLen = stringLengths.get(0);
                if (stringLengths.stream().allMatch(len -> len == firstLen)) {
                    postconditions.add("\\result.length() == " + firstLen);
                    if (firstLen == 0) {
                        postconditions.add("\\result.isEmpty()");
                    }
                }
            }
        }

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                analyzeStringExpression(expr, methodDecl, postconditions, collector);
            });
        }
    }

    void analyzeStringExpression(Expression expr, MethodDeclaration methodDecl, Set<String> postconditions,
                                  ASTCollector collector) {
        // Check for StringBuilder/StringBuffer usage
        if (expr instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr) expr;
            String methodName = call.getNameAsString();

            if (methodName.equals("toString")) {
                call.getScope().ifPresent(scope -> {
                    String scopeStr = scope.toString();
                    if (scopeStr.contains("StringBuilder") || scopeStr.contains("StringBuffer")) {
                        postconditions.add("\\result != null");
                    }
                });
            }

            // Static String methods
            if (methodName.equals("valueOf") || methodName.equals("format") ||
                methodName.equals("join")) {
                postconditions.add("\\result != null");
            }

            // Instance string methods
            call.getScope().ifPresent(scope -> {
                String scopeStr = scope.toString();
                boolean isStringParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(scopeStr) &&
                                       p.getType().asString().equals("String"));

                // Also check for string fields or local variables
                boolean mightBeString = isStringParam ||
                        collector.varDeclExprs.stream()
                            .flatMap(v -> v.getVariables().stream())
                            .anyMatch(v -> v.getNameAsString().equals(scopeStr) &&
                                          v.getType().asString().equals("String"));

                if (isStringParam || mightBeString) {
                    analyzeStringMethodCall(methodName, scopeStr, call, postconditions);
                }
            });
        }

        // Check for string concatenation with +
        if (expr instanceof BinaryExpr) {
            BinaryExpr binExpr = (BinaryExpr) expr;
            if (binExpr.getOperator() == BinaryExpr.Operator.PLUS) {
                // Check if this is string concatenation
                boolean leftIsString = isStringExpression(binExpr.getLeft(), methodDecl);
                boolean rightIsString = isStringExpression(binExpr.getRight(), methodDecl);

                if (leftIsString || rightIsString) {
                    postconditions.add("\\result != null");

                    // If both operands are parameters, we can say something about length
                    String leftName = binExpr.getLeft().toString();
                    String rightName = binExpr.getRight().toString();

                    boolean leftIsParam = isStringParameter(leftName, methodDecl);
                    boolean rightIsParam = isStringParameter(rightName, methodDecl);

                    if (leftIsParam && rightIsParam) {
                        postconditions.add("\\result.length() == " + leftName + ".length() + " + rightName + ".length()");
                    } else if (leftIsParam && binExpr.getRight() instanceof StringLiteralExpr) {
                        int literalLen = ((StringLiteralExpr) binExpr.getRight()).asString().length();
                        postconditions.add("\\result.length() == " + leftName + ".length() + " + literalLen);
                    } else if (rightIsParam && binExpr.getLeft() instanceof StringLiteralExpr) {
                        int literalLen = ((StringLiteralExpr) binExpr.getLeft()).asString().length();
                        postconditions.add("\\result.length() == " + literalLen + " + " + rightName + ".length()");
                    }
                }
            }
        }

        // Check for string literal returns (length inference only; non-null
        // is already handled at the method level by analyzeStringReturnProperties)
        if (expr instanceof StringLiteralExpr) {
            String value = ((StringLiteralExpr) expr).asString();
            if (value.isEmpty()) {
                postconditions.add("\\result.isEmpty()");
            }
        }
    }

    void analyzeStringMethodCall(String methodName, String scopeStr,
                                 MethodCallExpr call, Set<String> postconditions) {
        switch (methodName) {
            // Length-preserving operations
            case "toUpperCase":
            case "toLowerCase":
                postconditions.add("\\result != null");
                postconditions.add("\\result.length() == " + scopeStr + ".length()");
                break;

            // Trimming operations - length can only decrease
            case "trim":
            case "strip":
            case "stripLeading":
            case "stripTrailing":
                postconditions.add("\\result != null");
                postconditions.add("\\result.length() <= " + scopeStr + ".length()");
                break;

            // Substring - length can only decrease
            case "substring":
                postconditions.add("\\result != null");
                if (call.getArguments().size() == 1) {
                    // substring(beginIndex) - returns from beginIndex to end
                    Expression beginArg = call.getArguments().get(0);
                    if (beginArg instanceof IntegerLiteralExpr) {
                        int begin = ((IntegerLiteralExpr) beginArg).asInt();
                        postconditions.add("\\result.length() == " + scopeStr + ".length() - " + begin);
                    } else {
                        postconditions.add("\\result.length() <= " + scopeStr + ".length()");
                    }
                } else if (call.getArguments().size() == 2) {
                    // substring(beginIndex, endIndex)
                    Expression beginArg = call.getArguments().get(0);
                    Expression endArg = call.getArguments().get(1);
                    if (beginArg instanceof IntegerLiteralExpr && endArg instanceof IntegerLiteralExpr) {
                        int begin = ((IntegerLiteralExpr) beginArg).asInt();
                        int end = ((IntegerLiteralExpr) endArg).asInt();
                        postconditions.add("\\result.length() == " + (end - begin));
                    } else {
                        postconditions.add("\\result.length() <= " + scopeStr + ".length()");
                    }
                }
                break;

            // Concatenation
            case "concat":
                postconditions.add("\\result != null");
                if (call.getArguments().size() == 1) {
                    Expression arg = call.getArguments().get(0);
                    if (arg instanceof StringLiteralExpr) {
                        int argLen = ((StringLiteralExpr) arg).asString().length();
                        postconditions.add("\\result.length() == " + scopeStr + ".length() + " + argLen);
                    } else {
                        postconditions.add("\\result.length() >= " + scopeStr + ".length()");
                    }
                }
                break;

            // Repeat (Java 11+)
            case "repeat":
                postconditions.add("\\result != null");
                if (call.getArguments().size() == 1) {
                    Expression arg = call.getArguments().get(0);
                    if (arg instanceof IntegerLiteralExpr) {
                        int count = ((IntegerLiteralExpr) arg).asInt();
                        postconditions.add("\\result.length() == " + scopeStr + ".length() * " + count);
                    } else {
                        String argName = arg.toString();
                        postconditions.add("\\result.length() == " + scopeStr + ".length() * " + argName);
                    }
                }
                break;

            // Replace operations
            case "replace":
            case "replaceAll":
            case "replaceFirst":
                postconditions.add("\\result != null");
                // Length can increase or decrease depending on replacement
                break;

            // Split returns array
            case "split":
                postconditions.add("\\result != null");
                postconditions.add("\\result.length >= 1");
                break;

            // Character access
            case "charAt":
                // Returns a char, not a String
                break;

            // Comparison methods return boolean
            case "equals":
            case "equalsIgnoreCase":
            case "startsWith":
            case "endsWith":
            case "contains":
            case "matches":
            case "isEmpty":
            case "isBlank":
                // Boolean return, no String postconditions
                break;

            // Methods returning int
            case "length":
            case "indexOf":
            case "lastIndexOf":
            case "compareTo":
            case "compareToIgnoreCase":
                // Int return
                break;

            // Intern returns the same or pooled string
            case "intern":
                postconditions.add("\\result != null");
                postconditions.add("\\result.equals(" + scopeStr + ")");
                break;

            // Default case - at least we know it returns non-null for most String methods
            default:
                postconditions.add("\\result != null");
                break;
        }
    }

    boolean isStringExpression(Expression expr, MethodDeclaration methodDecl) {
        if (expr instanceof StringLiteralExpr) {
            return true;
        }
        if (expr instanceof NameExpr) {
            String name = expr.toString();
            // Check if it's a String parameter
            return methodDecl.getParameters().stream()
                    .anyMatch(p -> p.getNameAsString().equals(name) &&
                                   p.getType().asString().equals("String"));
        }
        if (expr instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr) expr;
            // Common methods that return String
            String methodName = call.getNameAsString();
            return methodName.equals("toString") || methodName.equals("substring") ||
                   methodName.equals("concat") || methodName.equals("toUpperCase") ||
                   methodName.equals("toLowerCase") || methodName.equals("trim") ||
                   methodName.equals("strip") || methodName.equals("replace") ||
                   methodName.equals("replaceAll") || methodName.equals("valueOf") ||
                   methodName.equals("format") || methodName.equals("join");
        }
        return false;
    }

    boolean isStringParameter(String name, MethodDeclaration methodDecl) {
        return methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(name) &&
                               p.getType().asString().equals("String"));
    }
}
