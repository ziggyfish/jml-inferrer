package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.Type;

/**
 * Shared utility methods used by multiple analyzers.
 */
class AnalysisUtils {

    static boolean isNumericType(Type type) {
        String typeStr = type.asString();
        return typeStr.equals("int") || typeStr.equals("long") || typeStr.equals("double") ||
               typeStr.equals("float") || typeStr.equals("Integer") || typeStr.equals("Long") ||
               typeStr.equals("Double") || typeStr.equals("Float");
    }

    static boolean isReferenceType(String type) {
        return !type.equals("int") && !type.equals("long") && !type.equals("double") &&
               !type.equals("float") && !type.equals("boolean") && !type.equals("char") &&
               !type.equals("byte") && !type.equals("short") && !type.equals("void");
    }

    static boolean isCollectionType(String type) {
        return type.contains("List") || type.contains("Set") || type.contains("Collection") ||
               type.contains("Map") || type.contains("ArrayList") || type.contains("HashSet") ||
               type.contains("HashMap") || type.contains("LinkedList");
    }

    /**
     * Returns true if the expression string is compound (contains arithmetic operators
     * at the top level) and should be wrapped in parentheses when substituted.
     */
    static boolean isCompoundExpression(String expr) {
        if (expr == null || expr.isEmpty()) return false;
        // Simple identifier, literal, or method call — no parens needed
        if (expr.matches("[a-zA-Z_][a-zA-Z0-9_.]*") || expr.matches("-?\\d+(\\.\\d+)?")) return false;
        // Only treat as already-parenthesized if the opening '(' matches the closing ')'
        if (expr.startsWith("(") && expr.endsWith(")")) {
            int depth = 0;
            boolean outerMatch = true;
            for (int i = 0; i < expr.length() - 1; i++) {
                if (expr.charAt(i) == '(') depth++;
                else if (expr.charAt(i) == ')') depth--;
                if (depth == 0) { outerMatch = false; break; }
            }
            if (outerMatch) return false;
        }
        // Contains an arithmetic/bitwise operator outside of parentheses/method calls
        int depth = 0;
        for (int i = 0; i < expr.length(); i++) {
            char ch = expr.charAt(i);
            if (ch == '(' || ch == '[') depth++;
            else if (ch == ')' || ch == ']') depth--;
            else if (depth == 0 && (ch == '+' || ch == '-' || ch == '*' || ch == '/' || ch == '%'
                    || ch == '&' || ch == '|' || ch == '^')) {
                // Ignore unary minus at start
                if (ch == '-' && i == 0) continue;
                return true;
            }
        }
        return false;
    }

    /**
     * Returns true if the expression is a string literal (starts and ends with double quotes).
     */
    static boolean isStringLiteral(String expr) {
        if (expr == null) return false;
        return expr.startsWith("\"") && expr.endsWith("\"");
    }

    /**
     * Returns true if the resolved expression is trivial (single identifier, literal, or this).
     */
    static boolean isTrivialResult(String expr) {
        if (expr == null) return true;
        if (expr.matches("[a-zA-Z_][a-zA-Z0-9_]*")) return true; // Single identifier
        if (expr.matches("-?\\d+(\\.\\d+)?")) return true;        // Single literal
        if (expr.equals("this")) return true;
        // Expressions with 'new' are not valid in JML postconditions
        if (expr.contains("new ")) return true;
        // Ternary expressions can cause operator precedence issues in JML
        if (expr.contains("?") && expr.contains(":")) return true;
        return false;
    }

    /**
     * Builds a result equality postcondition. Uses {@code .equals()} for string literals
     * (since JML {@code ==} is reference equality), and {@code ==} for everything else.
     */
    static String buildResultEquality(String resolvedExpr) {
        if (isStringLiteral(resolvedExpr)) {
            return "\\result.equals(" + resolvedExpr + ")";
        }
        // Parenthesize expressions containing comparison/equality/logical operators to avoid
        // ambiguous precedence like \result == a == b
        if (resolvedExpr.matches(".*[=!<>]=.*") ||
            resolvedExpr.matches(".*(?<!=)>(?!=).*") ||
            resolvedExpr.matches(".*(?<!=)<(?!=).*") ||
            resolvedExpr.contains("&&") || resolvedExpr.contains("||")) {
            return "\\result == (" + resolvedExpr + ")";
        }
        return "\\result == " + resolvedExpr;
    }

    /**
     * Converts a BinaryExpr.Operator to its string representation.
     */
    static String getOperatorString(BinaryExpr.Operator operator) {
        return switch (operator) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            case DIVIDE -> "/";
            case REMAINDER -> "%";
            case AND -> "&&";
            case OR -> "||";
            default -> null;
        };
    }

    /**
     * Converts a compound AssignExpr.Operator to its string representation.
     */
    static String getCompoundOperatorString(AssignExpr.Operator operator) {
        return switch (operator) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            case DIVIDE -> "/";
            case REMAINDER -> "%";
            case BINARY_AND -> "&";
            case BINARY_OR -> "|";
            case XOR -> "^";
            case LEFT_SHIFT -> "<<";
            case SIGNED_RIGHT_SHIFT -> ">>";
            case UNSIGNED_RIGHT_SHIFT -> ">>>";
            default -> null;
        };
    }

    static boolean isFieldReference(MethodDeclaration methodDecl, String name) {
        // Check if name refers to a field (not a parameter or local variable)
        boolean isParameter = methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(name));
        if (isParameter) return false;

        // Check if it's a local variable
        boolean isLocalVar = methodDecl.findAll(com.github.javaparser.ast.expr.VariableDeclarationExpr.class).stream()
                .flatMap(vd -> vd.getVariables().stream())
                .anyMatch(v -> v.getNameAsString().equals(name));
        if (isLocalVar) return false;

        // Assume it's a field if not param or local
        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(c -> c.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .anyMatch(v -> v.getNameAsString().equals(name)))
                .orElse(false);
    }

    static boolean isFieldReference(MethodDeclaration methodDecl, String name, ASTCollector collector) {
        boolean isParameter = methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(name));
        if (isParameter) return false;

        boolean isLocalVar = collector.varDeclExprs.stream()
                .flatMap(vd -> vd.getVariables().stream())
                .anyMatch(v -> v.getNameAsString().equals(name));
        if (isLocalVar) return false;

        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(c -> c.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .anyMatch(v -> v.getNameAsString().equals(name)))
                .orElse(false);
    }

    static String negateCondition(Expression condition) {
        if (condition instanceof BinaryExpr) {
            BinaryExpr binExpr = (BinaryExpr) condition;
            BinaryExpr.Operator op = binExpr.getOperator();
            String left = binExpr.getLeft().toString();
            String right = binExpr.getRight().toString();

            return switch (op) {
                case EQUALS -> left + " != " + right;
                case NOT_EQUALS -> left + " == " + right;
                case LESS -> left + " >= " + right;
                case LESS_EQUALS -> left + " > " + right;
                case GREATER -> left + " <= " + right;
                case GREATER_EQUALS -> left + " < " + right;
                default -> "!(" + condition + ")";
            };
        }
        return "!(" + condition + ")";
    }

    /**
     * Checks if an expression is known to be non-negative.
     */
    static boolean isNonNegativeExpression(Expression expr, MethodDeclaration methodDecl) {
        if (expr instanceof IntegerLiteralExpr) {
            return ((IntegerLiteralExpr) expr).asInt() >= 0;
        }

        if (expr instanceof MethodCallExpr) {
            String name = ((MethodCallExpr) expr).getNameAsString();
            return name.equals("abs") || name.equals("length") || name.equals("size");
        }

        if (isSelfMultiplication(expr)) {
            return true;
        }

        // Check if it's a parameter with a non-negative precondition
        if (expr instanceof NameExpr) {
            String name = expr.toString();
            // Would need to check preconditions, but for simplicity return false
        }

        return false;
    }

    /**
     * Returns true if the expression is x * x (self-multiplication), which guarantees >= 0.
     */
    static boolean isSelfMultiplication(Expression expr) {
        if (expr instanceof BinaryExpr) {
            BinaryExpr bin = (BinaryExpr) expr;
            if (bin.getOperator() == BinaryExpr.Operator.MULTIPLY &&
                bin.getLeft() instanceof NameExpr && bin.getRight() instanceof NameExpr &&
                ((NameExpr) bin.getLeft()).getNameAsString()
                    .equals(((NameExpr) bin.getRight()).getNameAsString())) {
                return true;
            }
        }
        return false;
    }
}
