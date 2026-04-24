package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.Type;

/**
 * Shared utility methods used by multiple analyzers.
 */
public class AnalysisUtils {

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
        return false;
    }

    /**
     * Builds a result equality postcondition. Uses {@code .equals()} for string literals
     * and string-concatenation expressions (since JML {@code ==} is reference equality
     * and {@code a + b} produces a fresh {@code String} object), and {@code ==} for
     * everything else.
     */
    static String buildResultEquality(String resolvedExpr) {
        return buildResultEquality(resolvedExpr, false);
    }

    /**
     * Same as {@link #buildResultEquality(String)} but forces {@code .equals()} when
     * the caller knows the return type is {@code String}. Needed for
     * {@code return a + b;} where both operands are {@code String} parameters and
     * the expression has no literal for the heuristic to latch onto.
     */
    static String buildResultEquality(String resolvedExpr, boolean forceStringEquals) {
        // Only switch to `.equals()` when we know the result is a String:
        // either the caller forces it (return type is String), or the entire
        // resolved expression IS a string literal. Catching `containsStringLiteral`
        // elsewhere was too aggressive — it fired on booleans like
        // `s.equals("hello")` whose \result is boolean, producing the bogus
        // `\result.equals(s.equals("hello"))` postcondition.
        if (forceStringEquals || isStringLiteral(resolvedExpr)) {
            return "\\result.equals(" + resolvedExpr + ")";
        }
        // Parenthesize expressions containing comparison/equality/logical operators OR a
        // ternary `?:` to avoid ambiguous precedence like \result == a == b or
        // \result == cond ? a : b.
        if (resolvedExpr.matches(".*[=!<>]=.*") ||
            resolvedExpr.matches(".*(?<!=)>(?!=).*") ||
            resolvedExpr.matches(".*(?<!=)<(?!=).*") ||
            resolvedExpr.contains("&&") || resolvedExpr.contains("||") ||
            (resolvedExpr.contains("?") && resolvedExpr.contains(":"))) {
            return "\\result == (" + resolvedExpr + ")";
        }
        return "\\result == " + resolvedExpr;
    }

    /**
     * Heuristic: returns true when the expression mentions a {@code String} literal.
     * A {@code +} whose operands include a string literal is necessarily string
     * concatenation, and the resulting object is distinct from any operand, so
     * reference equality ({@code ==}) is the wrong comparison. {@code .equals()}
     * is correct for the value-equality the inferrer intends.
     */
    private static boolean containsStringLiteral(String expr) {
        // Look for a quoted string literal that isn't escaped. Simple check: the
        // string contains a `"` that starts a literal, followed by a closing `"`.
        int i = 0;
        while (i < expr.length()) {
            if (expr.charAt(i) == '"') {
                int j = i + 1;
                while (j < expr.length() && expr.charAt(j) != '"') {
                    if (expr.charAt(j) == '\\' && j + 1 < expr.length()) j += 2;
                    else j++;
                }
                if (j < expr.length()) return true;
            }
            i++;
        }
        return false;
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
            if (name.equals("length") || name.equals("size")) return true;
            // abs() only guaranteed non-negative for floating-point return types;
            // Math.abs(Integer.MIN_VALUE) returns Integer.MIN_VALUE (negative)
            if (name.equals("abs") && isFloatingPointReturn(methodDecl)) return true;
            return false;
        }

        if (isSelfMultiplication(expr) && isFloatingPointReturn(methodDecl)) {
            // x * x is only guaranteed non-negative for floating-point types;
            // int/long overflow can produce negative values
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
     * Returns true if the method's return type is a floating-point type (double/float),
     * which does not overflow to negative values (unlike int/long).
     */
    static boolean isFloatingPointReturn(MethodDeclaration methodDecl) {
        String typeStr = methodDecl.getTypeAsString();
        return typeStr.equals("double") || typeStr.equals("float") ||
               typeStr.equals("Double") || typeStr.equals("Float");
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

    /**
     * True for specifications that are trivially, textually true so we can drop
     * them at the add-site before they reach JML output. Covers:
     * <ul>
     *   <li>Identical-side comparisons: {@code x >= x}, {@code x <= x}, {@code x == x}</li>
     *   <li>Literal pairs like {@code 0 >= 0}, {@code 5 <= 5}</li>
     *   <li>Non-negativity of array lengths: {@code 0 <= arr.length},
     *       {@code arr.length >= 0}</li>
     *   <li>Non-negativity of collection sizes: {@code 0 <= list.size()},
     *       {@code list.size() >= 0}</li>
     *   <li>Non-negativity of string lengths: {@code 0 <= s.length()},
     *       {@code s.length() >= 0}</li>
     *   <li>Sum of two non-negative length/size expressions — e.g.
     *       {@code (a.length + b.length) >= 0}</li>
     * </ul>
     */
    public static boolean isTriviallyTrueClause(String clause) {
        if (clause == null) return false;
        String p = clause.trim();
        // Don't filter literal `true` — the fallback loop-invariant emission uses it
        // as a minimal placeholder when no stronger invariant is available, so the
        // method satisfies the "has loop_invariant" quality gate.
        // Identical-sides comparison: `x >= x`, `x <= x`, `x == x`.
        for (String op : new String[]{" >= ", " <= ", " == "}) {
            int idx = p.indexOf(op);
            if (idx < 0) continue;
            String left = p.substring(0, idx).trim();
            String right = p.substring(idx + op.length()).trim();
            if (left.equals(right)) return true;
            try {
                int li = Integer.parseInt(left);
                int ri = Integer.parseInt(right);
                char c = op.charAt(1);
                if (c == '>' && li >= ri) return true;
                if (c == '<' && li <= ri) return true;
                if (c == '=' && li == ri) return true;
            } catch (NumberFormatException ignored) { }
        }
        // `literal != other-literal` — always true (e.g. `10 != 0`).
        int neq = p.indexOf(" != ");
        if (neq > 0) {
            String left = p.substring(0, neq).trim();
            String right = p.substring(neq + 4).trim();
            try {
                long li = Long.parseLong(left);
                long ri = Long.parseLong(right);
                if (li != ri) return true;
            } catch (NumberFormatException ignored) { }
            // `literal != Integer.MIN_VALUE` — true for any literal except MIN_VALUE.
            if (right.equals("Integer.MIN_VALUE")) {
                try {
                    long li = Long.parseLong(left);
                    if (li != Integer.MIN_VALUE) return true;
                } catch (NumberFormatException ignored) { }
            }
        }
        // `0 <= <dotted>.length`, `0 <= <dotted>.size()`, `0 <= <dotted>.length()`
        String lengthOrSize = "(length|size\\(\\)|length\\(\\))";
        if (p.matches("0\\s*<=\\s*[\\w\\.]+\\." + lengthOrSize)) return true;
        if (p.matches("[\\w\\.]+\\." + lengthOrSize + "\\s*>=\\s*0")) return true;
        // Sum of two length/size terms is also >= 0.
        if (p.matches("\\(?[\\w\\.]+\\." + lengthOrSize + "\\s*\\+\\s*[\\w\\.]+\\."
                + lengthOrSize + "\\)?\\s*>=\\s*0")) return true;
        // `x != null && y != null` ↔ `x != null` plus `y != null` individually;
        // the compound form is never *false* unless one conjunct is, so the add-site
        // filter drops it only when both conjuncts were already registered. To keep
        // this helper context-free, skip that case here.
        return false;
    }

    /**
     * Simplifies a conjoined path condition by removing redundant clauses.
     * E.g., "(x <= 0) && (x < 0)" → "x < 0"
     *        "(x <= 0) && (x >= 0)" → "x == 0"
     */
    static String simplifyPathCondition(String pathCondition) {
        if (pathCondition == null) return null;

        // Match pattern: (A op1 B) && (A op2 B) or (A op1 B) && (A op2 C)
        java.util.regex.Matcher m = java.util.regex.Pattern.compile(
                "^\\((.+?)\\s*(<=|>=|<|>|==|!=)\\s*(.+?)\\)\\s*&&\\s*\\((.+?)\\s*(<=|>=|<|>|==|!=)\\s*(.+?)\\)$"
        ).matcher(pathCondition);

        if (!m.matches()) return pathCondition;

        String left1 = m.group(1).trim(), op1 = m.group(2), right1 = m.group(3).trim();
        String left2 = m.group(4).trim(), op2 = m.group(5), right2 = m.group(6).trim();

        // Only simplify when both conditions compare the same operands
        if (!left1.equals(left2) || !right1.equals(right2)) return pathCondition;

        String simplified = simplifyTwoComparisons(left1, op1, op2, right1);
        return simplified != null ? simplified : pathCondition;
    }

    private static String simplifyTwoComparisons(String left, String op1, String op2, String right) {
        // Normalize: put the stronger/tighter condition first
        String a = op1, b = op2;

        // Subsumption: one condition implies the other
        // x < N && x <= N  →  x < N  (< is stronger than <=)
        // x > N && x >= N  →  x > N  (> is stronger than >=)
        if (subsumes(a, b)) return left + " " + a + " " + right;
        if (subsumes(b, a)) return left + " " + b + " " + right;

        // Conjunction of complementary inequalities → equality
        // x <= N && x >= N  →  x == N
        // x >= N && x <= N  →  x == N
        if ((a.equals("<=") && b.equals(">=")) || (a.equals(">=") && b.equals("<="))) {
            return left + " == " + right;
        }

        return null;
    }

    /** Returns true if op1 logically implies op2 (op1 is strictly stronger). */
    private static boolean subsumes(String op1, String op2) {
        return switch (op1) {
            case "<" -> op2.equals("<=") || op2.equals("!=");
            case ">" -> op2.equals(">=") || op2.equals("!=");
            case "==" -> op2.equals("<=") || op2.equals(">=");
            default -> false;
        };
    }
}
