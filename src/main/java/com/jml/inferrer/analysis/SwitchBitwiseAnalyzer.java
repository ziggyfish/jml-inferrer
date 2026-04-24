package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Analyzes switch statements/expressions and bitwise operations for specification inference.
 */
class SwitchBitwiseAnalyzer {

    private static final Logger logger = LoggerFactory.getLogger(SwitchBitwiseAnalyzer.class);

    void analyzeSwitchStatements(MethodDeclaration methodDecl, MethodSpecification spec,
                                  ASTCollector collector) {
        // Analyze switch expressions (Java 14+)
        collector.switchExprs.forEach(switchExpr -> {
            analyzeSwitchCases(switchExpr.getSelector(), switchExpr.getEntries(), spec, true, methodDecl);
        });

        // Analyze traditional switch statements
        collector.switchStmts.forEach(switchStmt -> {
            analyzeSwitchCases(switchStmt.getSelector(), switchStmt.getEntries(), spec, false, methodDecl);
        });
    }

    void analyzeSwitchCases(Expression selector, List<SwitchEntry> entries,
                            MethodSpecification spec, boolean isExpression,
                            MethodDeclaration methodDecl) {
        String selectorStr = selector.toString();
        Set<String> caseValues = new LinkedHashSet<>();
        boolean hasDefault = false;

        // Track the "active" labels for fall-through cases (case A: case B: return X;)
        // — labels accumulate until we hit a case body that yields a value.
        List<String> pendingLabels = new ArrayList<>();
        SymbolicExecutor scopeChecker = new SymbolicExecutor();
        Set<String> paramNames = new LinkedHashSet<>();
        for (var p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());
        boolean selectorSafe = scopeChecker.isMethodScopeSafe(selectorStr, methodDecl, paramNames);

        for (SwitchEntry entry : entries) {
            if (entry.getLabels().isEmpty()) {
                hasDefault = true;
            } else {
                entry.getLabels().forEach(label -> caseValues.add(label.toString()));
                entry.getLabels().forEach(label -> pendingLabels.add(label.toString()));
            }

            String yieldedExpr = extractCaseYield(entry);
            if (yieldedExpr != null && selectorSafe && !pendingLabels.isEmpty()
                    && scopeChecker.isMethodScopeSafe(yieldedExpr, methodDecl, paramNames)) {
                String guard;
                if (pendingLabels.size() == 1) {
                    guard = selectorStr + " == " + pendingLabels.get(0);
                } else {
                    guard = pendingLabels.stream()
                            .map(l -> selectorStr + " == " + l)
                            .collect(java.util.stream.Collectors.joining(" || ", "(", ")"));
                }
                spec.addPostcondition(guard + " ==> " + AnalysisUtils.buildResultEquality(yieldedExpr),
                        MethodSpecification.ConfidenceLevel.HIGH);
                pendingLabels.clear();
            }
        }

        if (hasDefault || isExpression) {
            if (!methodDecl.getType().isVoidType() && !methodDecl.getType().isPrimitiveType()) {
                spec.addPostcondition("\\result != null",
                        MethodSpecification.ConfidenceLevel.HIGH);
            }
        }

        boolean selectorIsParam = spec.getPreconditions().stream()
                .anyMatch(p -> p.contains(selectorStr));

        if (!caseValues.isEmpty() && selectorIsParam) {
            try {
                List<Integer> intValues = caseValues.stream()
                        .map(Integer::parseInt)
                        .sorted()
                        .toList();

                if (!intValues.isEmpty()) {
                    int min = intValues.get(0);
                    int max = intValues.get(intValues.size() - 1);
                    spec.addPrecondition(selectorStr + " >= " + min + " && " + selectorStr + " <= " + max,
                            MethodSpecification.ConfidenceLevel.MEDIUM);
                }
            } catch (NumberFormatException e) {
                // Not integer cases, might be enum or string
            }
        }
    }

    void analyzeBitwiseOperations(MethodDeclaration methodDecl, MethodSpecification spec,
                                   ASTCollector collector) {
        // These analyzers emit numeric bounds on \result. Skip when the method doesn't
        // return a numeric value — emitting `\result >= 0` on a boolean-returning method
        // is rejected by OpenJML as a type mismatch.
        if (!AnalysisUtils.isNumericType(methodDecl.getType())) return;

        collector.binaryExprs.forEach(binExpr -> {
            BinaryExpr.Operator op = binExpr.getOperator();

            switch (op) {
                case BINARY_AND:
                    analyzeBitwiseAnd(binExpr, methodDecl, spec);
                    break;
                case BINARY_OR:
                    analyzeBitwiseOr(binExpr, methodDecl, spec);
                    break;
                case XOR:
                    analyzeBitwiseXor(binExpr, methodDecl, spec);
                    break;
                case LEFT_SHIFT:
                    analyzeLeftShift(binExpr, methodDecl, spec);
                    break;
                case SIGNED_RIGHT_SHIFT:
                case UNSIGNED_RIGHT_SHIFT:
                    analyzeRightShift(binExpr, methodDecl, spec);
                    break;
            }
        });
    }

    /**
     * True when {@code binExpr} is itself the top-level expression of the enclosing
     * return statement (i.e., {@code return binExpr;}). When it's a subexpression of
     * a larger return (e.g. {@code return (a << 16) | (low & 0xFFFF);} and binExpr
     * is the inner {@code low & 0xFFFF}), the bounds we derive for binExpr don't
     * apply to the whole result — they'd produce unsound postconditions.
     */
    private boolean isTopLevelReturnExpression(BinaryExpr binExpr) {
        ReturnStmt rs = binExpr.findAncestor(ReturnStmt.class).orElse(null);
        if (rs == null) return false;
        return rs.getExpression().map(e -> e == binExpr).orElse(false);
    }

    private void analyzeBitwiseAnd(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        Expression left = binExpr.getLeft();
        Expression right = binExpr.getRight();

        if (right instanceof IntegerLiteralExpr) {
            int mask = ((IntegerLiteralExpr) right).asInt();
            if (mask >= 0 && isTopLevelReturnExpression(binExpr)) {
                spec.addPostcondition("\\result >= 0", MethodSpecification.ConfidenceLevel.HIGH);
                spec.addPostcondition("\\result <= " + mask, MethodSpecification.ConfidenceLevel.HIGH);
            }
        }

        if (right instanceof IntegerLiteralExpr &&
            ((IntegerLiteralExpr) right).asInt() == 1 &&
            isTopLevelReturnExpression(binExpr)) {
            spec.addPostcondition("\\result == 0 || \\result == 1",
                    MethodSpecification.ConfidenceLevel.HIGH);
        }
    }

    private void analyzeBitwiseOr(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        Expression left = binExpr.getLeft();
        Expression right = binExpr.getRight();

        if (right instanceof IntegerLiteralExpr) {
            int value = ((IntegerLiteralExpr) right).asInt();
            if (value >= 0 && isTopLevelReturnExpression(binExpr)) {
                spec.addPostcondition("\\result >= " + value, MethodSpecification.ConfidenceLevel.MEDIUM);
            }
        }
    }

    private void analyzeBitwiseXor(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        if (binExpr.getLeft().toString().equals(binExpr.getRight().toString())
                && isTopLevelReturnExpression(binExpr)) {
            spec.addPostcondition("\\result == 0", MethodSpecification.ConfidenceLevel.HIGH);
        }
    }

    private void analyzeLeftShift(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        Expression right = binExpr.getRight();

        if (right instanceof IntegerLiteralExpr) {
            if (isTopLevelReturnExpression(binExpr)
                    && AnalysisUtils.isNonNegativeExpression(binExpr.getLeft(), methodDecl)) {
                spec.addPostcondition("\\result >= 0", MethodSpecification.ConfidenceLevel.HIGH);
            }
        }
    }

    /**
     * Returns the expression a switch entry yields/returns, or {@code null} if the entry
     * has no clear single-expression yield (multiple statements, void body, throws, etc.).
     * Handles:
     *   case X -> expr;        (switch-expression arrow form)
     *   case X: return expr;   (switch-statement return)
     *   case X: yield expr;    (switch-statement yield)
     *   fall-through (case X: case Y: return expr;) is handled by the caller.
     */
    private String extractCaseYield(SwitchEntry entry) {
        var stmts = entry.getStatements();
        if (stmts.isEmpty()) return null;

        // Switch-expression arrow form: single ExpressionStmt yielding the value
        if (entry.getType() == SwitchEntry.Type.EXPRESSION && stmts.size() == 1
                && stmts.get(0) instanceof ExpressionStmt es) {
            return es.getExpression().toString();
        }

        // Walk statements to find a return/yield, ignoring break
        for (Statement s : stmts) {
            if (s instanceof BreakStmt) continue;
            if (s instanceof ReturnStmt rs) {
                return rs.getExpression().map(Object::toString).orElse(null);
            }
            if (s instanceof YieldStmt ys) {
                return ys.getExpression().toString();
            }
            if (s instanceof BlockStmt bs && bs.getStatements().size() == 1) {
                Statement only = bs.getStatements().get(0);
                if (only instanceof ReturnStmt rs) {
                    return rs.getExpression().map(Object::toString).orElse(null);
                }
                if (only instanceof YieldStmt ys) {
                    return ys.getExpression().toString();
                }
            }
            // Any other statement (assignment, throw, side-effect) means we can't summarise this case
            return null;
        }
        return null;
    }

    private void analyzeRightShift(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        if (!isTopLevelReturnExpression(binExpr)) return;
        boolean isUnsigned = binExpr.getOperator() == BinaryExpr.Operator.UNSIGNED_RIGHT_SHIFT;

        if (isUnsigned) {
            spec.addPostcondition("\\result >= 0", MethodSpecification.ConfidenceLevel.HIGH);
        }

        Expression right = binExpr.getRight();
        if (right instanceof IntegerLiteralExpr) {
            String leftStr = binExpr.getLeft().toString();
            if (AnalysisUtils.isNonNegativeExpression(binExpr.getLeft(), methodDecl)) {
                spec.addPostcondition("\\result <= " + leftStr, MethodSpecification.ConfidenceLevel.MEDIUM);
            }
        }
    }
}
