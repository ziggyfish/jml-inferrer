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

        for (SwitchEntry entry : entries) {
            if (entry.getLabels().isEmpty()) {
                hasDefault = true;
            } else {
                entry.getLabels().forEach(label -> caseValues.add(label.toString()));
            }

            entry.getStatements().forEach(stmt -> {
                if (stmt instanceof ReturnStmt) {
                    ReturnStmt returnStmt = (ReturnStmt) stmt;
                    returnStmt.getExpression().ifPresent(returnExpr -> {
                        entry.getLabels().forEach(label -> {
                            String labelStr = label.toString();
                            String returnVal = returnExpr.toString();
                            logger.debug("Switch case {} returns {}", labelStr, returnVal);
                        });
                    });
                }
            });
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

    private void analyzeBitwiseAnd(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        Expression left = binExpr.getLeft();
        Expression right = binExpr.getRight();

        if (right instanceof IntegerLiteralExpr) {
            int mask = ((IntegerLiteralExpr) right).asInt();
            if (mask >= 0) {
                binExpr.findAncestor(ReturnStmt.class).ifPresent(returnStmt -> {
                    spec.addPostcondition("\\result >= 0", MethodSpecification.ConfidenceLevel.HIGH);
                    spec.addPostcondition("\\result <= " + mask, MethodSpecification.ConfidenceLevel.HIGH);
                });
            }
        }

        if (right instanceof IntegerLiteralExpr &&
            ((IntegerLiteralExpr) right).asInt() == 1) {
            binExpr.findAncestor(ReturnStmt.class).ifPresent(returnStmt -> {
                spec.addPostcondition("\\result == 0 || \\result == 1",
                        MethodSpecification.ConfidenceLevel.HIGH);
            });
        }
    }

    private void analyzeBitwiseOr(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        Expression left = binExpr.getLeft();
        Expression right = binExpr.getRight();

        if (right instanceof IntegerLiteralExpr) {
            int value = ((IntegerLiteralExpr) right).asInt();
            if (value >= 0) {
                binExpr.findAncestor(ReturnStmt.class).ifPresent(returnStmt -> {
                    spec.addPostcondition("\\result >= " + value, MethodSpecification.ConfidenceLevel.MEDIUM);
                });
            }
        }
    }

    private void analyzeBitwiseXor(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        if (binExpr.getLeft().toString().equals(binExpr.getRight().toString())) {
            binExpr.findAncestor(ReturnStmt.class).ifPresent(returnStmt -> {
                spec.addPostcondition("\\result == 0", MethodSpecification.ConfidenceLevel.HIGH);
            });
        }
    }

    private void analyzeLeftShift(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        Expression right = binExpr.getRight();

        if (right instanceof IntegerLiteralExpr) {
            int shiftAmount = ((IntegerLiteralExpr) right).asInt();
            long multiplier = 1L << shiftAmount;

            binExpr.findAncestor(ReturnStmt.class).ifPresent(returnStmt -> {
                String leftStr = binExpr.getLeft().toString();
                if (AnalysisUtils.isNonNegativeExpression(binExpr.getLeft(), methodDecl)) {
                    spec.addPostcondition("\\result >= 0", MethodSpecification.ConfidenceLevel.HIGH);
                }
            });
        }
    }

    private void analyzeRightShift(BinaryExpr binExpr, MethodDeclaration methodDecl, MethodSpecification spec) {
        boolean isUnsigned = binExpr.getOperator() == BinaryExpr.Operator.UNSIGNED_RIGHT_SHIFT;

        binExpr.findAncestor(ReturnStmt.class).ifPresent(returnStmt -> {
            if (isUnsigned) {
                spec.addPostcondition("\\result >= 0", MethodSpecification.ConfidenceLevel.HIGH);
            }

            Expression right = binExpr.getRight();
            if (right instanceof IntegerLiteralExpr) {
                int shiftAmount = ((IntegerLiteralExpr) right).asInt();

                String leftStr = binExpr.getLeft().toString();
                if (AnalysisUtils.isNonNegativeExpression(binExpr.getLeft(), methodDecl)) {
                    spec.addPostcondition("\\result <= " + leftStr, MethodSpecification.ConfidenceLevel.MEDIUM);
                }
            }
        });
    }
}
