package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.IfStmt;

import java.util.*;

/**
 * Analyzes field modifications to infer postconditions about field state changes.
 */
class FieldModificationAnalyzer {

    void analyzeFieldModifications(MethodDeclaration methodDecl, Set<String> postconditions,
                                     ASTCollector collector) {
        // Collect all field names from the class
        Set<String> fieldNames = new LinkedHashSet<>();
        methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
            .ifPresent(classDecl -> classDecl.getFields().forEach(field ->
                field.getVariables().forEach(var -> fieldNames.add(var.getNameAsString()))));

        Map<String, Long> fieldDeltas = new LinkedHashMap<>();
        Set<String> nonAdditiveFields = new LinkedHashSet<>();

        java.util.function.Function<Expression, String> getFieldName = target -> {
            if (target instanceof FieldAccessExpr) {
                FieldAccessExpr fa = (FieldAccessExpr) target;
                if (fa.getScope().toString().equals("this") && fieldNames.contains(fa.getNameAsString())) {
                    return fa.getNameAsString();
                }
            } else if (target instanceof NameExpr) {
                String name = ((NameExpr) target).getNameAsString();
                if (fieldNames.contains(name)) {
                    return name;
                }
            }
            return null;
        };

        Set<String> conditionalFields = new LinkedHashSet<>();

        // Pass 1: Process unary expressions (++, --)
        collector.unaryExprs.forEach(unaryExpr -> {
            Expression expr = unaryExpr.getExpression();
            String name = getFieldName.apply(expr);
            if (name != null) {
                String branchCond = getEnclosingBranchCondition(unaryExpr, methodDecl);
                long delta = 0;
                if (unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                    unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT) {
                    delta = 1;
                } else if (unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT ||
                           unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT) {
                    delta = -1;
                }
                if (delta != 0) {
                    if (branchCond != null) {
                        conditionalFields.add(name);
                        String op = delta > 0 ? "+" : "-";
                        postconditions.add(branchCond + " ==> this." + name + " == \\old(this." + name + ") " + op + " " + Math.abs(delta));
                    } else {
                        fieldDeltas.merge(name, delta, Long::sum);
                    }
                }
            }
        });

        // Pass 2: Process assignment expressions
        collector.assignExprs.forEach(assign -> {
            String name = getFieldName.apply(assign.getTarget());
            if (name == null) return;

            Expression value = assign.getValue();
            AssignExpr.Operator operator = assign.getOperator();
            String branchCond = getEnclosingBranchCondition(assign, methodDecl);

            if (operator == AssignExpr.Operator.PLUS && value instanceof IntegerLiteralExpr) {
                if (branchCond != null) {
                    conditionalFields.add(name);
                    long delta = (long) ((IntegerLiteralExpr) value).asInt();
                    String op = delta >= 0 ? "+" : "-";
                    postconditions.add(branchCond + " ==> this." + name + " == \\old(this." + name + ") " + op + " " + Math.abs(delta));
                } else {
                    fieldDeltas.merge(name, (long) ((IntegerLiteralExpr) value).asInt(), Long::sum);
                }
            } else if (operator == AssignExpr.Operator.MINUS && value instanceof IntegerLiteralExpr) {
                if (branchCond != null) {
                    conditionalFields.add(name);
                    long delta = (long) ((IntegerLiteralExpr) value).asInt();
                    postconditions.add(branchCond + " ==> this." + name + " == \\old(this." + name + ") - " + delta);
                } else {
                    fieldDeltas.merge(name, -(long) ((IntegerLiteralExpr) value).asInt(), Long::sum);
                }
            } else if (operator == AssignExpr.Operator.PLUS || operator == AssignExpr.Operator.MINUS) {
                String operatorStr = AnalysisUtils.getCompoundOperatorString(operator);
                if (operatorStr != null) {
                    String postcond = "this." + name + " == \\old(this." + name + ") " + operatorStr + " " + value;
                    if (branchCond != null) {
                        postconditions.add(branchCond + " ==> " + postcond);
                    } else {
                        postconditions.add(postcond);
                    }
                }
                nonAdditiveFields.add(name);
            } else if (operator != AssignExpr.Operator.ASSIGN) {
                String operatorStr = AnalysisUtils.getCompoundOperatorString(operator);
                if (operatorStr != null) {
                    String postcond = "this." + name + " == \\old(this." + name + ") " + operatorStr + " " + value;
                    if (branchCond != null) {
                        postconditions.add(branchCond + " ==> " + postcond);
                    } else {
                        postconditions.add(postcond);
                    }
                }
                nonAdditiveFields.add(name);
            } else {
                String postcond = generateFieldAssignPostcondition(name, value, operator, methodDecl);
                if (postcond != null) {
                    if (branchCond != null) {
                        postconditions.add(branchCond + " ==> " + postcond);
                    } else {
                        postconditions.add(postcond);
                    }
                }
                nonAdditiveFields.add(name);
            }
        });

        // Pass 3: Generate accumulated delta postconditions (unconditional only)
        for (Map.Entry<String, Long> entry : fieldDeltas.entrySet()) {
            String name = entry.getKey();
            long delta = entry.getValue();
            if (nonAdditiveFields.contains(name)) continue;
            if (conditionalFields.contains(name)) continue;
            if (delta == 0) continue;

            String op = delta > 0 ? "+" : "-";
            long absDelta = Math.abs(delta);
            postconditions.add("this." + name + " == \\old(this." + name + ") " + op + " " + absDelta);
        }
    }

    String generateFieldAssignPostcondition(String fieldName, Expression value,
            AssignExpr.Operator operator, MethodDeclaration methodDecl) {
        if (value instanceof IntegerLiteralExpr ||
            value instanceof DoubleLiteralExpr || value instanceof StringLiteralExpr ||
            value instanceof BooleanLiteralExpr || value instanceof LongLiteralExpr ||
            value instanceof CharLiteralExpr || value instanceof NullLiteralExpr) {
            return "this." + fieldName + " == " + value;
        } else if (value instanceof NameExpr) {
            String name = ((NameExpr) value).getNameAsString();
            boolean isParam = methodDecl.getParameters().stream()
                    .anyMatch(p -> p.getNameAsString().equals(name));
            if (isParam) {
                return "this." + fieldName + " == " + name;
            }
            boolean isField = methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .map(cls -> cls.getFields().stream()
                            .flatMap(f -> f.getVariables().stream())
                            .anyMatch(v -> v.getNameAsString().equals(name)))
                    .orElse(false);
            if (isField) {
                return "this." + fieldName + " == \\old(this." + name + ")";
            }
            return null;
        } else if (value instanceof ArrayAccessExpr) {
            return "this." + fieldName + " == " + value;
        } else if (value instanceof FieldAccessExpr) {
            FieldAccessExpr fa = (FieldAccessExpr) value;
            if (fa.getScope().toString().equals("this")) {
                return "this." + fieldName + " == \\old(this." + fa.getNameAsString() + ")";
            }
            return "this." + fieldName + " == " + value;
        } else if (value instanceof UnaryExpr) {
            UnaryExpr unary = (UnaryExpr) value;
            if (unary.isPrefix()) {
                Expression inner = unary.getExpression();
                if (inner instanceof FieldAccessExpr) {
                    FieldAccessExpr fa = (FieldAccessExpr) inner;
                    if (fa.getScope().toString().equals("this")) {
                        String op = unary.getOperator().asString();
                        return "this." + fieldName + " == " + op + "\\old(this." + fa.getNameAsString() + ")";
                    }
                } else if (inner instanceof NameExpr) {
                    String name = ((NameExpr) inner).getNameAsString();
                    boolean isField = methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                            .map(cls -> cls.getFields().stream()
                                    .flatMap(f -> f.getVariables().stream())
                                    .anyMatch(v -> v.getNameAsString().equals(name)))
                            .orElse(false);
                    if (isField) {
                        String op = unary.getOperator().asString();
                        return "this." + fieldName + " == " + op + "\\old(this." + name + ")";
                    }
                }
                return "this." + fieldName + " == " + value;
            }
        } else if (value instanceof CastExpr) {
            CastExpr cast = (CastExpr) value;
            if (cast.getExpression() instanceof NameExpr ||
                cast.getExpression() instanceof LiteralExpr) {
                return "this." + fieldName + " == " + value;
            }
        } else if (value instanceof EnclosedExpr) {
            return generateFieldAssignPostcondition(fieldName,
                    ((EnclosedExpr) value).getInner(), operator, methodDecl);
        } else if (value instanceof BinaryExpr) {
            String oldExpr = generateOldExpression(fieldName, (BinaryExpr) value, operator);
            if (oldExpr != null) {
                return oldExpr;
            }
            BinaryExpr bin = (BinaryExpr) value;
            if (isSimpleJMLExpression(bin.getLeft()) && isSimpleJMLExpression(bin.getRight())) {
                return "this." + fieldName + " == " + value;
            }
        } else if (value instanceof ConditionalExpr) {
            return null;
        }
        return null;
    }

    private boolean isSimpleJMLExpression(Expression expr) {
        return expr instanceof NameExpr || expr instanceof LiteralExpr ||
               expr instanceof FieldAccessExpr || expr instanceof ArrayAccessExpr ||
               expr instanceof ThisExpr ||
               (expr instanceof UnaryExpr && ((UnaryExpr) expr).isPrefix() &&
                isSimpleJMLExpression(((UnaryExpr) expr).getExpression())) ||
               (expr instanceof EnclosedExpr &&
                isSimpleJMLExpression(((EnclosedExpr) expr).getInner()));
    }

    private String generateOldExpression(String fieldName, BinaryExpr binaryExpr, AssignExpr.Operator assignOp) {
        String left = binaryExpr.getLeft().toString();
        String right = binaryExpr.getRight().toString();
        BinaryExpr.Operator operator = binaryExpr.getOperator();

        boolean leftIsField = left.equals(fieldName) || left.equals("this." + fieldName);
        boolean rightIsField = right.equals(fieldName) || right.equals("this." + fieldName);

        if (assignOp != AssignExpr.Operator.ASSIGN) {
            String operatorStr = switch (assignOp) {
                case PLUS -> "+";
                case MINUS -> "-";
                case MULTIPLY -> "*";
                case DIVIDE -> "/";
                case REMAINDER -> "%";
                default -> null;
            };

            if (operatorStr != null) {
                return "this." + fieldName + " == \\old(this." + fieldName + ") " + operatorStr + " " + binaryExpr;
            }
        }

        if (leftIsField && !rightIsField) {
            String operatorStr = AnalysisUtils.getOperatorString(operator);
            if (operatorStr != null) {
                return "this." + fieldName + " == \\old(this." + fieldName + ") " + operatorStr + " " + right;
            }
        } else if (rightIsField && !leftIsField) {
            String operatorStr = AnalysisUtils.getOperatorString(operator);
            if (operatorStr != null) {
                return "this." + fieldName + " == " + left + " " + operatorStr + " \\old(this." + fieldName + ")";
            }
        }

        return null;
    }

    String getEnclosingBranchCondition(com.github.javaparser.ast.Node node, MethodDeclaration methodDecl) {
        com.github.javaparser.ast.Node current = node;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent == methodDecl.getBody().orElse(null) || parent == methodDecl) {
                return null;
            }
            if (parent instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) parent;
                String rawCond;
                if (current == ifStmt.getThenStmt()) {
                    rawCond = ifStmt.getCondition().toString();
                } else if (ifStmt.getElseStmt().isPresent() && current == ifStmt.getElseStmt().get()) {
                    rawCond = AnalysisUtils.negateCondition(ifStmt.getCondition());
                } else {
                    current = parent;
                    continue;
                }
                return wrapFieldRefsWithOld(rawCond, methodDecl);
            }
            current = parent;
        }
        return null;
    }

    String wrapFieldRefsWithOld(String condition, MethodDeclaration methodDecl) {
        Set<String> fieldNames = methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> {
                    Set<String> names = new LinkedHashSet<>();
                    cls.getFields().stream()
                            .flatMap(f -> f.getVariables().stream())
                            .forEach(v -> names.add(v.getNameAsString()));
                    return names;
                })
                .orElse(Collections.emptySet());

        String result = condition;
        for (String field : fieldNames) {
            String thisField = "this." + field;
            if (result.contains(thisField) && !result.contains("\\old(" + thisField + ")")) {
                result = result.replace(thisField, "\\old(" + thisField + ")");
            }
        }
        return result;
    }
}
