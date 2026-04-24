package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.IfStmt;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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

        // Count non-loop modifications per field. A field hit by multiple
        // non-additive operations cannot have any single per-step ensures;
        // emitting them produces unsound conjunctive postconditions like
        // `value == \old(value) + a && value == \old(value) - b`.
        Map<String, Integer> nonAdditiveCount = new LinkedHashMap<>();
        for (UnaryExpr u : collector.unaryExprs) {
            String n = (u.getExpression() instanceof FieldAccessExpr fa
                    && fa.getScope().toString().equals("this")
                    && fieldNames.contains(fa.getNameAsString()))
                    ? fa.getNameAsString()
                    : (u.getExpression() instanceof NameExpr ne && fieldNames.contains(ne.getNameAsString())
                            ? ne.getNameAsString() : null);
            if (n == null || isInsideLoop(u)) continue;
            // ++/-- with literal delta is additive — composes safely via fieldDeltas.
            // Skip from non-additive count.
        }
        for (AssignExpr a : collector.assignExprs) {
            String n = (a.getTarget() instanceof FieldAccessExpr fa
                    && fa.getScope().toString().equals("this")
                    && fieldNames.contains(fa.getNameAsString()))
                    ? fa.getNameAsString()
                    : (a.getTarget() instanceof NameExpr ne && fieldNames.contains(ne.getNameAsString())
                            ? ne.getNameAsString() : null);
            if (n == null || isInsideLoop(a)) continue;
            AssignExpr.Operator op = a.getOperator();
            // PLUS/MINUS of an integer literal compose additively (fieldDeltas).
            // Anything else (PLUS/MINUS of a variable, MULTIPLY, ASSIGN) is non-additive.
            boolean additive = (op == AssignExpr.Operator.PLUS || op == AssignExpr.Operator.MINUS)
                    && a.getValue() instanceof IntegerLiteralExpr;
            if (!additive) {
                nonAdditiveCount.merge(n, 1, Integer::sum);
            }
        }
        Set<String> multiplyModifiedFields = new LinkedHashSet<>();
        for (Map.Entry<String, Integer> e : nonAdditiveCount.entrySet()) {
            if (e.getValue() > 1) multiplyModifiedFields.add(e.getKey());
        }

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
                // Skip when the increment is inside a loop — the fixed-delta postcondition
                // `field == \old(field) + 1` is wrong in that case because the loop can run
                // many times. The loop invariant machinery handles those shapes separately.
                if (isInsideLoop(unaryExpr)) {
                    nonAdditiveFields.add(name);
                    return;
                }
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
            // Same rationale as Pass 1: a compound assignment inside a loop can't be
            // summarised as a fixed-delta postcondition.
            if (isInsideLoop(assign)
                    && (operator == AssignExpr.Operator.PLUS
                        || operator == AssignExpr.Operator.MINUS
                        || operator == AssignExpr.Operator.MULTIPLY)) {
                nonAdditiveFields.add(name);
                return;
            }
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
                if (!multiplyModifiedFields.contains(name)) {
                    String operatorStr = AnalysisUtils.getCompoundOperatorString(operator);
                    if (operatorStr != null) {
                        String postcond = "this." + name + " == \\old(this." + name + ") " + operatorStr + " " + value;
                        if (branchCond != null) {
                            postconditions.add(branchCond + " ==> " + postcond);
                        } else {
                            postconditions.add(postcond);
                        }
                    }
                }
                nonAdditiveFields.add(name);
            } else if (operator != AssignExpr.Operator.ASSIGN) {
                if (!multiplyModifiedFields.contains(name)) {
                    String operatorStr = AnalysisUtils.getCompoundOperatorString(operator);
                    if (operatorStr != null) {
                        String postcond = "this." + name + " == \\old(this." + name + ") " + operatorStr + " " + value;
                        if (branchCond != null) {
                            postconditions.add(branchCond + " ==> " + postcond);
                        } else {
                            postconditions.add(postcond);
                        }
                    }
                }
                nonAdditiveFields.add(name);
            } else {
                if (!multiplyModifiedFields.contains(name)) {
                    String postcond = generateFieldAssignPostcondition(name, value, operator, methodDecl);
                    if (postcond != null) {
                        if (branchCond != null) {
                            postconditions.add(branchCond + " ==> " + postcond);
                        } else {
                            postconditions.add(postcond);
                        }
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
                // If the RHS field was modified earlier in the same method, its
                // value at this assignment is POST-state, not pre-state. `\old(...)`
                // would be wrong — emit the post-state reference `this.name` so
                // the generated postcondition relates the two fields in their
                // post-state (e.g. `lastNotifiedValue == this.count` when
                // `count++; lastNotifiedValue = count;`).
                if (isFieldModifiedInMethod(methodDecl, name)) {
                    return "this." + fieldName + " == this." + name;
                }
                return "this." + fieldName + " == \\old(this." + name + ")";
            }
            return null;
        } else if (value instanceof ArrayAccessExpr) {
            return "this." + fieldName + " == " + value;
        } else if (value instanceof FieldAccessExpr) {
            FieldAccessExpr fa = (FieldAccessExpr) value;
            if (fa.getScope().toString().equals("this")) {
                String refName = fa.getNameAsString();
                if (isFieldModifiedInMethod(methodDecl, refName)) {
                    return "this." + fieldName + " == this." + refName;
                }
                return "this." + fieldName + " == \\old(this." + refName + ")";
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
        // Guard-return pattern: if the node sits after an `if (cond) return ...;` at the
        // same block level, it only executes when `!cond`. Collect those implicit guards
        // so the emitted postcondition is correctly scoped.
        List<String> guardNegations = collectGuardReturnNegations(node, methodDecl);

        com.github.javaparser.ast.Node current = node;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent == methodDecl.getBody().orElse(null) || parent == methodDecl) {
                if (!guardNegations.isEmpty()) {
                    return String.join(" && ", guardNegations);
                }
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
                String substituted = substituteLocalInits(rawCond, methodDecl);
                if (substituted == null) {
                    // Condition references a local that can't be resolved to pre-state —
                    // skip the condition rather than emit an invalid JML identifier.
                    return null;
                }
                String wrapped = wrapFieldRefsWithOld(substituted, methodDecl);
                if (!guardNegations.isEmpty()) {
                    List<String> parts = new ArrayList<>(guardNegations);
                    parts.add(wrapped);
                    return String.join(" && ", parts);
                }
                return wrapped;
            }
            if (parent instanceof com.github.javaparser.ast.stmt.SwitchEntry entry) {
                // Find the enclosing switch and emit `selector == label` for the entry's labels
                com.github.javaparser.ast.Node switchNode = entry.getParentNode().orElse(null);
                String selector = null;
                if (switchNode instanceof com.github.javaparser.ast.stmt.SwitchStmt ss) {
                    selector = ss.getSelector().toString();
                } else if (switchNode instanceof com.github.javaparser.ast.expr.SwitchExpr se) {
                    selector = se.getSelector().toString();
                }
                if (selector == null || entry.getLabels().isEmpty()) {
                    current = parent;
                    continue;
                }
                String guard;
                if (entry.getLabels().size() == 1) {
                    guard = selector + " == " + entry.getLabels().get(0).toString();
                } else {
                    final String sel = selector;
                    guard = entry.getLabels().stream()
                            .map(l -> sel + " == " + l.toString())
                            .collect(java.util.stream.Collectors.joining(" || ", "(", ")"));
                }
                return wrapFieldRefsWithOld(guard, methodDecl);
            }
            current = parent;
        }
        return null;
    }

    /**
     * Walks from {@code node} upward, collecting the negated conditions of every
     * earlier sibling that is a guard-return {@code if (cond) return ...;}. These
     * implicit guards mean {@code node} only executes when {@code !cond}, and the
     * emitted postcondition must include them so the ensures is branch-correct.
     */
    private List<String> collectGuardReturnNegations(com.github.javaparser.ast.Node node,
                                                      MethodDeclaration methodDecl) {
        List<String> negations = new ArrayList<>();
        com.github.javaparser.ast.Node current = node;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent instanceof com.github.javaparser.ast.stmt.BlockStmt block) {
                // Look at siblings BEFORE the current statement in this block
                int idx = block.getStatements().indexOf(current);
                if (idx < 0) {
                    // Find the statement-level ancestor
                    com.github.javaparser.ast.Node stmt = current;
                    while (stmt != null && block.getStatements().indexOf(stmt) < 0) {
                        stmt = stmt.getParentNode().orElse(null);
                    }
                    if (stmt == null) break;
                    idx = block.getStatements().indexOf(stmt);
                }
                for (int i = 0; i < idx; i++) {
                    com.github.javaparser.ast.stmt.Statement sibling = block.getStatement(i);
                    if (sibling instanceof IfStmt ifStmt
                            && ifStmt.getElseStmt().isEmpty()
                            && alwaysReturnsOrThrows(ifStmt.getThenStmt())) {
                        String rawCond = AnalysisUtils.negateCondition(ifStmt.getCondition());
                        String substituted = substituteLocalInits(rawCond, methodDecl);
                        if (substituted != null) {
                            negations.add("(" + wrapFieldRefsWithOld(substituted, methodDecl) + ")");
                        }
                    }
                }
            }
            current = parent;
            if (parent == methodDecl || parent == methodDecl.getBody().orElse(null)) break;
        }
        return negations;
    }

    private boolean isInsideLoop(com.github.javaparser.ast.Node node) {
        com.github.javaparser.ast.Node cur = node;
        while (cur.getParentNode().isPresent()) {
            cur = cur.getParentNode().get();
            if (cur instanceof com.github.javaparser.ast.stmt.ForStmt
                    || cur instanceof com.github.javaparser.ast.stmt.WhileStmt
                    || cur instanceof com.github.javaparser.ast.stmt.DoStmt
                    || cur instanceof com.github.javaparser.ast.stmt.ForEachStmt) {
                return true;
            }
        }
        return false;
    }

    private boolean alwaysReturnsOrThrows(com.github.javaparser.ast.stmt.Statement stmt) {
        if (stmt instanceof com.github.javaparser.ast.stmt.ReturnStmt) return true;
        if (stmt instanceof com.github.javaparser.ast.stmt.ThrowStmt) return true;
        if (stmt instanceof com.github.javaparser.ast.stmt.BlockStmt block) {
            for (com.github.javaparser.ast.stmt.Statement s : block.getStatements()) {
                if (s instanceof com.github.javaparser.ast.stmt.ReturnStmt
                        || s instanceof com.github.javaparser.ast.stmt.ThrowStmt) return true;
            }
        }
        return false;
    }

    /**
     * Substitutes local-variable identifiers in {@code condition} with their
     * initializer expressions (recursively). Returns {@code null} if any local
     * can't be resolved to a pre-state expression (params, fields, literals).
     */
    private String substituteLocalInits(String condition, MethodDeclaration methodDecl) {
        // Collect params, fields, local initializers.
        Set<String> paramNames = new HashSet<>();
        methodDecl.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));
        Set<String> fieldNames = methodDecl.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .map(com.github.javaparser.ast.body.VariableDeclarator::getNameAsString)
                        .collect(java.util.stream.Collectors.toSet()))
                .orElseGet(HashSet::new);
        Map<String, String> localInits = new HashMap<>();
        methodDecl.findAll(com.github.javaparser.ast.expr.VariableDeclarationExpr.class).forEach(vde ->
                vde.getVariables().forEach(v -> v.getInitializer().ifPresent(init -> {
                    localInits.put(v.getNameAsString(), init.toString());
                })));

        // Iteratively substitute locals until no more substitutions happen or an
        // unresolvable identifier is encountered.
        String result = condition;
        for (int i = 0; i < 10; i++) {
            boolean changed = false;
            Matcher m = Pattern.compile("\\b([a-zA-Z_$][a-zA-Z_$0-9]*)\\b").matcher(result);
            StringBuilder sb = new StringBuilder();
            int last = 0;
            while (m.find()) {
                sb.append(result, last, m.start());
                String tok = m.group(1);
                int peek = m.end();
                boolean followedByParen = peek < result.length() && result.charAt(peek) == '(';
                boolean afterDot = m.start() > 0 && result.charAt(m.start() - 1) == '.';
                if (followedByParen || afterDot || isReservedToken(tok)
                        || paramNames.contains(tok) || fieldNames.contains(tok)) {
                    sb.append(tok);
                } else if (localInits.containsKey(tok)) {
                    sb.append("(").append(localInits.get(tok)).append(")");
                    changed = true;
                } else {
                    // Unresolvable identifier — signal failure.
                    return null;
                }
                last = m.end();
            }
            sb.append(result, last, result.length());
            result = sb.toString();
            if (!changed) return result;
        }
        return result;
    }

    private boolean isReservedToken(String tok) {
        return tok.equals("this") || tok.equals("null") || tok.equals("true")
                || tok.equals("false") || tok.equals("new") || tok.equals("Math")
                || tok.equals("Integer") || tok.equals("Long") || tok.equals("String");
    }

    /**
     * True when the method body contains any statement that writes to the named
     * instance field — compound or plain assignment, unary inc/dec — and therefore
     * the field's value at any non-earliest point is POST-state (post prior writes)
     * rather than pre-state.
     */
    private boolean isFieldModifiedInMethod(MethodDeclaration methodDecl, String fieldName) {
        if (methodDecl.getBody().isEmpty()) return false;
        for (AssignExpr ae : methodDecl.getBody().get().findAll(AssignExpr.class)) {
            Expression target = ae.getTarget();
            if (target instanceof NameExpr ne && ne.getNameAsString().equals(fieldName)) return true;
            if (target instanceof FieldAccessExpr fa
                    && fa.getScope().toString().equals("this")
                    && fa.getNameAsString().equals(fieldName)) return true;
        }
        for (UnaryExpr ue : methodDecl.getBody().get().findAll(UnaryExpr.class)) {
            UnaryExpr.Operator op = ue.getOperator();
            if (op != UnaryExpr.Operator.PREFIX_INCREMENT
                    && op != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && op != UnaryExpr.Operator.PREFIX_DECREMENT
                    && op != UnaryExpr.Operator.POSTFIX_DECREMENT) continue;
            Expression inner = ue.getExpression();
            if (inner instanceof NameExpr ne && ne.getNameAsString().equals(fieldName)) return true;
            if (inner instanceof FieldAccessExpr fa
                    && fa.getScope().toString().equals("this")
                    && fa.getNameAsString().equals(fieldName)) return true;
        }
        return false;
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
        // First pass: qualified `this.field` → `\old(this.field)`.
        for (String field : fieldNames) {
            String thisField = "this." + field;
            if (result.contains(thisField) && !result.contains("\\old(" + thisField + ")")) {
                result = result.replace(thisField, "\\old(" + thisField + ")");
            }
        }
        // Second pass: bare-name `field` (not already inside `\old(...)` or `this.`)
        // → `\old(this.field)`. This catches the Countdown.tick case where the
        // inner-if condition is `remaining == 0` (bare) rather than
        // `this.remaining == 0`.
        //
        // Skip parameters whose names happen to shadow a field (usually rare, but
        // the condition source identifier is scoped to the method, not the class).
        Set<String> paramNames = new LinkedHashSet<>();
        methodDecl.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));
        for (String field : fieldNames) {
            if (paramNames.contains(field)) continue;
            // Word-boundary pattern that skips occurrences already in an \old(...)
            // or `this.field` — the first-pass already handled those.
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                    "(?<![\\w.\\\\])" + java.util.regex.Pattern.quote(field) + "(?!\\w)");
            java.util.regex.Matcher m = p.matcher(result);
            StringBuffer sb = new StringBuffer();
            while (m.find()) {
                m.appendReplacement(sb,
                        java.util.regex.Matcher.quoteReplacement("\\old(this." + field + ")"));
            }
            m.appendTail(sb);
            result = sb.toString();
        }
        return result;
    }
}
