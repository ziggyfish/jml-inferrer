package com.jml.inferrer.analysis;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;

import java.util.*;

/**
 * Symbolic execution engine for tracking variable values through method bodies.
 */
class SymbolicExecutor {

    /**
     * Represents a return expression discovered during symbolic walk, optionally
     * guarded by a path condition (null means unconditional).
     */
    static class SymbolicReturn {
        final String pathCondition; // null = unconditional
        final String resolvedExpr;
        SymbolicReturn(String pathCondition, String resolvedExpr) {
            this.pathCondition = pathCondition;
            this.resolvedExpr = resolvedExpr;
        }
    }

    /**
     * Returns {@code true} if every bare identifier in {@code expression} is visible at method
     * scope — i.e. a parameter, an instance field, or a Java/JML reserved name. Used to discard
     * postconditions that would reference loop-locals or other identifiers OpenJML cannot
     * resolve at the spec site.
     */
    boolean isMethodScopeSafe(String expression,
                              com.github.javaparser.ast.body.MethodDeclaration methodDecl,
                              Set<String> paramNames) {
        if (expression == null || expression.isEmpty()) return true;

        Set<String> reserved = Set.of("this", "null", "true", "false", "new",
                "Math", "Integer", "Long", "Double", "Float", "String", "System",
                "Collections", "Arrays", "Objects", "Optional", "super", "Object",
                "Number", "Boolean", "Byte", "Short", "Character",
                "byte", "short", "int", "long", "float", "double", "char", "boolean", "void");

        int i = 0;
        while (i < expression.length()) {
            char ch = expression.charAt(i);

            if (ch == '"' || ch == '\'') {
                char quote = ch;
                i++;
                while (i < expression.length() && expression.charAt(i) != quote) {
                    if (expression.charAt(i) == '\\' && i + 1 < expression.length()) i++;
                    i++;
                }
                if (i < expression.length()) i++;
                continue;
            }

            if (ch == '\\') {
                // JML keyword like \result, \old, \forall — always method-scope safe
                i++;
                while (i < expression.length() && Character.isJavaIdentifierPart(expression.charAt(i))) i++;
                continue;
            }

            if (Character.isJavaIdentifierStart(ch)) {
                int start = i;
                while (i < expression.length() && Character.isJavaIdentifierPart(expression.charAt(i))) i++;
                String token = expression.substring(start, i);

                boolean afterDot = start > 0 && expression.charAt(start - 1) == '.';
                if (afterDot) continue;
                // Method-call name: a token immediately followed by '(' is the name of an
                // invocation (e.g. gcd(a, b), Math.abs(x)), not a free variable.
                int peek = i;
                while (peek < expression.length() && Character.isWhitespace(expression.charAt(peek))) peek++;
                if (peek < expression.length() && expression.charAt(peek) == '(') continue;
                if (reserved.contains(token)) continue;
                if (paramNames.contains(token)) continue;
                if (AnalysisUtils.isFieldReference(methodDecl, token)) continue;

                return false;
            }

            i++;
        }
        return true;
    }

    String substituteEnv(String expression, Map<String, String> env, Set<String> paramNames) {
        if (expression == null || expression.isEmpty()) return expression;

        Set<String> reserved = Set.of("this", "null", "true", "false", "new",
                "Math", "Integer", "Long", "Double", "Float", "String", "System",
                "Collections", "Arrays", "Objects", "Optional", "super", "Object",
                "Number", "Boolean", "Byte", "Short", "Character",
                "byte", "short", "int", "long", "float", "double", "char", "boolean", "void");

        StringBuilder result = new StringBuilder();
        int i = 0;
        while (i < expression.length()) {
            char ch = expression.charAt(i);

            // Skip string literals
            if (ch == '"' || ch == '\'') {
                char quote = ch;
                result.append(ch);
                i++;
                while (i < expression.length() && expression.charAt(i) != quote) {
                    if (expression.charAt(i) == '\\' && i + 1 < expression.length()) {
                        result.append(expression.charAt(i));
                        i++;
                    }
                    result.append(expression.charAt(i));
                    i++;
                }
                if (i < expression.length()) {
                    result.append(expression.charAt(i));
                    i++;
                }
                continue;
            }

            // Parse Java identifier
            if (Character.isJavaIdentifierStart(ch)) {
                int start = i;
                while (i < expression.length() && Character.isJavaIdentifierPart(expression.charAt(i))) {
                    i++;
                }
                String token = expression.substring(start, i);

                // Check if preceded by '.' (field/method access) — leave as-is
                boolean afterDot = start > 0 && expression.charAt(start - 1) == '.';

                if (afterDot || reserved.contains(token)) {
                    result.append(token);
                } else if (env.containsKey(token)) {
                    String value = env.get(token);
                    if (AnalysisUtils.isCompoundExpression(value)) {
                        result.append("(").append(value).append(")");
                    } else {
                        result.append(value);
                    }
                } else {
                    // Parameter name not in env, or field reference — leave as-is
                    result.append(token);
                }
                continue;
            }

            // Non-identifier character
            result.append(ch);
            i++;
        }
        return result.toString();
    }

    List<Statement> extractStatements(Statement stmt) {
        if (stmt instanceof BlockStmt) {
            return ((BlockStmt) stmt).getStatements();
        }
        return Collections.singletonList(stmt);
    }

    boolean branchAlwaysReturns(Statement stmt) {
        if (stmt instanceof ReturnStmt || stmt instanceof ThrowStmt) return true;
        if (stmt instanceof BlockStmt) {
            List<Statement> stmts = ((BlockStmt) stmt).getStatements();
            if (stmts.isEmpty()) return false;
            return branchAlwaysReturns(stmts.get(stmts.size() - 1));
        }
        if (stmt instanceof IfStmt) {
            IfStmt ifStmt = (IfStmt) stmt;
            if (ifStmt.getElseStmt().isEmpty()) return false;
            return branchAlwaysReturns(ifStmt.getThenStmt())
                    && branchAlwaysReturns(ifStmt.getElseStmt().get());
        }
        return false;
    }

    void taintModifiedVariables(Map<String, String> env, Statement stmt) {
        for (AssignExpr assign : stmt.findAll(AssignExpr.class)) {
            if (assign.getTarget() instanceof NameExpr) {
                env.remove(((NameExpr) assign.getTarget()).getNameAsString());
            }
        }
        for (UnaryExpr unary : stmt.findAll(UnaryExpr.class)) {
            if (unary.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT
                    || unary.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                    || unary.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT
                    || unary.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT) {
                if (unary.getExpression() instanceof NameExpr) {
                    env.remove(((NameExpr) unary.getExpression()).getNameAsString());
                }
            }
        }
        // Also taint variables declared inside (they shadow outer)
        for (VariableDeclarationExpr vde : stmt.findAll(VariableDeclarationExpr.class)) {
            for (com.github.javaparser.ast.body.VariableDeclarator vd : vde.getVariables()) {
                env.remove(vd.getNameAsString());
            }
        }
    }

    String conjoin(String existing, String additional) {
        if (existing == null) return additional;
        if (additional == null) return existing;
        return "(" + existing + ") && (" + additional + ")";
    }

    void mergeEnvs(Map<String, String> envBefore, Map<String, String> thenEnv,
                   Map<String, String> elseEnv, Map<String, String> envOut,
                   Map<String, List<SymbolicReturn>> conditionalAssignments,
                   String condStr, String negCondStr) {
        envOut.putAll(envBefore);

        Set<String> allVars = new LinkedHashSet<>();
        allVars.addAll(thenEnv.keySet());
        allVars.addAll(elseEnv.keySet());

        for (String var : allVars) {
            String thenVal = thenEnv.get(var);
            String elseVal = elseEnv.get(var);

            if (thenVal != null && elseVal != null && thenVal.equals(elseVal)) {
                envOut.put(var, thenVal);
            } else if (thenVal != null && elseVal != null) {
                envOut.remove(var);
                List<SymbolicReturn> entries = conditionalAssignments.computeIfAbsent(var, k -> new ArrayList<>());
                entries.add(new SymbolicReturn(condStr, thenVal));
                entries.add(new SymbolicReturn(negCondStr, elseVal));
            } else if (thenVal != null) {
                envOut.remove(var);
                List<SymbolicReturn> entries = conditionalAssignments.computeIfAbsent(var, k -> new ArrayList<>());
                entries.add(new SymbolicReturn(condStr, thenVal));
            } else {
                envOut.remove(var);
                List<SymbolicReturn> entries = conditionalAssignments.computeIfAbsent(var, k -> new ArrayList<>());
                entries.add(new SymbolicReturn(negCondStr, elseVal));
            }
        }
    }

    void walkStatements(List<Statement> statements, Map<String, String> env,
                        Map<String, List<SymbolicReturn>> conditionalAssignments,
                        String pathCondition, Set<String> paramNames,
                        List<SymbolicReturn> results, int depth) {
        if (depth > 10) return; // prevent stack overflow on deeply nested code

        for (Statement stmt : statements) {
            // --- ExpressionStmt: variable declaration or assignment ---
            if (stmt instanceof ExpressionStmt) {
                Expression inner = ((ExpressionStmt) stmt).getExpression();

                if (inner instanceof VariableDeclarationExpr) {
                    for (com.github.javaparser.ast.body.VariableDeclarator vd :
                            ((VariableDeclarationExpr) inner).getVariables()) {
                        if (vd.getInitializer().isPresent()) {
                            String rhsRaw = vd.getInitializer().get().toString();
                            String resolved = substituteEnv(rhsRaw, env, paramNames);
                            env.put(vd.getNameAsString(), resolved);
                        }
                    }
                } else if (inner instanceof AssignExpr) {
                    AssignExpr assign = (AssignExpr) inner;
                    if (assign.getTarget() instanceof NameExpr) {
                        String varName = ((NameExpr) assign.getTarget()).getNameAsString();
                        String rhsRaw = assign.getValue().toString();
                        String resolvedRhs = substituteEnv(rhsRaw, env, paramNames);

                        if (assign.getOperator() == AssignExpr.Operator.ASSIGN) {
                            env.put(varName, resolvedRhs);
                        } else {
                            String op = AnalysisUtils.getCompoundOperatorString(assign.getOperator());
                            if (op != null) {
                                String currentValue;
                                if (env.containsKey(varName)) {
                                    currentValue = env.get(varName);
                                } else if (!paramNames.contains(varName)) {
                                    currentValue = "\\old(this." + varName + ")";
                                } else {
                                    currentValue = varName;
                                }
                                String lhs = AnalysisUtils.isCompoundExpression(currentValue) ? "(" + currentValue + ")" : currentValue;
                                String rhs = AnalysisUtils.isCompoundExpression(resolvedRhs) ? "(" + resolvedRhs + ")" : resolvedRhs;
                                env.put(varName, lhs + " " + op + " " + rhs);
                            }
                        }
                    }
                }
                continue;
            }

            // --- ReturnStmt ---
            if (stmt instanceof ReturnStmt) {
                ReturnStmt ret = (ReturnStmt) stmt;
                if (ret.getExpression().isPresent()) {
                    Expression returnExpr = ret.getExpression().get();

                    // Decompose ternary expressions into two conditional paths
                    if (returnExpr instanceof ConditionalExpr) {
                        ConditionalExpr ternary = (ConditionalExpr) returnExpr;
                        String condStr = substituteEnv(ternary.getCondition().toString(), env, paramNames);
                        String negCondStr = AnalysisUtils.negateCondition(ternary.getCondition());
                        String thenResolved = substituteEnv(ternary.getThenExpr().toString(), env, paramNames);
                        String elseResolved = substituteEnv(ternary.getElseExpr().toString(), env, paramNames);
                        results.add(new SymbolicReturn(conjoin(pathCondition, condStr), thenResolved));
                        results.add(new SymbolicReturn(conjoin(pathCondition, negCondStr), elseResolved));
                        return;
                    }

                    String rawReturn = returnExpr.toString();
                    String resolved = substituteEnv(rawReturn, env, paramNames);

                    // Also resolve through conditional assignments
                    if (conditionalAssignments != null) {
                        for (Map.Entry<String, List<SymbolicReturn>> entry : conditionalAssignments.entrySet()) {
                            String var = entry.getKey();
                            if (resolved.contains(var)) {
                                for (SymbolicReturn ca : entry.getValue()) {
                                    Map<String, String> tempEnv = new LinkedHashMap<>(env);
                                    tempEnv.put(var, ca.resolvedExpr);
                                    String condResolved = substituteEnv(rawReturn, tempEnv, paramNames);
                                    String combinedCond = conjoin(pathCondition, ca.pathCondition);
                                    results.add(new SymbolicReturn(combinedCond, condResolved));
                                }
                                return; // handled via conditional assignments
                            }
                        }
                    }

                    results.add(new SymbolicReturn(pathCondition, resolved));
                }
                return; // return always terminates this path
            }

            // --- IfStmt ---
            if (stmt instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) stmt;
                String condRaw = ifStmt.getCondition().toString();
                String condStr = substituteEnv(condRaw, env, paramNames);
                String negCondStr = AnalysisUtils.negateCondition(ifStmt.getCondition());

                boolean thenReturns = branchAlwaysReturns(ifStmt.getThenStmt());
                boolean hasElse = ifStmt.getElseStmt().isPresent();
                boolean elseReturns = hasElse && branchAlwaysReturns(ifStmt.getElseStmt().get());

                if (thenReturns && elseReturns) {
                    Map<String, String> thenEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getThenStmt()), thenEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, condStr), paramNames, results, depth + 1);

                    Map<String, String> elseEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getElseStmt().get()), elseEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, negCondStr), paramNames, results, depth + 1);
                    return;

                } else if (thenReturns && !hasElse) {
                    Map<String, String> thenEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getThenStmt()), thenEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, condStr), paramNames, results, depth + 1);
                    pathCondition = conjoin(pathCondition, negCondStr);
                    continue;

                } else if (thenReturns && hasElse) {
                    Map<String, String> thenEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getThenStmt()), thenEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, condStr), paramNames, results, depth + 1);

                    Map<String, String> elseEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getElseStmt().get()), elseEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, negCondStr), paramNames, new ArrayList<>(), depth + 1);
                    env.clear();
                    env.putAll(elseEnv);
                    pathCondition = conjoin(pathCondition, negCondStr);
                    continue;

                } else if (!thenReturns && hasElse && elseReturns) {
                    Map<String, String> elseEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getElseStmt().get()), elseEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, negCondStr), paramNames, results, depth + 1);

                    Map<String, String> thenEnv = new LinkedHashMap<>(env);
                    walkStatements(extractStatements(ifStmt.getThenStmt()), thenEnv,
                            conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                            conjoin(pathCondition, condStr), paramNames, new ArrayList<>(), depth + 1);
                    env.clear();
                    env.putAll(thenEnv);
                    pathCondition = conjoin(pathCondition, condStr);
                    continue;

                } else if (hasElse) {
                    Map<String, String> thenEnv = new LinkedHashMap<>(env);
                    Map<String, List<SymbolicReturn>> thenInnerConds = new LinkedHashMap<>();
                    walkStatements(extractStatements(ifStmt.getThenStmt()), thenEnv,
                            thenInnerConds,
                            conjoin(pathCondition, condStr), paramNames, new ArrayList<>(), depth + 1);

                    Map<String, String> elseEnv = new LinkedHashMap<>(env);
                    Map<String, List<SymbolicReturn>> elseInnerConds = new LinkedHashMap<>();
                    walkStatements(extractStatements(ifStmt.getElseStmt().get()), elseEnv,
                            elseInnerConds,
                            conjoin(pathCondition, negCondStr), paramNames, new ArrayList<>(), depth + 1);

                    Map<String, String> merged = new LinkedHashMap<>();
                    if (conditionalAssignments == null) {
                        conditionalAssignments = new LinkedHashMap<>();
                    }
                    mergeEnvs(env, thenEnv, elseEnv, merged, conditionalAssignments, condStr, negCondStr);

                    for (Map.Entry<String, List<SymbolicReturn>> innerEntry : thenInnerConds.entrySet()) {
                        String var = innerEntry.getKey();
                        if (!merged.containsKey(var)) {
                            List<SymbolicReturn> outerEntries = conditionalAssignments.computeIfAbsent(var, k -> new ArrayList<>());
                            for (SymbolicReturn sr : innerEntry.getValue()) {
                                outerEntries.add(new SymbolicReturn(conjoin(condStr, sr.pathCondition), sr.resolvedExpr));
                            }
                        }
                    }
                    for (Map.Entry<String, List<SymbolicReturn>> innerEntry : elseInnerConds.entrySet()) {
                        String var = innerEntry.getKey();
                        if (!merged.containsKey(var)) {
                            List<SymbolicReturn> outerEntries = conditionalAssignments.computeIfAbsent(var, k -> new ArrayList<>());
                            for (SymbolicReturn sr : innerEntry.getValue()) {
                                outerEntries.add(new SymbolicReturn(conjoin(negCondStr, sr.pathCondition), sr.resolvedExpr));
                            }
                        }
                    }

                    env.clear();
                    env.putAll(merged);
                    continue;

                } else {
                    taintModifiedVariables(env, ifStmt.getThenStmt());
                    continue;
                }
            }

            // --- Loop statements ---
            if (stmt instanceof ForStmt || stmt instanceof WhileStmt
                    || stmt instanceof ForEachStmt || stmt instanceof DoStmt) {
                Statement body;
                if (stmt instanceof ForStmt) body = ((ForStmt) stmt).getBody();
                else if (stmt instanceof WhileStmt) body = ((WhileStmt) stmt).getBody();
                else if (stmt instanceof ForEachStmt) body = ((ForEachStmt) stmt).getBody();
                else body = ((DoStmt) stmt).getBody();

                taintModifiedVariables(env, body);
                if (stmt instanceof ForStmt) {
                    for (Expression update : ((ForStmt) stmt).getUpdate()) {
                        if (update instanceof AssignExpr && ((AssignExpr) update).getTarget() instanceof NameExpr) {
                            env.remove(((NameExpr) ((AssignExpr) update).getTarget()).getNameAsString());
                        }
                        if (update instanceof UnaryExpr && ((UnaryExpr) update).getExpression() instanceof NameExpr) {
                            env.remove(((NameExpr) ((UnaryExpr) update).getExpression()).getNameAsString());
                        }
                    }
                }
                walkStatements(extractStatements(body), new LinkedHashMap<>(env),
                        conditionalAssignments != null ? new LinkedHashMap<>(conditionalAssignments) : null,
                        pathCondition, paramNames, results, depth + 1);
                continue;
            }

            // --- BlockStmt ---
            if (stmt instanceof BlockStmt) {
                walkStatements(((BlockStmt) stmt).getStatements(), env,
                        conditionalAssignments, pathCondition, paramNames, results, depth + 1);
                return;
            }

            // --- TryStmt ---
            if (stmt instanceof TryStmt) {
                TryStmt tryStmt = (TryStmt) stmt;
                walkStatements(tryStmt.getTryBlock().getStatements(), env,
                        conditionalAssignments, pathCondition, paramNames, results, depth + 1);
                taintModifiedVariables(env, tryStmt.getTryBlock());
                continue;
            }

            // --- ThrowStmt ---
            if (stmt instanceof ThrowStmt) {
                return;
            }

            // --- SwitchStmt ---
            if (stmt instanceof SwitchStmt) {
                taintModifiedVariables(env, stmt);
                continue;
            }
        }
    }
}
