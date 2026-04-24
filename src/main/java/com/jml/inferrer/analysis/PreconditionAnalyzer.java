package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.*;

/**
 * Analyzes method declarations to infer JML preconditions.
 */
class PreconditionAnalyzer {

    void inferPreconditions(MethodDeclaration methodDecl, com.jml.inferrer.model.MethodSpecification spec,
                            InterproceduralAnalyzer interproceduralAnalyzer, ASTCollector collector) {
        Set<String> preconditions = new LinkedHashSet<>();

        for (Parameter param : methodDecl.getParameters()) {
            String paramName = param.getNameAsString();
            com.github.javaparser.ast.type.Type paramType = param.getType();

            // Reference type null checks
            if (paramType.isReferenceType() && !paramType.isPrimitiveType()) {
                if (hasNullCheckOrAccess(methodDecl, paramName, collector)) {
                    preconditions.add(paramName + " != null");
                }
            }

            // String-specific preconditions
            if (paramType.asString().equals("String")) {
                analyzeStringParameterConstraints(methodDecl, paramName, preconditions, collector);
            }

            // Numeric type constraints
            if (AnalysisUtils.isNumericType(paramType)) {
                analyzeNumericConstraints(methodDecl, paramName, preconditions, collector);
                analyzeFieldArrayIndexConstraints(methodDecl, paramName, preconditions, collector);
            }

            // Array and collection constraints
            if (paramType.asString().contains("[]")) {
                analyzeArrayParameterConstraints(methodDecl, paramName, preconditions, collector);
            } else if (AnalysisUtils.isCollectionType(paramType.asString())) {
                analyzeCollectionParameterConstraints(methodDecl, paramName, preconditions, collector);
            }
        }

        // Analyze early validation patterns
        analyzeEarlyValidation(methodDecl, preconditions, collector);

        // Analyze null checks in method body
        NullCheckVisitor nullCheckVisitor = new NullCheckVisitor();
        methodDecl.accept(nullCheckVisitor, null);
        preconditions.addAll(nullCheckVisitor.getNullChecks());

        // Instance-field null preconditions. When the method dereferences `this.field`
        // (via field.foo, field[i], or as an array-creation dimension), emit
        // `requires this.field != null` so OpenJML's nullable-by-default analysis has
        // a chance to prove the access.
        analyzeInstanceFieldNullPreconditions(methodDecl, preconditions, collector);

        // Nested param-field null: `obj.name.method()` needs `obj.name != null`.
        analyzeNestedFieldDereference(methodDecl, preconditions, collector);

        // Cross-array bound preconditions for the `for(i=0; i<a.length; i++) b[i] = a[i]`
        // pattern: the access `b[i]` is in-bounds only when `b.length >= a.length`.
        analyzeCrossArrayLoopBounds(methodDecl, preconditions, collector);

        // Param-bounded loop bounds for `for(i=start; i<end; i++) arr[i] = ...` style.
        // Without `start >= 0` and `end <= arr.length` the access is unproveable.
        analyzeRangeLoopArrayBounds(methodDecl, preconditions, collector);

        // Field-index-into-field-array: `this.data[this.size] = v` needs
        // `this.size < this.data.length` as a precondition. Symmetric to
        // analyzeFieldArrayIndexConstraints but the index is a field, not a param.
        analyzeFieldIndexFieldArrayBounds(methodDecl, preconditions, collector);

        // Analyze parameter relationships
        analyzeParameterRelationships(methodDecl, preconditions, collector);

        // Interprocedural analysis: propagate preconditions from called methods
        interproceduralAnalyzer.analyzeMethodCallPreconditions(methodDecl, preconditions, collector);

        preconditions.forEach(spec::addPrecondition);
    }

    boolean hasNullCheckOrAccess(MethodDeclaration methodDecl, String paramName, ASTCollector collector) {
        // Check for explicit null checks
        boolean hasNullCheck = collector.binaryExprs.stream()
            .anyMatch(binExpr -> {
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS ||
                    binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS) {
                    return (binExpr.getLeft().toString().equals(paramName) && binExpr.getRight().isNullLiteralExpr()) ||
                           (binExpr.getRight().toString().equals(paramName) && binExpr.getLeft().isNullLiteralExpr());
                }
                return false;
            });

        // Check for method calls on the parameter
        boolean hasMethodCall = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false));

        // Check for field access on the parameter
        boolean hasFieldAccess = collector.fieldAccessExprs.stream()
            .anyMatch(field -> field.getScope().toString().equals(paramName));

        // Check for for-each loop over the parameter (implies non-null)
        boolean hasForEachUsage = collector.forEachStmts.stream()
            .anyMatch(forEach -> forEach.getIterable().toString().equals(paramName));

        return hasNullCheck || hasMethodCall || hasFieldAccess || hasForEachUsage;
    }

    private void analyzeStringParameterConstraints(MethodDeclaration methodDecl, String paramName,
                                                    Set<String> preconditions, ASTCollector collector) {
        // Check for null requirement
        if (hasNullCheckOrAccess(methodDecl, paramName, collector)) {
            preconditions.add(paramName + " != null");
        }

        // Check for isEmpty() calls
        boolean hasEmptyCheck = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("isEmpty"));

        // Check for length() calls with comparisons
        collector.methodCallExprs.stream()
            .filter(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("length"))
            .forEach(lengthCall -> {
                // Look for comparisons with this length call
                collector.binaryExprs.stream()
                    .filter(binExpr -> binExpr.getLeft().toString().contains(paramName + ".length()") ||
                                       binExpr.getRight().toString().contains(paramName + ".length()"))
                    .forEach(binExpr -> {
                        if (binExpr.getOperator() == BinaryExpr.Operator.GREATER &&
                            binExpr.getLeft().toString().contains(paramName + ".length()")) {
                            preconditions.add(paramName + ".length() > " + binExpr.getRight());
                        }
                    });
            });

        // If isEmpty() is called, check whether it's used in a guard condition (if/else).
        // If the method handles both empty and non-empty cases, don't add as precondition.
        if (hasEmptyCheck) {
            boolean isGuardCondition = collector.ifStmts.stream()
                    .anyMatch(ifStmt -> {
                        String condStr = ifStmt.getCondition().toString();
                        return condStr.contains(paramName + ".isEmpty()");
                    });
            if (!isGuardCondition) {
                // isEmpty() is called but not as a guard — likely needs non-empty
                preconditions.add("!" + paramName + ".isEmpty()");
            }
            // If it IS a guard, the method handles both cases, so no precondition needed
        }

        // Check for charAt() calls - implies non-empty
        boolean hasCharAt = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("charAt"));

        if (hasCharAt) {
            preconditions.add(paramName + ".length() > 0");
        }
    }

    private void analyzeArrayParameterConstraints(MethodDeclaration methodDecl, String paramName,
                                                    Set<String> preconditions, ASTCollector collector) {
        // Check for null requirement
        boolean hasArrayAccess = collector.arrayAccessExprs.stream()
            .anyMatch(access -> access.getName().toString().equals(paramName));

        boolean hasLengthAccess = collector.fieldAccessExprs.stream()
            .anyMatch(field -> field.getScope().toString().equals(paramName) &&
                              field.getNameAsString().equals("length"));

        if (hasArrayAccess || hasLengthAccess) {
            preconditions.add(paramName + " != null");
        }

        // Check for array index access to infer non-empty requirement
        if (hasArrayAccess) {
            // Check if accessing specific indices
            collector.arrayAccessExprs.stream()
                .filter(access -> access.getName().toString().equals(paramName))
                .forEach(access -> {
                    Expression index = access.getIndex();
                    if (index instanceof IntegerLiteralExpr) {
                        int indexValue = ((IntegerLiteralExpr) index).asInt();
                        preconditions.add(paramName + ".length > " + indexValue);
                    } else if (index instanceof NameExpr) {
                        // Index is a variable — check if it's a parameter
                        String indexName = ((NameExpr) index).getNameAsString();
                        boolean isParam = methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(indexName));
                        if (isParam) {
                            // Generate proper bounds: idx >= 0 && idx < arr.length
                            preconditions.add(indexName + " >= 0");
                            preconditions.add(indexName + " < " + paramName + ".length");
                        }
                        // Non-parameter index (loop var, local) — let the loop's own
                        // invariant bound it. Don't emit `arr.length > 0` blindly:
                        // empty-array loops don't iterate and don't access `arr[i]`.
                    }
                    // Complex index expressions are also handled by loop invariants.
                });
        }

        // Check for length comparisons in conditionals
        analyzeArrayLengthConstraints(methodDecl, paramName, preconditions, collector);
    }

    /**
     * If a numeric parameter is used to index an instance-field array
     * (e.g. {@code data[idx]} where {@code data} is a field), emit
     * {@code idx >= 0} and {@code idx < this.data.length} preconditions.
     * Symmetric to {@link #analyzeArrayParameterConstraints} but handles the case where
     * the array lives on {@code this}, not in the parameter list.
     */
    /**
     * `this.data[this.size] = value` (or any `this.fieldArray[this.fieldIdx]` access)
     * requires a precondition bounding {@code fieldIdx} within {@code fieldArray.length}.
     * The index field must be distinct from the array field and numeric; both must be
     * instance fields of the enclosing class. When the write modifies {@code fieldIdx}
     * (e.g. {@code size++}), the original index value still applies to the array
     * write that happened FIRST in the body.
     */
    private void analyzeFieldIndexFieldArrayBounds(MethodDeclaration methodDecl,
                                                    Set<String> preconditions, ASTCollector collector) {
        for (var access : collector.arrayAccessExprs) {
            Expression index = access.getIndex();
            String idxField = fieldName(index, methodDecl);
            if (idxField == null) continue;

            Expression name = access.getName();
            while (name instanceof ArrayAccessExpr inner) name = inner.getName();
            String arrField = fieldName(name, methodDecl);
            if (arrField == null || arrField.equals(idxField)) continue;

            preconditions.add("this." + idxField + " >= 0");
            preconditions.add("this." + idxField + " < this." + arrField + ".length");
        }
    }

    /** Extract the backing instance-field name from {@code this.field}, {@code field}, or null. */
    private String fieldName(Expression expr, MethodDeclaration methodDecl) {
        if (expr instanceof FieldAccessExpr fa && fa.getScope().toString().equals("this")) {
            return fa.getNameAsString();
        }
        if (expr instanceof NameExpr ne && AnalysisUtils.isFieldReference(methodDecl, ne.getNameAsString())) {
            return ne.getNameAsString();
        }
        return null;
    }

    private void analyzeFieldArrayIndexConstraints(MethodDeclaration methodDecl, String paramName,
                                                    Set<String> preconditions, ASTCollector collector) {
        for (var access : collector.arrayAccessExprs) {
            // Top-level access: index must be the parameter we're analyzing
            Expression index = access.getIndex();
            if (!(index instanceof NameExpr ne) || !ne.getNameAsString().equals(paramName)) continue;

            // Resolve the underlying field name (handles `data[i]`, `this.data[i]`, nested arrays)
            Expression name = access.getName();
            String fieldName = null;
            while (name instanceof ArrayAccessExpr inner) name = inner.getName();
            if (name instanceof FieldAccessExpr fa && fa.getScope().toString().equals("this")) {
                fieldName = fa.getNameAsString();
            } else if (name instanceof NameExpr nameExpr) {
                String n = nameExpr.getNameAsString();
                if (AnalysisUtils.isFieldReference(methodDecl, n)) fieldName = n;
            }
            if (fieldName == null) continue;

            preconditions.add(paramName + " >= 0");
            preconditions.add(paramName + " < this." + fieldName + ".length");
        }
    }

    private void analyzeCollectionParameterConstraints(MethodDeclaration methodDecl, String paramName,
                                                        Set<String> preconditions, ASTCollector collector) {
        // Check for null requirement
        boolean hasMethodCall = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false));

        if (hasMethodCall) {
            preconditions.add(paramName + " != null");
        }

        // Check for size() calls
        boolean hasSizeCheck = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("size"));

        // Check for isEmpty() calls
        boolean hasEmptyCheck = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("isEmpty"));

        // Check for iterator or get operations - implies non-empty
        boolean hasGet = collector.methodCallExprs.stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("get"));

        if (hasGet) {
            preconditions.add(paramName + ".size() > 0");
        }
    }

    private void analyzeInstanceFieldNullPreconditions(MethodDeclaration methodDecl,
                                                        Set<String> preconditions, ASTCollector collector) {
        // Gather reference-type instance field names from the enclosing class.
        Set<String> refFieldNames = methodDecl.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .filter(f -> !f.getCommonType().isPrimitiveType())
                        .flatMap(f -> f.getVariables().stream())
                        .map(com.github.javaparser.ast.body.VariableDeclarator::getNameAsString)
                        .collect(java.util.stream.Collectors.toSet()))
                .orElseGet(java.util.HashSet::new);
        if (refFieldNames.isEmpty()) return;

        Set<String> dereferenced = new java.util.LinkedHashSet<>();
        // Field access: `this.data.length` → `data` is dereferenced
        collector.fieldAccessExprs.forEach(fa -> {
            if (fa.getScope() instanceof FieldAccessExpr inner
                    && inner.getScope().toString().equals("this")
                    && refFieldNames.contains(inner.getNameAsString())) {
                dereferenced.add(inner.getNameAsString());
            } else if (fa.getScope() instanceof NameExpr ne
                    && refFieldNames.contains(ne.getNameAsString())) {
                dereferenced.add(ne.getNameAsString());
            }
        });
        // Array access: `data[i]`, `this.data[i]`, `data[r][c]`
        collector.arrayAccessExprs.forEach(aa -> {
            Expression base = aa.getName();
            while (base instanceof ArrayAccessExpr inner) base = inner.getName();
            if (base instanceof FieldAccessExpr fa
                    && fa.getScope().toString().equals("this")
                    && refFieldNames.contains(fa.getNameAsString())) {
                dereferenced.add(fa.getNameAsString());
            } else if (base instanceof NameExpr ne
                    && refFieldNames.contains(ne.getNameAsString())) {
                dereferenced.add(ne.getNameAsString());
            }
        });
        // Method call on field: `this.list.add(x)`
        collector.methodCallExprs.forEach(call -> call.getScope().ifPresent(scope -> {
            if (scope instanceof FieldAccessExpr fa
                    && fa.getScope().toString().equals("this")
                    && refFieldNames.contains(fa.getNameAsString())) {
                dereferenced.add(fa.getNameAsString());
            } else if (scope instanceof NameExpr ne
                    && refFieldNames.contains(ne.getNameAsString())) {
                dereferenced.add(ne.getNameAsString());
            }
        }));

        for (String field : dereferenced) {
            preconditions.add("this." + field + " != null");
        }
    }

    private void analyzeEarlyValidation(MethodDeclaration methodDecl, Set<String> preconditions,
                                         ASTCollector collector) {
        Set<String> paramNames = new java.util.LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());
        SymbolicExecutor scopeChecker = new SymbolicExecutor();

        collector.ifStmts.forEach(ifStmt -> {
            // An if-throw nested inside a loop refers to loop-local variables
            // (e.g., for(int i...) if (matrix[i] == null) throw ...) that cannot appear
            // in a method-level requires clause.
            if (isInsideLoop(ifStmt)) return;

            // Check if this if statement throws an exception
            boolean throwsException = ifStmt.getThenStmt().findAll(ThrowStmt.class).size() > 0;

            if (throwsException) {
                Expression condition = ifStmt.getCondition();

                // Invert the condition to get the precondition
                if (condition instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) condition;
                    String invertedCondition = invertCondition(binExpr);
                    if (invertedCondition != null && !invertedCondition.isEmpty()
                            && scopeChecker.isMethodScopeSafe(invertedCondition, methodDecl, paramNames)) {
                        preconditions.add(invertedCondition);
                    }
                } else if (condition instanceof UnaryExpr) {
                    UnaryExpr unaryExpr = (UnaryExpr) condition;
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
                        // !(condition) in if-throw means condition must be true
                        String inner = unaryExpr.getExpression().toString();
                        if (scopeChecker.isMethodScopeSafe(inner, methodDecl, paramNames)) {
                            preconditions.add(inner);
                        }
                    }
                }
            }
        });
    }

    static boolean isInsideLoop(com.github.javaparser.ast.Node node) {
        return node.findAncestor(com.github.javaparser.ast.stmt.ForStmt.class).isPresent()
                || node.findAncestor(com.github.javaparser.ast.stmt.ForEachStmt.class).isPresent()
                || node.findAncestor(com.github.javaparser.ast.stmt.WhileStmt.class).isPresent()
                || node.findAncestor(com.github.javaparser.ast.stmt.DoStmt.class).isPresent();
    }

    private void analyzeParameterRelationships(MethodDeclaration methodDecl, Set<String> preconditions,
                                                ASTCollector collector) {
        List<Parameter> params = methodDecl.getParameters();

        // Only generate parameter relationship preconditions from early validation patterns
        // (if-throw blocks), not from general branching logic.
        collector.ifStmts.forEach(ifStmt -> {
            boolean throwsException = !ifStmt.getThenStmt().findAll(ThrowStmt.class).isEmpty();
            if (!throwsException) return;

            ifStmt.getCondition().findAll(BinaryExpr.class).forEach(binExpr -> {
                String left = binExpr.getLeft().toString();
                String right = binExpr.getRight().toString();

                boolean leftIsParam = params.stream().anyMatch(p -> p.getNameAsString().equals(left));
                boolean rightIsParam = params.stream().anyMatch(p -> p.getNameAsString().equals(right));

                if (leftIsParam && rightIsParam) {
                    // Invert the condition: if (a < b) throw → requires a >= b
                    String inverted = invertBinaryOperator(binExpr.getOperator());
                    if (inverted != null) {
                        preconditions.add(left + " " + inverted + " " + right);
                    }
                }
            });
        });
    }

    String invertBinaryOperator(BinaryExpr.Operator op) {
        switch (op) {
            case LESS: return ">=";
            case LESS_EQUALS: return ">";
            case GREATER: return "<=";
            case GREATER_EQUALS: return "<";
            case EQUALS: return "!=";
            case NOT_EQUALS: return "==";
            default: return null;
        }
    }

    /**
     * For loops of the shape {@code for (int i = LO; i <op> A.length; i++)} whose body
     * contains an access {@code B[i]} where {@code A != B}, both arrays parameters, emit
     * {@code B.length >= A.length} (or the analogous bound for {@code <=}). Without this
     * the access raises {@code PossiblyTooLargeIndex} on copy / merge / dot-product loops.
     *
     * <p>Only fires when both arrays are top-level method parameters and the loop's lower
     * bound is a non-negative literal (so the lower-end accesses are already covered by
     * {@code i >= 0}).</p>
     */
    private void analyzeCrossArrayLoopBounds(MethodDeclaration methodDecl,
                                              Set<String> preconditions, ASTCollector collector) {
        Set<String> arrayParams = new java.util.LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            if (p.getType().asString().contains("[]")) {
                arrayParams.add(p.getNameAsString());
            }
        }
        if (arrayParams.size() < 2) return;

        for (com.github.javaparser.ast.stmt.ForStmt fs
                : methodDecl.findAll(com.github.javaparser.ast.stmt.ForStmt.class)) {
            if (fs.getInitialization().size() != 1) continue;
            Expression init = fs.getInitialization().get(0);
            if (!(init instanceof VariableDeclarationExpr vde)) continue;
            if (vde.getVariables().size() != 1) continue;
            String counter = vde.getVariables().get(0).getNameAsString();
            Optional<Expression> initExprOpt = vde.getVariables().get(0).getInitializer();
            if (initExprOpt.isEmpty()) continue;
            Expression initExpr = initExprOpt.get();
            if (!initExpr.isIntegerLiteralExpr()) continue;
            if (initExpr.asIntegerLiteralExpr().asInt() < 0) continue;

            if (fs.getCompare().isEmpty()) continue;
            if (!(fs.getCompare().get() instanceof BinaryExpr cmp)) continue;
            if (!(cmp.getLeft() instanceof NameExpr ne)
                    || !ne.getNameAsString().equals(counter)) continue;
            String upperParam = extractArrayLengthParam(cmp.getRight(), arrayParams);
            if (upperParam == null) continue;

            String op;
            if (cmp.getOperator() == BinaryExpr.Operator.LESS) op = ">=";
            else if (cmp.getOperator() == BinaryExpr.Operator.LESS_EQUALS) op = ">";
            else continue;

            for (ArrayAccessExpr aa : fs.getBody().findAll(ArrayAccessExpr.class)) {
                if (!(aa.getName() instanceof NameExpr arrNe)) continue;
                String accessedArray = arrNe.getNameAsString();
                if (!arrayParams.contains(accessedArray)) continue;
                if (accessedArray.equals(upperParam)) continue;
                if (!(aa.getIndex() instanceof NameExpr idxNe)) continue;
                if (!idxNe.getNameAsString().equals(counter)) continue;
                preconditions.add(accessedArray + ".length " + op + " " + upperParam + ".length");
            }
        }
    }

    /**
     * For method calls like {@code obj.name.length()} where {@code obj} is a parameter,
     * emit {@code obj.name != null} precondition. Covers the nested-dereference case
     * that {@link #analyzeInstanceFieldNullPreconditions} doesn't handle (that one
     * handles {@code this.field}, not {@code param.field}).
     */
    private void analyzeNestedFieldDereference(MethodDeclaration methodDecl,
                                                 Set<String> preconditions, ASTCollector collector) {
        Set<String> paramNames = new java.util.LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());
        if (paramNames.isEmpty()) return;

        collector.methodCallExprs.forEach(call -> {
            if (call.getScope().isEmpty()) return;
            Expression scope = call.getScope().get();
            if (!(scope instanceof FieldAccessExpr fae)) return;
            if (!(fae.getScope() instanceof NameExpr paramNe)) return;
            if (!paramNames.contains(paramNe.getNameAsString())) return;
            preconditions.add(paramNe.getNameAsString() + "." + fae.getNameAsString() + " != null");
        });

        collector.fieldAccessExprs.forEach(fa -> {
            // `obj.name.length` (no method call): still requires obj.name != null
            if (!(fa.getScope() instanceof FieldAccessExpr inner)) return;
            if (!(inner.getScope() instanceof NameExpr paramNe)) return;
            if (!paramNames.contains(paramNe.getNameAsString())) return;
            preconditions.add(paramNe.getNameAsString() + "." + inner.getNameAsString() + " != null");
        });
    }

    /**
     * For loops like {@code for (int i = start; i < end; i++) arr[i] = ...} where
     * {@code start} and {@code end} are method parameters and {@code arr} is also a
     * parameter, emit {@code start >= 0} and {@code end <= arr.length} as
     * preconditions. Without these the in-loop access raises PossiblyNegativeIndex
     * or PossiblyTooLargeIndex.
     */
    private void analyzeRangeLoopArrayBounds(MethodDeclaration methodDecl,
                                              Set<String> preconditions, ASTCollector collector) {
        Set<String> paramNames = new java.util.LinkedHashSet<>();
        Set<String> arrayParams = new java.util.LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            paramNames.add(p.getNameAsString());
            if (p.getType().asString().contains("[]")) {
                arrayParams.add(p.getNameAsString());
            }
        }
        if (arrayParams.isEmpty()) return;

        for (com.github.javaparser.ast.stmt.ForStmt fs
                : methodDecl.findAll(com.github.javaparser.ast.stmt.ForStmt.class)) {
            if (fs.getInitialization().size() != 1) continue;
            if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) continue;
            if (vde.getVariables().size() != 1) continue;
            String counter = vde.getVariables().get(0).getNameAsString();
            Optional<Expression> initOpt = vde.getVariables().get(0).getInitializer();
            if (initOpt.isEmpty()) continue;
            Expression initExpr = initOpt.get();
            // init must be a parameter — that's the lower bound we want >= 0 on.
            if (!(initExpr instanceof NameExpr initNe)) continue;
            String startParam = initNe.getNameAsString();
            if (!paramNames.contains(startParam)) continue;

            if (fs.getCompare().isEmpty()) continue;
            if (!(fs.getCompare().get() instanceof BinaryExpr cmp)) continue;
            if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                    || !cmpLeft.getNameAsString().equals(counter)) continue;
            // Compare RHS must be a parameter — that's the upper bound.
            if (!(cmp.getRight() instanceof NameExpr cmpRight)) continue;
            String endParam = cmpRight.getNameAsString();
            if (!paramNames.contains(endParam)) continue;
            String endOp;
            if (cmp.getOperator() == BinaryExpr.Operator.LESS) endOp = "<=";
            else if (cmp.getOperator() == BinaryExpr.Operator.LESS_EQUALS) endOp = "<";
            else continue;

            for (ArrayAccessExpr aa : fs.getBody().findAll(ArrayAccessExpr.class)) {
                if (!(aa.getName() instanceof NameExpr arrNe)) continue;
                if (!arrayParams.contains(arrNe.getNameAsString())) continue;
                if (!(aa.getIndex() instanceof NameExpr idxNe)) continue;
                if (!idxNe.getNameAsString().equals(counter)) continue;
                preconditions.add(startParam + " >= 0");
                preconditions.add(endParam + " " + endOp + " " + arrNe.getNameAsString() + ".length");
            }
        }
    }

    /**
     * If {@code expr} is {@code arrayParam.length} for some param in the given set,
     * returns the parameter name; otherwise null.
     */
    private String extractArrayLengthParam(Expression expr, Set<String> arrayParams) {
        if (expr instanceof FieldAccessExpr fae && fae.getNameAsString().equals("length")
                && fae.getScope() instanceof NameExpr ne
                && arrayParams.contains(ne.getNameAsString())) {
            return ne.getNameAsString();
        }
        return null;
    }

    private void analyzeArrayLengthConstraints(MethodDeclaration methodDecl, String paramName,
                                                Set<String> preconditions, ASTCollector collector) {
        Set<String> paramNames = new java.util.HashSet<>();
        methodDecl.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));

        collector.binaryExprs.stream()
            .filter(binExpr -> binExpr.getLeft().toString().equals(paramName + ".length") ||
                               binExpr.getRight().toString().equals(paramName + ".length"))
            // Skip comparisons that appear inside if-throw guards or branching ifs --
            // those are handled by analyzeEarlyValidation (which inverts them) and
            // copying them verbatim here produces contradictory preconditions
            // (e.g. `if (arr.length == 0) throw` would yield both `arr.length == 0`
            // here and `arr.length != 0` from the inversion).
            .filter(binExpr -> !isGuardThrowCondition(binExpr))
            .filter(binExpr -> !isBranchingIfCondition(binExpr))
            .forEach(binExpr -> {
                if (binExpr.getLeft().toString().equals(paramName + ".length")) {
                    String otherSide = binExpr.getRight().toString();
                    // Only add precondition if the other side is a parameter or literal
                    if (!isParameterOrLiteral(otherSide, paramNames)) return;
                    switch (binExpr.getOperator()) {
                        case GREATER:
                            preconditions.add(paramName + ".length > " + otherSide);
                            break;
                        case GREATER_EQUALS:
                            preconditions.add(paramName + ".length >= " + otherSide);
                            break;
                        case EQUALS:
                            preconditions.add(paramName + ".length == " + otherSide);
                            break;
                    }
                } else if (binExpr.getRight().toString().equals(paramName + ".length")) {
                    String otherSide = binExpr.getLeft().toString();
                    // Only add precondition if the other side is a parameter or literal
                    if (!isParameterOrLiteral(otherSide, paramNames)) return;
                    switch (binExpr.getOperator()) {
                        case LESS:
                            preconditions.add(paramName + ".length > " + otherSide);
                            break;
                        case LESS_EQUALS:
                            preconditions.add(paramName + ".length >= " + otherSide);
                            break;
                        case EQUALS:
                            preconditions.add(paramName + ".length == " + otherSide);
                            break;
                    }
                }
            });
    }

    private boolean isParameterOrLiteral(String expr, Set<String> paramNames) {
        if (paramNames.contains(expr)) return true;
        if (expr.matches("-?\\d+")) return true; // integer literal
        // Check for param.length, param.size(), etc.
        for (String param : paramNames) {
            if (expr.startsWith(param + ".")) return true;
        }
        return false;
    }

    String invertCondition(BinaryExpr binExpr) {
        String left = binExpr.getLeft().toString();
        String right = binExpr.getRight().toString();

        return switch (binExpr.getOperator()) {
            case LESS -> left + " >= " + right;
            case LESS_EQUALS -> left + " > " + right;
            case GREATER -> left + " <= " + right;
            case GREATER_EQUALS -> left + " < " + right;
            case EQUALS -> left + " != " + right;
            case NOT_EQUALS -> left + " == " + right;
            case OR -> {
                // !(a || b) means neither a nor b
                if (binExpr.getLeft() instanceof BinaryExpr && binExpr.getRight() instanceof BinaryExpr) {
                    String invertedLeft = invertCondition((BinaryExpr) binExpr.getLeft());
                    String invertedRight = invertCondition((BinaryExpr) binExpr.getRight());
                    yield invertedLeft + " && " + invertedRight;
                }
                yield null;
            }
            default -> null;
        };
    }

    void analyzeNumericConstraints(MethodDeclaration methodDecl, String paramName,
                                    Set<String> preconditions, ASTCollector collector) {
        collector.binaryExprs.stream()
            .filter(expr -> expr.getLeft().toString().equals(paramName) || expr.getRight().toString().equals(paramName))
            .filter(expr -> !isBranchingIfCondition(expr)) // Skip comparisons in if/else branching logic
            .filter(expr -> !isGuardThrowCondition(expr)) // Skip if-throw guards (handled by analyzeEarlyValidation)
            .forEach(expr -> {
                if (expr.getOperator() == BinaryExpr.Operator.GREATER && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " > " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.GREATER_EQUALS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " >= " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.LESS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " < " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.LESS_EQUALS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " <= " + expr.getRight());
                }
            });
    }

    boolean isBranchingIfCondition(Expression expr) {
        com.github.javaparser.ast.Node current = expr;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) parent;
                if (current == ifStmt.getCondition()) {
                    // Only filter if both branches are handled (has else)
                    return ifStmt.getElseStmt().isPresent();
                }
            }
            // Ternary condition is branching logic, not a precondition
            if (parent instanceof ConditionalExpr) {
                ConditionalExpr ternary = (ConditionalExpr) parent;
                if (current == ternary.getCondition()) {
                    return true;
                }
            }
            // Also check if embedded inside a larger condition (e.g., x > 0 && y > 0)
            if (parent instanceof BinaryExpr) {
                BinaryExpr parentBin = (BinaryExpr) parent;
                if (parentBin.getOperator() == BinaryExpr.Operator.AND ||
                    parentBin.getOperator() == BinaryExpr.Operator.OR) {
                    current = parent;
                    continue;
                }
            }
            break;
        }
        return false;
    }

    boolean isGuardThrowCondition(Expression expr) {
        com.github.javaparser.ast.Node current = expr;
        while (current.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = current.getParentNode().get();
            if (parent instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) parent;
                if (current == ifStmt.getCondition()) {
                    // if-throw: handled by analyzeEarlyValidation
                    if (!ifStmt.getThenStmt().findAll(ThrowStmt.class).isEmpty()) {
                        return true;
                    }
                    // if-return without else: guard clause, method handles both paths
                    if (!ifStmt.getElseStmt().isPresent() &&
                        !ifStmt.getThenStmt().findAll(ReturnStmt.class).isEmpty()) {
                        return true;
                    }
                    return false;
                }
            }
            if (parent instanceof BinaryExpr) {
                BinaryExpr parentBin = (BinaryExpr) parent;
                if (parentBin.getOperator() == BinaryExpr.Operator.AND ||
                    parentBin.getOperator() == BinaryExpr.Operator.OR) {
                    current = parent;
                    continue;
                }
            }
            break;
        }
        return false;
    }

    /**
     * Visitor to detect null checks in the method body.
     */
    static class NullCheckVisitor extends VoidVisitorAdapter<Void> {
        private final Set<String> nullChecks = new LinkedHashSet<>();

        @Override
        public void visit(IfStmt ifStmt, Void arg) {
            ifStmt.getCondition().ifBinaryExpr(binExpr -> {
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS &&
                    (binExpr.getRight().isNullLiteralExpr() || binExpr.getLeft().isNullLiteralExpr())) {
                    Expression nonNullExpr = binExpr.getRight().isNullLiteralExpr() ? binExpr.getLeft() : binExpr.getRight();
                    nullChecks.add(nonNullExpr.toString() + " != null");
                } else if (binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS &&
                          (binExpr.getRight().isNullLiteralExpr() || binExpr.getLeft().isNullLiteralExpr())) {
                    Expression nonNullExpr = binExpr.getRight().isNullLiteralExpr() ? binExpr.getLeft() : binExpr.getRight();
                    nullChecks.add(nonNullExpr.toString() + " != null");
                }
            });
            super.visit(ifStmt, arg);
        }

        public Set<String> getNullChecks() {
            return nullChecks;
        }
    }
}
