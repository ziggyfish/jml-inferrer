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

        // Field-bounded loop length: `for(i=0; i<size; i++) data[i]...` requires
        // `size <= data.length` so the access is in-bounds. Sister of
        // analyzeCrossArrayLoopBounds for the field-as-bound case (matrix shapes).
        analyzeFieldBoundedLoopArrayLength(methodDecl, preconditions, collector);

        // 2D-diagonal null/length forall: `for(i=0; i<size; i++) data[i][i]` needs
        // `(\forall int k; 0 <= k < size; data[k] != null && k < data[k].length)`
        // so the inner access is well-defined per element. Companion of P3 in
        // OverflowPreconditionAnalyzer; together they make matrixTrace verify.
        analyzeTwoDimensionalDiagonalAccess(methodDecl, preconditions, collector);

        // 1D-row-major 2D access: nested for-loops with body `arr[i * cols + j]`
        // where arr/rows/cols are parameters. Needs rows*cols size cap on both
        // matrix.length (in-bounds) and INT_MAX (multiply overflow), plus a
        // fixed-K element bound so the partial-sum invariant carries.
        analyzeRowMajor2DAccess(methodDecl, preconditions);

        // Param-bounded loop bounds for `for(i=start; i<end; i++) arr[i] = ...` style.
        // Without `start >= 0` and `end <= arr.length` the access is unproveable.
        analyzeRangeLoopArrayBounds(methodDecl, preconditions, collector);

        // Field-index-into-field-array: `this.data[this.size] = v` needs
        // `this.size < this.data.length` as a precondition. Symmetric to
        // analyzeFieldArrayIndexConstraints but the index is a field, not a param.
        analyzeFieldIndexFieldArrayBounds(methodDecl, preconditions, collector);

        // Modular index arithmetic `arr[(i + offset) % arr.length]` — the `%` makes
        // the result in [0, arr.length-1] by Java semantics, but OpenJML needs
        // arr.length > 0 (to prove the modulo divisor is non-zero) and the offset
        // to be non-negative (Java's `%` follows the dividend's sign).
        analyzeModularIndexAccess(methodDecl, preconditions, spec, collector);

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

    /**
     * True when {@code expr} sits inside a guard position — an if-condition
     * (typically guarding a throw / early return) or the condition of a
     * for/while/do loop. A comparison appearing as a method's return-statement
     * expression is NOT a guard — it's the body's contract — and should not
     * be promoted to a precondition.
     */
    private boolean isGuardContext(com.github.javaparser.ast.Node expr) {
        com.github.javaparser.ast.Node cur = expr;
        while (cur != null) {
            com.github.javaparser.ast.Node parent = cur.getParentNode().orElse(null);
            if (parent == null) return false;
            if (parent instanceof IfStmt is && is.getCondition() == cur) return true;
            if (parent instanceof ForStmt fs && fs.getCompare().orElse(null) == cur) return true;
            if (parent instanceof WhileStmt ws && ws.getCondition() == cur) return true;
            if (parent instanceof DoStmt ds && ds.getCondition() == cur) return true;
            // Stop at the enclosing return — comparisons there are the contract.
            if (parent instanceof ReturnStmt) return false;
            // Method body / class — passed all enclosing scopes without a guard.
            if (parent instanceof MethodDeclaration) return false;
            cur = parent;
        }
        return false;
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

        // Check for length() calls with comparisons. Only treat as a precondition
        // when the comparison sits inside a guard context (if-throw or loop guard) —
        // a comparison that's the body's return expression is the method's
        // CONTRACT, not its precondition. Without this filter, a method like
        // `boolean longerThan(String a, String b) { return a.length() > b.length(); }`
        // would emit `requires a.length() > b.length()` (the body's return),
        // turning the contract into a vacuous precondition.
        collector.methodCallExprs.stream()
            .filter(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("length"))
            .forEach(lengthCall -> {
                collector.binaryExprs.stream()
                    .filter(binExpr -> binExpr.getLeft().toString().contains(paramName + ".length()") ||
                                       binExpr.getRight().toString().contains(paramName + ".length()"))
                    .filter(binExpr -> isGuardContext(binExpr))
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

            Expression name = access.getName();
            while (name instanceof ArrayAccessExpr inner) name = inner.getName();
            String arrField = fieldName(name, methodDecl);
            if (arrField == null) continue;

            // Simple shape: `data[idxField]`.
            String idxField = fieldName(index, methodDecl);
            if (idxField != null && !idxField.equals(arrField)) {
                // StackPopPrecondition pattern: `this.size--; return this.data[this.size];`
                // The access reads the POST-decrement value, so the bound `size >= 0` is
                // insufficient — post value could be -1. Detect a decrement of idxField
                // before this access and emit the stricter bound instead.
                int decDelta = countDecrementsBefore(methodDecl, idxField, access);
                int incDelta = countIncrementsBefore(methodDecl, idxField, access);
                int netShift = decDelta - incDelta; // positive => post = pre - netShift
                // General form: post = pre - netShift. Safe access needs
                //   netShift <= pre < length + netShift
                // which, turned into a JML clause, is
                //   (pre >= netShift) AND (pre < length + netShift).
                String shiftStr = (netShift >= 0 ? "+ " : "- ") + Math.abs(netShift);
                // Null-safety prelude: emit `this.arrField != null` BEFORE any
                // bound that dereferences it. OpenJML evaluates preconditions
                // in source order — without this leading null check the bound
                // raises UndefinedNullDeReference before the null precondition
                // fires. See analyzeFieldArrayIndexConstraints for the
                // same pattern on parameter-indexed accesses.
                preconditions.add("this." + arrField + " != null");
                if (netShift == 0) {
                    preconditions.add("this." + idxField + " >= 0");
                    preconditions.add("this." + idxField + " < this." + arrField + ".length");
                } else {
                    preconditions.add("this." + idxField + " >= " + netShift);
                    preconditions.add("this." + idxField + " < this." + arrField + ".length "
                            + shiftStr);
                }
                continue;
            }

            // Arithmetic shape: `data[field + lit]` or `data[field - lit]`. Emit
            // bounds on the full index expression so the access is provably safe.
            // Example: `data[top - 1]` with `top >= 1 && top <= data.length` —
            // OpenJML composes `top - 1 >= 0` and `top - 1 < data.length`.
            if (index instanceof BinaryExpr be
                    && (be.getOperator() == BinaryExpr.Operator.PLUS
                        || be.getOperator() == BinaryExpr.Operator.MINUS)
                    && be.getRight().isIntegerLiteralExpr()) {
                String baseField = fieldName(be.getLeft(), methodDecl);
                if (baseField != null && !baseField.equals(arrField)) {
                    String indexStr = "this." + baseField + " "
                            + (be.getOperator() == BinaryExpr.Operator.PLUS ? "+" : "-")
                            + " " + be.getRight().asIntegerLiteralExpr().asInt();
                    // Null-safety prelude — same rationale as above branches.
                    preconditions.add("this." + arrField + " != null");
                    preconditions.add("(" + indexStr + ") >= 0");
                    preconditions.add("(" + indexStr + ") < this." + arrField + ".length");
                }
            }
        }
    }

    /** Count `field--` / `field -= 1` that appear BEFORE {@code beforeNode} in source. */
    private int countDecrementsBefore(MethodDeclaration methodDecl, String fieldName,
                                       com.github.javaparser.ast.Node beforeNode) {
        if (methodDecl.getBody().isEmpty()) return 0;
        int before = positionLine(beforeNode) * 10000 + positionCol(beforeNode);
        int count = 0;
        for (UnaryExpr ue : methodDecl.getBody().get().findAll(UnaryExpr.class)) {
            if (ue.getOperator() != UnaryExpr.Operator.PREFIX_DECREMENT
                    && ue.getOperator() != UnaryExpr.Operator.POSTFIX_DECREMENT) continue;
            if (!matchesField(ue.getExpression(), fieldName)) continue;
            if (positionLine(ue) * 10000 + positionCol(ue) < before) count++;
        }
        return count;
    }

    /** Count `field++` / `field += 1` that appear BEFORE {@code beforeNode} in source. */
    private int countIncrementsBefore(MethodDeclaration methodDecl, String fieldName,
                                       com.github.javaparser.ast.Node beforeNode) {
        if (methodDecl.getBody().isEmpty()) return 0;
        int before = positionLine(beforeNode) * 10000 + positionCol(beforeNode);
        int count = 0;
        for (UnaryExpr ue : methodDecl.getBody().get().findAll(UnaryExpr.class)) {
            if (ue.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT
                    && ue.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT) continue;
            if (!matchesField(ue.getExpression(), fieldName)) continue;
            if (positionLine(ue) * 10000 + positionCol(ue) < before) count++;
        }
        return count;
    }

    private boolean matchesField(Expression expr, String fieldName) {
        if (expr instanceof NameExpr ne) return ne.getNameAsString().equals(fieldName);
        if (expr instanceof FieldAccessExpr fa) {
            return fa.getScope().toString().equals("this") && fa.getNameAsString().equals(fieldName);
        }
        return false;
    }

    private int positionLine(com.github.javaparser.ast.Node node) {
        return node.getBegin().map(p -> p.line).orElse(Integer.MAX_VALUE);
    }

    private int positionCol(com.github.javaparser.ast.Node node) {
        return node.getBegin().map(p -> p.column).orElse(Integer.MAX_VALUE);
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
            Expression index = access.getIndex();
            if (!(index instanceof NameExpr ne) || !ne.getNameAsString().equals(paramName)) continue;

            // Resolve the underlying field name. For a 2D access like `data[row][col]`
            // there are two ArrayAccessExpr nodes — the outer one (index = col, name =
            // `data[row]`) and the inner one (index = row, name = `data`). The correct
            // bound for `col` is `data[row].length`, not `data.length`, so detect this
            // shape and emit the second-dimension bound instead.
            Expression name = access.getName();
            if (name instanceof ArrayAccessExpr innerAae) {
                Expression innerBase = innerAae.getName();
                while (innerBase instanceof ArrayAccessExpr inn) innerBase = inn.getName();
                String fieldName = null;
                if (innerBase instanceof FieldAccessExpr fa
                        && fa.getScope().toString().equals("this")) {
                    fieldName = fa.getNameAsString();
                } else if (innerBase instanceof NameExpr innerNe
                        && AnalysisUtils.isFieldReference(methodDecl, innerNe.getNameAsString())) {
                    fieldName = innerNe.getNameAsString();
                }
                if (fieldName != null && innerAae.getIndex() instanceof NameExpr rowNe
                        && methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(rowNe.getNameAsString()))) {
                    // Emit the full well-definedness chain for `this.field[row][paramName]`
                    // in left-to-right order. JML evaluates preconditions sequentially;
                    // each precondition's well-definedness uses only earlier ones, so the
                    // chain has to land in this exact order. Without this, OpenJML fires
                    // UndefinedNullDeReference / UndefinedNegativeIndex on the col bound
                    // even when later preconditions would have proved each step. The
                    // existing analyzer passes (analyzeInstanceFieldNullPreconditions for
                    // the 2D guarded null check, analyzeNumericConstraints for the row
                    // bounds) emit duplicates afterwards, but LinkedHashSet de-dupes by
                    // value, so the first insertion's position wins.
                    String rowName = rowNe.getNameAsString();
                    preconditions.add("this." + fieldName + " != null");
                    preconditions.add(rowName + " >= 0");
                    preconditions.add(rowName + " < this." + fieldName + ".length");
                    preconditions.add("this." + fieldName + "[" + rowName + "] != null");
                    preconditions.add(paramName + " >= 0");
                    preconditions.add(paramName + " < this." + fieldName
                            + "[" + rowName + "].length");
                    continue;
                }
            }

            String fieldName = null;
            while (name instanceof ArrayAccessExpr inner) name = inner.getName();
            if (name instanceof FieldAccessExpr fa && fa.getScope().toString().equals("this")) {
                fieldName = fa.getNameAsString();
            } else if (name instanceof NameExpr nameExpr) {
                String n = nameExpr.getNameAsString();
                if (AnalysisUtils.isFieldReference(methodDecl, n)) fieldName = n;
            }
            if (fieldName == null) continue;

            // Null-safety prelude — see the 2D branch above for the rationale.
            preconditions.add("this." + fieldName + " != null");
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
        Set<String> twoDRowAccesses = new LinkedHashSet<>();
        collector.arrayAccessExprs.forEach(aa -> {
            Expression base = aa.getName();
            // For `data[row][col]` the outer aa's name is `data[row]` (itself an
            // ArrayAccessExpr). Recognise this shape and, when `data` is a field and
            // `row` is a parameter, record `this.data[row] != null` so subsequent
            // access of the inner array is sound.
            if (base instanceof ArrayAccessExpr innerAae) {
                Expression innerBase = innerAae.getName();
                while (innerBase instanceof ArrayAccessExpr inn) innerBase = inn.getName();
                String fieldName = null;
                if (innerBase instanceof FieldAccessExpr fa
                        && fa.getScope().toString().equals("this")
                        && refFieldNames.contains(fa.getNameAsString())) {
                    fieldName = fa.getNameAsString();
                } else if (innerBase instanceof NameExpr ne
                        && refFieldNames.contains(ne.getNameAsString())) {
                    fieldName = ne.getNameAsString();
                }
                if (fieldName != null && innerAae.getIndex() instanceof NameExpr idxNe
                        && methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(idxNe.getNameAsString()))) {
                    // Guard the row-access null check by the bounds conditions so
                    // OpenJML's well-definedness check for `data[row]` passes even
                    // when preconditions are evaluated eagerly / independently.
                    String idx = idxNe.getNameAsString();
                    twoDRowAccesses.add("(" + idx + " >= 0 && " + idx + " < this." + fieldName
                            + ".length) ==> this." + fieldName + "[" + idx + "] != null");
                }
            }

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
        for (String rowAccess : twoDRowAccesses) {
            // twoDRowAccesses entries are already full precondition clauses
            // (the guarded implication includes `!= null` at the end).
            preconditions.add(rowAccess);
        }
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
        // Collect names of all instance reference-typed fields. Used below to
        // prepend `this.field != null` whenever an inverted-guard precondition
        // dereferences such a field via `.length`, `.size()`, or `[...]`.
        // Mirrors the gathering pattern in analyzeInstanceFieldNullPreconditions.
        Set<String> refFieldNames = methodDecl.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .filter(f -> !f.getCommonType().isPrimitiveType())
                        .flatMap(f -> f.getVariables().stream())
                        .map(com.github.javaparser.ast.body.VariableDeclarator::getNameAsString)
                        .collect(java.util.stream.Collectors.toSet()))
                .orElseGet(java.util.HashSet::new);

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
                        addNullPreludeForFieldDereferences(invertedCondition, refFieldNames, preconditions);
                        preconditions.add(invertedCondition);
                    }
                } else if (condition instanceof UnaryExpr) {
                    UnaryExpr unaryExpr = (UnaryExpr) condition;
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
                        // !(condition) in if-throw means condition must be true
                        String inner = unaryExpr.getExpression().toString();
                        if (scopeChecker.isMethodScopeSafe(inner, methodDecl, paramNames)) {
                            addNullPreludeForFieldDereferences(inner, refFieldNames, preconditions);
                            preconditions.add(inner);
                        }
                    }
                }
            }
        });
    }

    /**
     * For every reference field `f` whose dereference appears in {@code condition}
     * (as `f.length`, `this.f.length`, `f.size()`, `this.f.size()`, or `f[...]`),
     * inserts `this.f != null` into {@code preconditions} BEFORE the caller adds
     * the dereferencing condition. Without this prelude, the dereferencing
     * precondition fires UndefinedNullDeReference when the field is null —
     * even if a `this.f != null` precondition is later emitted by another
     * analyzer, OpenJML evaluates preconditions in source-order so the prelude
     * has to come first. LinkedHashSet preserves first-insertion order, so the
     * later analyzer's duplicate add is silently dropped.
     */
    private void addNullPreludeForFieldDereferences(String condition, Set<String> refFieldNames,
                                                     Set<String> preconditions) {
        for (String field : refFieldNames) {
            // Match `field.` or `field[` (qualified or bare). Word-boundary on the
            // left avoids false positives on prefix overlaps like `count` matching
            // `accountant`.
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                    "(?<![\\w.])" + java.util.regex.Pattern.quote(field) + "[\\.\\[]");
            if (p.matcher(condition).find()) {
                preconditions.add("this." + field + " != null");
            }
        }
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
     * Emits the 2D-diagonal null/length forall when a method body contains
     * {@code FIELD2D[i][i]} access inside a for-loop bounded by a numeric
     * instance field. Without this, the inner access is ill-defined and any
     * downstream forall over diagonal elements (e.g. the overflow bound from
     * {@code OverflowPreconditionAnalyzer}) cannot be proven well-formed.
     *
     * <p>Emitted shape:
     * {@code (\forall int k; LO <= k < FIELD; FIELD2D[k] != null && k < FIELD2D[k].length)}.
     * </p>
     */
    private void analyzeTwoDimensionalDiagonalAccess(MethodDeclaration methodDecl,
                                                      Set<String> preconditions,
                                                      ASTCollector collector) {
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
            int lo = initExpr.asIntegerLiteralExpr().asInt();
            if (lo < 0) continue;

            if (fs.getCompare().isEmpty()) continue;
            if (!(fs.getCompare().get() instanceof BinaryExpr cmp)) continue;
            if (cmp.getOperator() != BinaryExpr.Operator.LESS) continue;
            if (!(cmp.getLeft() instanceof NameExpr lne)
                    || !lne.getNameAsString().equals(counter)) continue;

            String boundField = fieldName(cmp.getRight(), methodDecl);
            if (boundField == null) continue;

            // Find a 2D-diagonal access in the body: `<field>[counter][counter]`.
            for (ArrayAccessExpr outer : fs.getBody().findAll(ArrayAccessExpr.class)) {
                if (!(outer.getIndex() instanceof NameExpr outerIdx)
                        || !outerIdx.getNameAsString().equals(counter)) continue;
                if (!(outer.getName() instanceof ArrayAccessExpr inner)) continue;
                if (!(inner.getIndex() instanceof NameExpr innerIdx)
                        || !innerIdx.getNameAsString().equals(counter)) continue;
                String diagField = fieldName(inner.getName(), methodDecl);
                if (diagField == null) continue;

                String diagPrefix = "this." + diagField;
                String boundPrefix = "this." + boundField;
                preconditions.add("(\\forall int k; " + lo + " <= k && k < " + boundPrefix
                        + "; " + diagPrefix + "[k] != null && k < " + diagPrefix + "[k].length)");
                break; // one forall is enough per loop
            }
        }
    }

    /**
     * For nested loops of the shape
     * {@code for(int i=0; i<rows; i++) for(int j=0; j<cols; j++) ... arr[i*cols+j] ...}
     * where {@code arr}, {@code rows}, {@code cols} are parameters, emits the
     * preconditions necessary for the indexing and overflow assertions to discharge:
     * non-negativity of the bounds, the rows*cols size cap on the array length,
     * the rows*cols cap on Integer.MAX_VALUE (so {@code i*cols} does not overflow),
     * and a fixed-K element bound on {@code arr[k]}.
     *
     * <p>The matching nested loop invariants are emitted by
     * {@code LoopInvariantAnalyzer}; both halves are required to verify together.</p>
     */
    private void analyzeRowMajor2DAccess(MethodDeclaration methodDecl,
                                          Set<String> preconditions) {
        Set<String> paramNames = new HashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            paramNames.add(p.getNameAsString());
        }
        for (ForStmt outer : methodDecl.findAll(ForStmt.class)) {
            ForLoopShape outerShape = readSimpleZeroBoundedFor(outer, paramNames);
            if (outerShape == null) continue;
            for (ForStmt inner : outer.getBody().findAll(ForStmt.class)) {
                if (inner == outer) continue;
                ForLoopShape innerShape = readSimpleZeroBoundedFor(inner, paramNames);
                if (innerShape == null) continue;
                if (innerShape.bound.equals(outerShape.bound)) continue;

                String arrName = findRowMajorArray(inner.getBody(),
                        outerShape.counter, innerShape.counter, innerShape.bound, paramNames);
                if (arrName == null) continue;

                String rows = outerShape.bound;
                String cols = innerShape.bound;
                preconditions.add(arrName + " != null");
                preconditions.add(rows + " >= 0");
                preconditions.add(cols + " >= 0");
                preconditions.add("(\\bigint) " + rows + " * " + cols + " <= " + arrName + ".length");
                preconditions.add("(\\bigint) " + rows + " * " + cols + " <= 1000000");
                preconditions.add("(\\forall int k; 0 <= k && k < " + arrName
                        + ".length; " + arrName + "[k] >= -1000 && " + arrName + "[k] <= 1000)");
                return; // one match per method
            }
        }
    }

    private static class ForLoopShape {
        final String counter;
        final String bound;
        ForLoopShape(String counter, String bound) {
            this.counter = counter;
            this.bound = bound;
        }
    }

    /**
     * Returns the (counter, bound) shape iff the for-loop is
     * {@code for(int counter = 0; counter < bound; counter++)} with
     * {@code bound} a parameter name.
     */
    private ForLoopShape readSimpleZeroBoundedFor(ForStmt fs, Set<String> paramNames) {
        if (fs.getInitialization().size() != 1) return null;
        Expression init = fs.getInitialization().get(0);
        if (!(init instanceof VariableDeclarationExpr vde)) return null;
        if (vde.getVariables().size() != 1) return null;
        String counter = vde.getVariables().get(0).getNameAsString();
        Optional<Expression> initOpt = vde.getVariables().get(0).getInitializer();
        if (initOpt.isEmpty() || !initOpt.get().isIntegerLiteralExpr()) return null;
        if (initOpt.get().asIntegerLiteralExpr().asInt() != 0) return null;
        if (fs.getCompare().isEmpty()
                || !(fs.getCompare().get() instanceof BinaryExpr cmp)) return null;
        if (cmp.getOperator() != BinaryExpr.Operator.LESS) return null;
        if (!(cmp.getLeft() instanceof NameExpr lne)
                || !lne.getNameAsString().equals(counter)) return null;
        if (!(cmp.getRight() instanceof NameExpr bne)
                || !paramNames.contains(bne.getNameAsString())) return null;
        return new ForLoopShape(counter, bne.getNameAsString());
    }

    /**
     * Returns the parameter array name iff the body contains
     * {@code arr[outerCounter * innerBound + innerCounter]} (in either operand
     * order for the multiplication and for the addition).
     */
    private String findRowMajorArray(Statement body, String outerCounter,
                                     String innerCounter, String innerBound,
                                     Set<String> paramNames) {
        for (ArrayAccessExpr aae : body.findAll(ArrayAccessExpr.class)) {
            if (!(aae.getName() instanceof NameExpr arrNe)) continue;
            if (!paramNames.contains(arrNe.getNameAsString())) continue;
            if (!(aae.getIndex() instanceof BinaryExpr be)
                    || be.getOperator() != BinaryExpr.Operator.PLUS) continue;
            BinaryExpr mulExpr = null;
            String addOther = null;
            if (be.getLeft() instanceof BinaryExpr lhs
                    && lhs.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                mulExpr = lhs;
                addOther = be.getRight().toString();
            } else if (be.getRight() instanceof BinaryExpr rhs
                    && rhs.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                mulExpr = rhs;
                addOther = be.getLeft().toString();
            }
            if (mulExpr == null || !addOther.equals(innerCounter)) continue;

            String mulL = mulExpr.getLeft().toString();
            String mulR = mulExpr.getRight().toString();
            boolean shapeOK = (mulL.equals(outerCounter) && mulR.equals(innerBound))
                    || (mulR.equals(outerCounter) && mulL.equals(innerBound));
            if (shapeOK) return arrNe.getNameAsString();
        }
        return null;
    }

    /**
     * For loops of the shape {@code for (int i = LO; i <op> FIELD; i++)} (where LO is a
     * non-negative literal and FIELD is a numeric instance field) whose body contains
     * an access {@code this.arrayField[i]} (1D or nested 2D), emit
     * {@code FIELD <= arrayField.length} so the access is in-bounds. Without this the
     * inferrer emits {@code arrayField != null} and {@code FIELD >= 0} but not the
     * cross-field bound, leaving OpenJML unable to discharge the upper-bound
     * assertion. Sister of {@link #analyzeCrossArrayLoopBounds} for field-bounded
     * (rather than parameter-bounded) loops; this is the matrix-shape pattern.
     */
    private void analyzeFieldBoundedLoopArrayLength(MethodDeclaration methodDecl,
                                                     Set<String> preconditions,
                                                     ASTCollector collector) {
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
            if (!(cmp.getLeft() instanceof NameExpr lne)
                    || !lne.getNameAsString().equals(counter)) continue;

            // Upper bound must be a numeric instance field. fieldName returns null
            // for `arr.length` (scope `arr`, not `this`) so the cross-array case
            // does not collide with this one.
            String boundField = fieldName(cmp.getRight(), methodDecl);
            if (boundField == null) continue;

            String op;
            if (cmp.getOperator() == BinaryExpr.Operator.LESS) op = "<=";
            else if (cmp.getOperator() == BinaryExpr.Operator.LESS_EQUALS) op = "<";
            else continue;

            for (ArrayAccessExpr aa : fs.getBody().findAll(ArrayAccessExpr.class)) {
                // P1 fires only when this access node IS the array's first
                // dimension and ITS OWN index is the counter. For 2D access
                // shapes like `data[row][counter]`, the OUTER access (whose
                // index is the counter) has name `data[row]`, so the bound
                // would be on `data[row].length` — that's a different shape
                // handled by OverflowPreconditionAnalyzer's row-fixed
                // accumulator. For 2D-diagonal `data[counter][counter]`, the
                // INNER access (whose name is the field directly) has its
                // index as the counter, which matches this trigger and emits
                // the cross-field length on the outer dimension correctly.
                if (!(aa.getIndex() instanceof NameExpr idxNe)
                        || !idxNe.getNameAsString().equals(counter)) continue;
                String arrField = fieldName(aa.getName(), methodDecl);
                if (arrField == null) continue;
                if (arrField.equals(boundField)) continue;

                preconditions.add("this." + arrField + " != null");
                preconditions.add("this." + boundField + " " + op
                        + " this." + arrField + ".length");
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
                String accessedArr = arrNe.getNameAsString();
                Expression idx = aa.getIndex();
                // Direct counter index `arr[i]` — original shape.
                if (idx instanceof NameExpr idxNe
                        && idxNe.getNameAsString().equals(counter)) {
                    preconditions.add(startParam + " >= 0");
                    preconditions.add(endParam + " " + endOp + " "
                            + accessedArr + ".length");
                    continue;
                }
                // Offset-shifted index `arr[i - startParam]` (the copy-range case):
                // the index ranges over [0, end - start), so the access requires
                // `dst.length >= end - start` AND `start >= 0`. The comparison
                // operator carries through (`<` → `>=`, `<=` → `>`).
                if (idx instanceof BinaryExpr be
                        && be.getOperator() == BinaryExpr.Operator.MINUS
                        && be.getLeft() instanceof NameExpr leftNe
                        && leftNe.getNameAsString().equals(counter)
                        && be.getRight() instanceof NameExpr rightNe
                        && rightNe.getNameAsString().equals(startParam)) {
                    String shiftedOp = endOp.equals("<=") ? ">=" : ">";
                    preconditions.add(startParam + " >= 0");
                    preconditions.add(accessedArr + ".length " + shiftedOp + " "
                            + endParam + " - " + startParam);
                }
                // Offset-shifted index `arr[startParam + i]` — symmetric to the
                // copy-range case, target is `dst[dstStart + i]` style.
                if (idx instanceof BinaryExpr be2
                        && be2.getOperator() == BinaryExpr.Operator.PLUS) {
                    boolean leftIsCounter = be2.getLeft() instanceof NameExpr lne2
                            && lne2.getNameAsString().equals(counter);
                    boolean rightIsCounter = be2.getRight() instanceof NameExpr rne2
                            && rne2.getNameAsString().equals(counter);
                    Expression offsetExpr = leftIsCounter ? be2.getRight()
                            : (rightIsCounter ? be2.getLeft() : null);
                    if (offsetExpr instanceof NameExpr offNe
                            && paramNames.contains(offNe.getNameAsString())) {
                        String off = offNe.getNameAsString();
                        // Index range: [off + start, off + end). Need
                        // `arr.length >= off + end` and `off + start >= 0`.
                        String shiftedOp = endOp.equals("<=") ? ">=" : ">";
                        preconditions.add(off + " + " + startParam + " >= 0");
                        preconditions.add(accessedArr + ".length " + shiftedOp + " "
                                + off + " + " + endParam);
                    }
                }
            }
        }
    }

    /**
     * Recognises array accesses indexed by a modular expression — {@code arr[(EXPR) % N]}
     * — and emits the preconditions that make the access provably in-bounds.
     *
     * <p>Specifically, for every {@code accessedArr[X % divisor]} where {@code divisor}
     * resolves (either directly or via a local) to {@code accessedArr.length}, emit:</p>
     * <ul>
     *   <li>{@code accessedArr.length > 0} as a precondition (the divisor must be non-zero),
     *       and as a loop invariant when the access is inside a loop.</li>
     *   <li>For every parameter referenced positively in {@code EXPR}, emit
     *       {@code param >= 0} (Java's {@code %} follows the dividend's sign, so a
     *       negative dividend yields a negative result and an out-of-bounds index).</li>
     * </ul>
     *
     * <p>Handles two divisor shapes:</p>
     * <ul>
     *   <li>{@code arr[X % arr.length]} — divisor is the array's own length.</li>
     *   <li>{@code int n = arr.length; ...; arr[X % n] = ...;} — divisor is a local
     *       initialised from the array's length (the rotate pattern).</li>
     * </ul>
     */
    private void analyzeModularIndexAccess(MethodDeclaration methodDecl,
                                            Set<String> preconditions,
                                            com.jml.inferrer.model.MethodSpecification spec,
                                            ASTCollector collector) {
        Set<String> paramNames = new java.util.LinkedHashSet<>();
        Set<String> arrayParams = new java.util.LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            paramNames.add(p.getNameAsString());
            if (p.getType().asString().contains("[]")) arrayParams.add(p.getNameAsString());
        }
        // Map: local name -> array name, when `int local = array.length;` is in scope.
        Map<String, String> lengthLocalToArray = new java.util.LinkedHashMap<>();
        methodDecl.findAll(com.github.javaparser.ast.expr.VariableDeclarationExpr.class).forEach(vde ->
                vde.getVariables().forEach(v -> v.getInitializer().ifPresent(init -> {
                    if (init instanceof FieldAccessExpr fae
                            && fae.getNameAsString().equals("length")
                            && fae.getScope() instanceof NameExpr ne
                            && arrayParams.contains(ne.getNameAsString())) {
                        lengthLocalToArray.put(v.getNameAsString(), ne.getNameAsString());
                    }
                })));

        for (ArrayAccessExpr aae : methodDecl.findAll(ArrayAccessExpr.class)) {
            // Index must be a `%` binary expression.
            if (!(aae.getIndex() instanceof BinaryExpr modExpr)) continue;
            if (modExpr.getOperator() != BinaryExpr.Operator.REMAINDER) continue;

            // Divisor must resolve to a parameter array's length, either directly or via
            // a local. The accessed array can be any array (parameter, field, or local) —
            // what matters is the divisor: when divisor > 0, Java's `%` produces a result
            // in [-(divisor-1), divisor-1], and additionally non-negative iff the dividend
            // is non-negative. Drives ArrayRotation.rotate where the access target is a
            // freshly-allocated local but the divisor `n = arr.length` ties to the param.
            Expression divisor = modExpr.getRight();
            String resolvedDivisorArray = null;
            if (divisor instanceof FieldAccessExpr divFae
                    && divFae.getNameAsString().equals("length")
                    && divFae.getScope() instanceof NameExpr divNe
                    && arrayParams.contains(divNe.getNameAsString())) {
                resolvedDivisorArray = divNe.getNameAsString();
            } else if (divisor instanceof NameExpr divNe
                    && lengthLocalToArray.containsKey(divNe.getNameAsString())) {
                resolvedDivisorArray = lengthLocalToArray.get(divNe.getNameAsString());
            }
            if (resolvedDivisorArray == null) continue;

            preconditions.add(resolvedDivisorArray + ".length > 0");

            // Inside a loop, also emit as loop invariant so the body can prove the access.
            Optional<com.github.javaparser.ast.stmt.ForStmt> forOpt =
                    aae.findAncestor(com.github.javaparser.ast.stmt.ForStmt.class);
            if (forOpt.isPresent() && spec != null) {
                int line = forOpt.get().getBegin().map(p -> p.line).orElse(0);
                spec.addLoopInvariant(resolvedDivisorArray + ".length > 0", line);
            }

            // For every parameter that appears in the dividend additively (e.g. shift in
            // `(i + shift) % n`), require it to be non-negative so the dividend stays >= 0.
            // Conservative: only require `>= 0` for parameters added positively.
            collectAdditiveParams(modExpr.getLeft(), paramNames).forEach(p ->
                    preconditions.add(p + " >= 0"));
        }
    }

    /**
     * Collects parameter names that appear in {@code expr} as positive operands of
     * {@code +} (so the overall sign of the expression is bounded below by their values
     * being non-negative). Conservative: bails on subtraction or unrecognised shapes.
     */
    private Set<String> collectAdditiveParams(Expression expr, Set<String> paramNames) {
        Set<String> out = new java.util.LinkedHashSet<>();
        collectAdditiveParamsHelper(expr, paramNames, out);
        return out;
    }

    private void collectAdditiveParamsHelper(Expression expr, Set<String> paramNames, Set<String> out) {
        if (expr instanceof EnclosedExpr enc) {
            collectAdditiveParamsHelper(enc.getInner(), paramNames, out);
            return;
        }
        if (expr instanceof BinaryExpr be && be.getOperator() == BinaryExpr.Operator.PLUS) {
            collectAdditiveParamsHelper(be.getLeft(), paramNames, out);
            collectAdditiveParamsHelper(be.getRight(), paramNames, out);
            return;
        }
        if (expr instanceof NameExpr ne && paramNames.contains(ne.getNameAsString())) {
            out.add(ne.getNameAsString());
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
            // The body's return expression IS the contract, not a precondition —
            // `boolean hasItems(int[] arr) { return arr.length > 0; }` would
            // otherwise emit `requires arr.length > 0` and invert the spec.
            .filter(binExpr -> !isInReturnExpression(binExpr))
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
            .filter(expr -> !isInReturnExpression(expr)) // The body's return expression IS the contract,
                                                         // not a precondition the caller must satisfy.
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

    /**
     * True when {@code expr} sits anywhere inside a {@link ReturnStmt}'s
     * value expression. The return value is the method's contract
     * (captured by the ensures clause), not a precondition the caller
     * must satisfy. Without this filter, a method like
     * {@code boolean isPositive(int n) { return n > 0; }} would emit
     * {@code requires n > 0} — turning the spec inside out.
     */
    boolean isInReturnExpression(Expression expr) {
        com.github.javaparser.ast.Node cur = expr;
        while (cur.getParentNode().isPresent()) {
            com.github.javaparser.ast.Node parent = cur.getParentNode().get();
            if (parent instanceof ReturnStmt) return true;
            // Stop at the enclosing method — anything above is class scope.
            if (parent instanceof MethodDeclaration) return false;
            cur = parent;
        }
        return false;
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
