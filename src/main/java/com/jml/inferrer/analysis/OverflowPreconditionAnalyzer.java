package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Emits preconditions that guarantee arithmetic operations in the method body
 * cannot overflow. Required when OpenJML is configured with
 * {@code --code-math=safe} and {@code --arithmetic-failure=hard}, where every
 * int add/sub/mul/neg/increment must stay within {@code [Integer.MIN_VALUE,
 * Integer.MAX_VALUE]}.
 *
 * <p>Walks every arithmetic operation — return expressions, local declarations,
 * compound assignments, unary increments — and for each operand expressible
 * purely in terms of parameters, fields, and previously-assigned locals,
 * emits a {@code (\bigint)}-cast bound precondition. Locals initialised from
 * parameter-only expressions are substituted into the emitted spec so the
 * precondition references only pre-state values.</p>
 *
 * <p>Operations whose operands depend on loop variables or otherwise non-pre-state
 * values are left to the loop-invariant layer.</p>
 */
class OverflowPreconditionAnalyzer {

    private static final Set<String> INTEGER_TYPE_NAMES =
            Set.of("int", "long", "short", "byte", "char");

    private Set<String> paramNames;
    private Set<String> intParamNames;
    private Set<String> intArrayParamNames;
    private Set<String> fieldNames;
    private Set<String> intFieldNames;
    private Set<String> intArrayFieldNames;
    private Map<String, Expression> localInits;
    private Set<String> loopVars;
    private MethodDeclaration methodDecl;

    void inferOverflowPreconditions(MethodDeclaration methodDecl, MethodSpecification spec,
                                     ASTCollector collector) {
        this.methodDecl = methodDecl;
        this.paramNames = methodDecl.getParameters().stream()
                .map(Parameter::getNameAsString)
                .collect(Collectors.toSet());
        this.intParamNames = methodDecl.getParameters().stream()
                .filter(p -> isIntegerPrimitive(p.getType().asString()))
                .map(Parameter::getNameAsString)
                .collect(Collectors.toSet());
        this.intArrayParamNames = methodDecl.getParameters().stream()
                .filter(p -> isIntegerArrayType(p.getType().asString()))
                .map(Parameter::getNameAsString)
                .collect(Collectors.toSet());
        this.fieldNames = getEnclosingClassFieldNames(methodDecl);
        this.intFieldNames = getEnclosingClassFieldsOfPredicate(methodDecl,
                OverflowPreconditionAnalyzer::isIntegerPrimitive);
        this.intArrayFieldNames = getEnclosingClassFieldsOfPredicate(methodDecl,
                OverflowPreconditionAnalyzer::isIntegerArrayType);
        this.localInits = collectLocalInitializers(collector);
        this.loopVars = collectLoopVariables(methodDecl);

        Set<String> emitted = new LinkedHashSet<>();

        for (AssignExpr assign : collector.assignExprs) {
            handleCompoundAssignment(assign, emitted);
            handleAssignmentOverflow(assign, emitted);
        }

        for (UnaryExpr unary : collector.unaryExprs) {
            handleUnaryNegation(unary, emitted);
            handleUnaryIncrement(unary, emitted);
        }

        for (BinaryExpr binary : collector.binaryExprs) {
            handleBinaryArithmetic(binary, emitted);
            handleDivisionByZero(binary, emitted);
        }

        for (ArrayCreationExpr arrayCreate : collector.arrayCreationExprs) {
            handleArrayCreation(arrayCreate, emitted);
        }

        emitted.forEach(spec::addPrecondition);
    }

    private void handleArrayCreation(ArrayCreationExpr arrayCreate, Set<String> emitted) {
        // `new T[n]` throws NegativeArraySizeException for n < 0. Emit `n >= 0` for every
        // dimension whose size is a pre-state-expressible integer expression.
        for (var level : arrayCreate.getLevels()) {
            level.getDimension().ifPresent(dim -> {
                String sizeStr = toIntStr(dim);
                if (sizeStr != null) {
                    emitted.add(sizeStr + " >= 0");
                }
            });
        }
    }

    // ---------------------------------------------------------------------
    // Handlers — one per syntactic shape
    // ---------------------------------------------------------------------

    private void handleCompoundAssignment(AssignExpr assign, Set<String> emitted) {
        String opSym = compoundOpSymbol(assign.getOperator());
        if (opSym == null) return;

        String targetRef = resolveFieldRef(assign.getTarget());
        if (targetRef == null) return;

        String valueStr = toBigintStr(assign.getValue());
        if (valueStr == null) return;

        String targetBigint = "(\\bigint) " + targetRef;
        emitBigintBoundsRaw(emitted, "(" + targetBigint + " " + opSym + " " + valueStr + ")");
    }

    private void handleAssignmentOverflow(AssignExpr assign, Set<String> emitted) {
        // Plain assignment `x = expr` — need to prove RHS doesn't overflow
        // as an int, but only arithmetic ops in the RHS generate overflow
        // obligations. The BinaryExpr walker handles those.
        // Unary negation handling is covered by the unary walker.
    }

    private void handleUnaryNegation(UnaryExpr unary, Set<String> emitted) {
        if (unary.getOperator() != UnaryExpr.Operator.MINUS) return;
        Expression operand = unary.getExpression();
        String intForm = toIntStr(operand);
        if (intForm == null) return;
        emitted.add(intForm + " != Integer.MIN_VALUE");
    }

    private void handleUnaryIncrement(UnaryExpr unary, Set<String> emitted) {
        UnaryExpr.Operator op = unary.getOperator();
        boolean isIncrement = op == UnaryExpr.Operator.POSTFIX_INCREMENT
                || op == UnaryExpr.Operator.PREFIX_INCREMENT;
        boolean isDecrement = op == UnaryExpr.Operator.POSTFIX_DECREMENT
                || op == UnaryExpr.Operator.PREFIX_DECREMENT;
        if (!isIncrement && !isDecrement) return;

        String intForm = toIntStr(unary.getExpression());
        if (intForm == null) return;

        // Skip if the target is itself a loop variable — handled by loop invariants
        if (unary.getExpression() instanceof NameExpr ne && loopVars.contains(ne.getNameAsString())) {
            return;
        }

        if (isIncrement) {
            emitted.add(intForm + " < Integer.MAX_VALUE");
        } else {
            emitted.add(intForm + " > Integer.MIN_VALUE");
        }
    }

    private void handleBinaryArithmetic(BinaryExpr binary, Set<String> emitted) {
        String opSym = binaryArithmeticOpSymbol(binary.getOperator());
        if (opSym == null) return;

        String bigint = toBigintStr(binary);
        if (bigint == null) return;

        emitBigintBoundsRaw(emitted, bigint);
    }

    /**
     * For {@code a / b} or {@code a % b}, emit {@code b != 0} when {@code b} is
     * pre-state-expressible (parameter, field, literal). Without this, OpenJML
     * raises {@code PossiblyDivideByZero} on every integer division.
     */
    private void handleDivisionByZero(BinaryExpr binary, Set<String> emitted) {
        BinaryExpr.Operator op = binary.getOperator();
        if (op != BinaryExpr.Operator.DIVIDE && op != BinaryExpr.Operator.REMAINDER) return;
        String rhs = toIntStr(binary.getRight());
        if (rhs == null) return;
        emitted.add(rhs + " != 0");
    }

    private void emitBigintBoundsRaw(Set<String> emitted, String bigintExpr) {
        emitted.add(bigintExpr + " >= Integer.MIN_VALUE");
        emitted.add(bigintExpr + " <= Integer.MAX_VALUE");
    }

    // ---------------------------------------------------------------------
    // Expression string-builders
    // ---------------------------------------------------------------------

    /**
     * Returns the expression rewritten so every arithmetic operation runs in
     * {@code \bigint}, or {@code null} if the expression references something
     * not expressible in the pre-state (loop vars, non-substitutable locals).
     *
     * <p>Crucial invariant: the {@code (\bigint)} cast is applied to every
     * arithmetic leaf (parameter, field, array element, literal) — never to a
     * compound sub-expression. Applying the cast to a compound like {@code
     * (x2 - x1)} would leave the inner subtraction in int, which under {@code
     * --spec-math=safe} becomes another overflow proof obligation.</p>
     */
    private String toBigintStr(Expression e) {
        if (e instanceof EnclosedExpr enc) return toBigintStr(enc.getInner());

        if (e instanceof BinaryExpr be) {
            String op = composableBinaryOpSymbol(be.getOperator());
            if (op == null) return null;
            String left = toBigintStr(be.getLeft());
            String right = toBigintStr(be.getRight());
            if (left == null || right == null) return null;
            return "(" + left + " " + op + " " + right + ")";
        }

        if (e instanceof UnaryExpr ue && ue.getOperator() == UnaryExpr.Operator.MINUS) {
            String inner = toBigintStr(ue.getExpression());
            return inner == null ? null : "(-" + inner + ")";
        }

        // NameExpr: recurse into local initialisers so the bigint cast distributes
        // over operands rather than wrapping the compound (which would leak int
        // arithmetic into a spec-math=safe context). Skip non-integer types —
        // OpenJML rejects (\bigint) casts of double, float, String, etc.
        if (e instanceof NameExpr ne) {
            String name = ne.getNameAsString();
            if (loopVars.contains(name)) return null;
            if (intParamNames.contains(name)) return "(\\bigint) " + name;
            if (intFieldNames.contains(name)) return "(\\bigint) this." + name;
            if (localInits.containsKey(name)) return toBigintStr(localInits.get(name));
            return null;
        }

        if (e instanceof FieldAccessExpr fae) {
            String scope = fae.getScope().toString();
            if (scope.equals("this") && intFieldNames.contains(fae.getNameAsString())) {
                return "(\\bigint) this." + fae.getNameAsString();
            }
            if (fae.getNameAsString().equals("length")) {
                // arr.length is int-typed
                String scopeStr = toIntStr(fae.getScope());
                return scopeStr == null ? null : "(\\bigint) " + scopeStr + ".length";
            }
            return null;
        }

        if (e instanceof ArrayAccessExpr aae) {
            String base = getIntArrayBaseName(aae);
            if (base == null) return null;
            String idx = toIntStr(aae.getIndex());
            if (idx == null) return null;
            return "(\\bigint) " + base + "[" + idx + "]";
        }

        if (e instanceof IntegerLiteralExpr || e instanceof LongLiteralExpr
                || e instanceof CharLiteralExpr) {
            return "(\\bigint) " + e.toString();
        }

        return null;
    }

    /**
     * Returns a syntactic int-form string for an expression whose every leaf is
     * expressible in the pre-state, or {@code null} if any leaf is a loop
     * variable or a non-substitutable local. Locals assigned from a pre-state
     * expression are substituted.
     */
    private String toIntStr(Expression e) {
        if (e instanceof EnclosedExpr enc) {
            String inner = toIntStr(enc.getInner());
            return inner == null ? null : "(" + inner + ")";
        }

        if (e instanceof IntegerLiteralExpr || e instanceof LongLiteralExpr
                || e instanceof CharLiteralExpr) {
            return e.toString();
        }

        if (e instanceof NameExpr ne) {
            String name = ne.getNameAsString();
            if (loopVars.contains(name)) return null;
            if (intParamNames.contains(name)) return name;
            if (intFieldNames.contains(name)) return "this." + name;
            if (localInits.containsKey(name)) {
                return toIntStr(localInits.get(name));
            }
            return null;
        }

        if (e instanceof FieldAccessExpr fae) {
            String scope = fae.getScope().toString();
            if (scope.equals("this") && intFieldNames.contains(fae.getNameAsString())) {
                return "this." + fae.getNameAsString();
            }
            // arr.length — result is int; scope must be an array reference
            if (fae.getNameAsString().equals("length")) {
                String scopeStr = arrayScopeRefStr(fae.getScope());
                return scopeStr == null ? null : scopeStr + ".length";
            }
            return null;
        }

        if (e instanceof ArrayAccessExpr aae) {
            String base = getIntArrayBaseName(aae);
            if (base == null) return null;
            String idx = toIntStr(aae.getIndex());
            if (idx == null) return null;
            return base + "[" + idx + "]";
        }

        if (e instanceof UnaryExpr ue && ue.getOperator() == UnaryExpr.Operator.MINUS) {
            String inner = toIntStr(ue.getExpression());
            return inner == null ? null : "(-" + inner + ")";
        }

        if (e instanceof BinaryExpr be) {
            String op = composableBinaryOpSymbol(be.getOperator());
            if (op == null) return null;
            String left = toIntStr(be.getLeft());
            String right = toIntStr(be.getRight());
            if (left == null || right == null) return null;
            return "(" + left + " " + op + " " + right + ")";
        }

        return null;
    }

    // ---------------------------------------------------------------------
    // Helpers
    // ---------------------------------------------------------------------

    private String resolveFieldRef(Expression expr) {
        if (expr instanceof FieldAccessExpr fae) {
            if (fae.getScope().toString().equals("this")
                    && intFieldNames.contains(fae.getNameAsString())) {
                return "this." + fae.getNameAsString();
            }
        } else if (expr instanceof NameExpr ne) {
            if (intFieldNames.contains(ne.getNameAsString())) {
                return "this." + ne.getNameAsString();
            }
        }
        return null;
    }

    private String getIntArrayBaseName(ArrayAccessExpr aae) {
        Expression name = aae.getName();
        if (name instanceof ArrayAccessExpr inner) {
            return getIntArrayBaseName(inner);
        }
        if (name instanceof FieldAccessExpr fa) {
            if (fa.getScope().toString().equals("this")
                    && intArrayFieldNames.contains(fa.getNameAsString())) {
                return "this." + fa.getNameAsString();
            }
            return null;
        }
        if (name instanceof NameExpr ne) {
            String varName = ne.getNameAsString();
            if (intArrayParamNames.contains(varName)) return varName;
            if (intArrayFieldNames.contains(varName)) return "this." + varName;
        }
        return null;
    }

    /**
     * Returns a pre-state reference string for an array-typed scope (used for
     * {@code arr.length}). Any array parameter or field qualifies — element type
     * doesn't matter for {@code .length}.
     */
    private String arrayScopeRefStr(Expression scope) {
        if (scope instanceof NameExpr ne) {
            String name = ne.getNameAsString();
            if (loopVars.contains(name)) return null;
            if (paramNames.contains(name) && isArrayParam(name)) return name;
            if (fieldNames.contains(name) && isArrayField(name)) return "this." + name;
        }
        if (scope instanceof FieldAccessExpr fae) {
            if (fae.getScope().toString().equals("this")
                    && fieldNames.contains(fae.getNameAsString())
                    && isArrayField(fae.getNameAsString())) {
                return "this." + fae.getNameAsString();
            }
        }
        return null;
    }

    private boolean isArrayParam(String name) {
        return methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(name)
                        && p.getType().asString().contains("["));
    }

    private boolean isArrayField(String name) {
        return methodDecl.findAncestor(ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .anyMatch(f -> f.getVariables().stream()
                                .anyMatch(v -> v.getNameAsString().equals(name)
                                        && v.getType().asString().contains("["))))
                .orElse(false);
    }

    private static boolean isIntegerPrimitive(String typeName) {
        return INTEGER_TYPE_NAMES.contains(typeName);
    }

    private static boolean isIntegerArrayType(String typeName) {
        if (!typeName.endsWith("[]")) return false;
        String elem = typeName.substring(0, typeName.length() - 2).trim();
        return INTEGER_TYPE_NAMES.contains(elem);
    }

    private Set<String> getEnclosingClassFieldsOfPredicate(MethodDeclaration md,
                                                            java.util.function.Predicate<String> typeTest) {
        return md.findAncestor(ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .flatMap(f -> {
                            String typeStr = f.getCommonType().asString();
                            return f.getVariables().stream()
                                    .filter(v -> typeTest.test(typeStr))
                                    .map(VariableDeclarator::getNameAsString);
                        })
                        .collect(Collectors.toSet()))
                .orElseGet(HashSet::new);
    }

    private String compoundOpSymbol(AssignExpr.Operator op) {
        return switch (op) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            default -> null;
        };
    }

    /**
     * Operators for which the analyzer emits standalone overflow bounds.
     * Division is excluded because bigint division reproduces int semantics
     * except for the {@code MIN_VALUE / -1} case, which is rare and narrow.
     */
    private String binaryArithmeticOpSymbol(BinaryExpr.Operator op) {
        return switch (op) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            default -> null;
        };
    }

    /**
     * Operators that compose inside a larger bigint expression. Includes
     * division and remainder so outer arithmetic can still be rewritten when
     * a sub-expression divides.
     */
    private String composableBinaryOpSymbol(BinaryExpr.Operator op) {
        return switch (op) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            case DIVIDE -> "/";
            case REMAINDER -> "%";
            default -> null;
        };
    }

    private Map<String, Expression> collectLocalInitializers(ASTCollector collector) {
        Map<String, Expression> map = new HashMap<>();
        for (VariableDeclarationExpr vde : collector.varDeclExprs) {
            for (VariableDeclarator v : vde.getVariables()) {
                v.getInitializer().ifPresent(init -> map.put(v.getNameAsString(), init));
            }
        }
        return map;
    }

    private Set<String> collectLoopVariables(MethodDeclaration methodDecl) {
        Set<String> vars = new HashSet<>();
        methodDecl.findAll(ForStmt.class).forEach(fs -> {
            fs.getInitialization().forEach(init -> {
                if (init instanceof VariableDeclarationExpr vde) {
                    vde.getVariables().forEach(v -> vars.add(v.getNameAsString()));
                }
            });
            // Also track accumulators mutated inside the for-loop body so the overflow
            // analyzer doesn't emit `accum-from-init < MAX_VALUE` preconditions that
            // collapse to trivialities like `0 < Integer.MAX_VALUE`.
            fs.getBody().findAll(UnaryExpr.class).forEach(u -> {
                if ((u.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT)
                        && u.getExpression() instanceof NameExpr ne) {
                    vars.add(ne.getNameAsString());
                }
            });
            fs.getBody().findAll(AssignExpr.class).forEach(a -> {
                if (a.getTarget() instanceof NameExpr ne) {
                    vars.add(ne.getNameAsString());
                }
            });
        });
        methodDecl.findAll(ForEachStmt.class).forEach(fes ->
                vars.add(fes.getVariable().getVariable(0).getNameAsString()));
        methodDecl.findAll(WhileStmt.class).forEach(ws -> {
            ws.findAll(VariableDeclarationExpr.class).forEach(vde ->
                    vde.getVariables().forEach(v -> vars.add(v.getNameAsString())));
            // Also track locals mutated inside the while body — they serve as counters
            // even when declared outside the loop: `int i = 0; while (i < n) i++;`.
            ws.getBody().findAll(UnaryExpr.class).forEach(u -> {
                if ((u.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT)
                        && u.getExpression() instanceof NameExpr ne) {
                    vars.add(ne.getNameAsString());
                }
            });
            ws.getBody().findAll(AssignExpr.class).forEach(a -> {
                if (a.getTarget() instanceof NameExpr ne) {
                    vars.add(ne.getNameAsString());
                }
            });
        });
        methodDecl.findAll(DoStmt.class).forEach(ds -> {
            ds.getBody().findAll(UnaryExpr.class).forEach(u -> {
                if ((u.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT
                        || u.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT)
                        && u.getExpression() instanceof NameExpr ne) {
                    vars.add(ne.getNameAsString());
                }
            });
        });
        return vars;
    }

    private Set<String> getEnclosingClassFieldNames(MethodDeclaration methodDecl) {
        return methodDecl.findAncestor(ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .map(v -> v.getNameAsString())
                        .collect(Collectors.toSet()))
                .orElseGet(HashSet::new);
    }
}
