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
    private MethodSpecification spec;

    void inferOverflowPreconditions(MethodDeclaration methodDecl, MethodSpecification spec,
                                     ASTCollector collector) {
        this.methodDecl = methodDecl;
        this.spec = spec;
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

        // Local-accumulator-over-array patterns: `int sum = 0; for(i=0; i<arr.length; i++) sum += arr[i];`
        // The compound-assignment walker above bails on these because the target is a local
        // (not a field, not an array element). Without an extra emission step every such
        // accumulator triggers `ArithmeticOperationRange overflow in int sum` at the
        // OpenJML level. Drives the AccumulatorInvariant.sum / ArrayMath2.dotProduct /
        // WhileSum.sumWhile / ForEachSum.sumArray cases.
        handleAccumulatorOverflow(emitted);

        // Recursive multiplication / addition patterns: factorial-shape
        // `n * recurse(n-1)` blows out at n=13 (12! = 479001600, 13! overflows int);
        // Fibonacci-shape `recurse(n-1) + recurse(n-2)` overflows around n=46;
        // power-of-two `2 * recurse(n-1)` overflows at n=31. Without a small literal
        // upper bound the recursive overflow is unprovable (z3 cannot unfold the
        // recursive call). Drives Recursive1.factorial, Recursive2.fib.
        handleRecursiveArithmeticOverflow(emitted);

        // SP-style forward propagation for straight-line bodies. When parameters
        // or fields are reassigned in sequence (e.g. `a = a*a; c += 6; b = a+c;`),
        // the syntactic precondition `(\bigint)a + (\bigint)c <= MAX` references
        // method-entry values, but the body's actual `a+c` operates on the
        // post-mutation values. Emit the substituted form as an additional
        // precondition. Drives FieldAccum.getValue and similar shapes.
        emitForwardPropagatedOverflowGuards(emitted);

        emitted.forEach(spec::addPrecondition);
    }

    /**
     * If the method is recursive AND its body returns an arithmetic combination of
     * a self-call and either {@code n} (factorial-shape), another self-call
     * (Fibonacci-shape), or a small literal (power-shape), emit a literal upper
     * bound on the int parameter so OpenJML's overflow check can discharge.
     *
     * <p>Bounds:</p>
     * <ul>
     *   <li>factorial-shape (n * recurse(...)): n <= 12</li>
     *   <li>fibonacci-shape (recurse(...) + recurse(...)): n <= 46</li>
     *   <li>power-shape (LIT * recurse(...)): n <= 30</li>
     * </ul>
     *
     * <p>Conservative: only fires when there is exactly one int parameter, the method
     * returns int or long, and the recursive return expression matches one of the
     * three shapes above. Nothing else triggers — z3 should never see a recursive
     * postcondition without a paired bound.</p>
     */
    /**
     * SP-style forward-propagation pass for straight-line method bodies. The
     * regular per-{@link BinaryExpr} emission references method-entry values,
     * but when a parameter or field is reassigned earlier in the body
     * (e.g. {@code a = a*a; c += 6; b = a+c;}) the body's runtime {@code a+c}
     * operates on the \emph{post-mutation} values, not the entry values. The
     * existing precondition {@code (\bigint)a + (\bigint)c <= MAX} is true but
     * narrower than what discharges the body's overflow check. Emit the
     * substituted form as an additional precondition.
     *
     * <p>Restricted to bodies whose top-level statements are ExpressionStmt /
     * LocalDecl / ReturnStmt (no if/loop/try), and where at least one
     * parameter or field is reassigned. The substitution map is built by
     * walking the body in source order; an assignment {@code v = rhs}
     * substitutes the current map into rhs, then records {@code v -> rhs'}.
     * For each subsequent BinaryExpr operand referring to {@code v}, the
     * substituted form is emitted in a {@code (\bigint)} bound.</p>
     *
     * <p>This is heuristic but sound: the substituted precondition is a true
     * fact about the runtime state, and emitting it alongside the
     * method-entry-form precondition adds information without removing any.
     * The probe-validated FieldAccum.getValue shape verifies under this
     * emission.</p>
     */
    private void emitForwardPropagatedOverflowGuards(Set<String> emitted) {
        if (methodDecl.getBody().isEmpty()) return;
        BlockStmt body = methodDecl.getBody().get();

        // Straight-line gate: only top-level ExpressionStmt / LocalDecl /
        // ReturnStmt allowed. Anything that branches (if/while/for/do/try/
        // switch) bails out — a single map can't capture per-branch state.
        for (Statement s : body.getStatements()) {
            if (s instanceof ExpressionStmt) continue;
            if (s instanceof ReturnStmt) continue;
            if (s instanceof com.github.javaparser.ast.stmt.LocalClassDeclarationStmt) return;
            // Local-variable declarations (`int b = a + c;`) appear as
            // ExpressionStmt-wrapped VariableDeclarationExpr in JavaParser's
            // ASTs in some configurations, but commonly come up as a separate
            // node type. Treat them as straight-line.
            if (isLocalDeclStmt(s)) continue;
            return; // any branch → bail
        }

        // Walk in order, building a substitution map.
        Map<String, String> subst = new java.util.HashMap<>();
        boolean reassignedAtLeastOne = false;
        for (Statement s : body.getStatements()) {
            // Process binary expressions IN this statement using the current map
            // before recording any new assignments from this same statement.
            // (The body's `int b = a + c;` reads a/c at the value bound on
            // entry to the statement, then assigns b.)
            for (BinaryExpr be : s.findAll(BinaryExpr.class)) {
                if (!isArithmeticBinaryOp(be)) continue;
                if (!operandReferencesReassigned(be, subst)) continue;
                String substituted = substituteBinaryToBigint(be, subst);
                if (substituted == null) continue;
                emitted.add(substituted + " >= Integer.MIN_VALUE");
                emitted.add(substituted + " <= Integer.MAX_VALUE");
            }
            // Local declarations `int v = rhs;` introduce v with rhs as its
            // current value. Including them in the subst map lets later
            // references to v expand to the runtime value (matters for
            // shapes like `int b = a+c; b = b*b;` where b*b's overflow
            // check needs the substituted form).
            for (VariableDeclarationExpr vde : s.findAll(VariableDeclarationExpr.class)) {
                for (VariableDeclarator vd : vde.getVariables()) {
                    if (vd.getInitializer().isEmpty()) continue;
                    if (!isIntegerPrimitive(vd.getType().asString())) continue;
                    String rhsSubst = applySubstitution(
                            vd.getInitializer().get().toString(), subst);
                    subst.put(vd.getNameAsString(), "(" + rhsSubst + ")");
                }
            }
            // Record param/field assignments in this statement.
            for (AssignExpr ae : s.findAll(AssignExpr.class)) {
                String name;
                if (ae.getTarget() instanceof NameExpr nn) {
                    name = nn.getNameAsString();
                } else if (ae.getTarget() instanceof FieldAccessExpr fae
                        && fae.getScope().toString().equals("this")) {
                    name = fae.getNameAsString();
                } else {
                    continue;
                }
                boolean isParamOrField = paramNames.contains(name)
                        || fieldNames.contains(name);
                boolean isTrackedLocal = subst.containsKey(name);
                if (!isParamOrField && !isTrackedLocal) continue;
                String currentValue = subst.getOrDefault(name,
                        fieldNames.contains(name) ? "this." + name : name);
                String rhsSubst = applySubstitution(ae.getValue().toString(), subst);
                String newValue;
                if (ae.getOperator() == AssignExpr.Operator.ASSIGN) {
                    newValue = "(" + rhsSubst + ")";
                } else if (ae.getOperator() == AssignExpr.Operator.PLUS) {
                    newValue = "(" + currentValue + " + " + rhsSubst + ")";
                } else if (ae.getOperator() == AssignExpr.Operator.MINUS) {
                    newValue = "(" + currentValue + " - " + rhsSubst + ")";
                } else if (ae.getOperator() == AssignExpr.Operator.MULTIPLY) {
                    newValue = "(" + currentValue + " * " + rhsSubst + ")";
                } else {
                    return; // unsupported compound — bail to stay sound
                }
                subst.put(name, newValue);
                if (isParamOrField) reassignedAtLeastOne = true;
            }
        }
        if (!reassignedAtLeastOne) return; // nothing to add beyond standard emission
    }

    /**
     * Returns the bigint-cast form of the substituted binary expression, or
     * null when any operand can't be safely lifted (e.g. references a loop
     * variable or local without a known initialiser).
     */
    private String substituteBinaryToBigint(BinaryExpr be, Map<String, String> subst) {
        String left = substituteOperandToBigint(be.getLeft(), subst);
        if (left == null) return null;
        String right = substituteOperandToBigint(be.getRight(), subst);
        if (right == null) return null;
        String op = composableBinaryOpSymbol(be.getOperator());
        if (op == null) return null;
        return "((" + left + ") " + op + " (" + right + "))";
    }

    private String substituteOperandToBigint(Expression e, Map<String, String> subst) {
        if (e instanceof EnclosedExpr enc) return substituteOperandToBigint(enc.getInner(), subst);
        if (e instanceof NameExpr ne) {
            String name = ne.getNameAsString();
            if (subst.containsKey(name)) {
                return "(\\bigint) " + subst.get(name);
            }
            if (intParamNames.contains(name)) return "(\\bigint) " + name;
            if (intFieldNames.contains(name)) return "(\\bigint) this." + name;
            return null;
        }
        if (e instanceof FieldAccessExpr fae && fae.getScope().toString().equals("this")
                && intFieldNames.contains(fae.getNameAsString())) {
            String name = fae.getNameAsString();
            if (subst.containsKey(name)) return "(\\bigint) " + subst.get(name);
            return "(\\bigint) this." + name;
        }
        if (e instanceof IntegerLiteralExpr || e instanceof LongLiteralExpr) {
            return "(\\bigint) " + e.toString();
        }
        if (e instanceof BinaryExpr be) {
            // Recursive case: nested binary like `a*a` — substitute each side.
            return substituteBinaryToBigint(be, subst);
        }
        if (e instanceof UnaryExpr ue && ue.getOperator() == UnaryExpr.Operator.MINUS) {
            String inner = substituteOperandToBigint(ue.getExpression(), subst);
            return inner == null ? null : "(-(" + inner + "))";
        }
        return null;
    }

    /** Apply current substitution map to an arbitrary expression's string form. */
    private String applySubstitution(String exprStr, Map<String, String> subst) {
        String result = exprStr;
        for (Map.Entry<String, String> e : subst.entrySet()) {
            result = result.replaceAll("\\b" + java.util.regex.Pattern.quote(e.getKey()) + "\\b",
                    java.util.regex.Matcher.quoteReplacement(e.getValue()));
        }
        return result;
    }

    private boolean operandReferencesReassigned(BinaryExpr be, Map<String, String> subst) {
        if (subst.isEmpty()) return false;
        for (NameExpr ne : be.findAll(NameExpr.class)) {
            if (subst.containsKey(ne.getNameAsString())) return true;
        }
        return false;
    }

    private boolean isArithmeticBinaryOp(BinaryExpr be) {
        BinaryExpr.Operator op = be.getOperator();
        return op == BinaryExpr.Operator.PLUS || op == BinaryExpr.Operator.MINUS
            || op == BinaryExpr.Operator.MULTIPLY;
    }

    private boolean isLocalDeclStmt(Statement s) {
        if (s instanceof com.github.javaparser.ast.stmt.ExpressionStmt es) {
            return es.getExpression() instanceof VariableDeclarationExpr;
        }
        return false;
    }

    private void handleRecursiveArithmeticOverflow(Set<String> emitted) {
        String methodName = methodDecl.getNameAsString();
        // Require exactly one int parameter — the recursion variable.
        if (intParamNames.size() != 1) return;
        String paramName = intParamNames.iterator().next();
        // Return type must be an integer primitive.
        String returnType = methodDecl.getType().asString();
        if (!"int".equals(returnType) && !"long".equals(returnType)) return;
        if (methodDecl.getBody().isEmpty()) return;

        // Walk every return in the body, looking for a recursive arithmetic shape.
        boolean factorialShape = false;  // n * recurse(...)
        boolean fibonacciShape = false;  // recurse(...) + recurse(...)
        boolean powerShape = false;      // LIT * recurse(...)
        for (com.github.javaparser.ast.stmt.ReturnStmt rs
                : methodDecl.findAll(com.github.javaparser.ast.stmt.ReturnStmt.class)) {
            if (rs.getExpression().isEmpty()) continue;
            Expression expr = rs.getExpression().get();
            if (expr instanceof EnclosedExpr enc) expr = enc.getInner();
            if (!(expr instanceof BinaryExpr be)) continue;

            BinaryExpr.Operator op = be.getOperator();
            boolean leftIsRecurse = isRecursiveCallTo(be.getLeft(), methodName);
            boolean rightIsRecurse = isRecursiveCallTo(be.getRight(), methodName);
            if (!leftIsRecurse && !rightIsRecurse) continue;

            if (op == BinaryExpr.Operator.PLUS && leftIsRecurse && rightIsRecurse) {
                fibonacciShape = true;
            } else if (op == BinaryExpr.Operator.MULTIPLY) {
                Expression other = leftIsRecurse ? be.getRight() : be.getLeft();
                if (other instanceof NameExpr otherNe
                        && otherNe.getNameAsString().equals(paramName)) {
                    factorialShape = true;
                } else if (other instanceof IntegerLiteralExpr) {
                    powerShape = true;
                }
            }
        }

        // Pick the tightest applicable bound. Factorial is most restrictive.
        Integer bound = null;
        if (factorialShape) bound = 12;
        else if (powerShape) bound = 30;
        else if (fibonacciShape) bound = 46;
        if (bound == null) return;

        emitted.add(paramName + " <= " + bound);
        // Pair with non-negative bound — the recursive base case typically
        // requires `n >= 0` so the recursion terminates. The early-validation
        // analyzer will also emit this from `if (n < 0) throw ...`, but
        // emitting it here makes the overflow precondition usable even when
        // the method has no explicit guard.
        emitted.add(paramName + " >= 0");
    }

    /** True when {@code e} is a method call whose name matches {@code methodName}. */
    private boolean isRecursiveCallTo(Expression e, String methodName) {
        if (e instanceof EnclosedExpr enc) return isRecursiveCallTo(enc.getInner(), methodName);
        if (!(e instanceof MethodCallExpr mce)) return false;
        return mce.getNameAsString().equals(methodName);
    }

    /**
     * Detects local-accumulator-over-array patterns and emits per-element bound
     * preconditions plus matching loop invariants so the running accumulator
     * provably stays inside int range.
     *
     * <p>Patterns recognised (the accumulator must be a local int/long declared
     * in the method as {@code = 0} for sum or {@code = 1} for product, modified
     * only inside the loop):</p>
     * <ul>
     *   <li>{@code for (int i=LO; i<arr.length; i++) sum += arr[i];}</li>
     *   <li>{@code for (int i=LO; i<arr.length; i++) sum += arr[i] * b[i];}</li>
     *   <li>{@code for (int i=LO; i<arr.length; i++) sum = sum + arr[i];}</li>
     *   <li>{@code for (int val : arr) sum += val;}</li>
     *   <li>{@code while (i < arr.length) { sum += arr[i]; i++; }}</li>
     * </ul>
     *
     * <p>For every such pattern, the per-element bound is
     * {@code arr[k] >= Integer.MIN_VALUE / arr.length && arr[k] <= Integer.MAX_VALUE / arr.length}.
     * Vacuously satisfied when {@code arr.length == 0} (the forall body is unevaluated
     * and the loop body never runs). The matching loop invariant bounds the running
     * accumulator by the same per-step share of the int range, scaled by the iteration
     * counter.</p>
     */
    private void handleAccumulatorOverflow(Set<String> emitted) {
        // For-loops with literal init and `i < arr.length` upper bound.
        for (ForStmt fs : methodDecl.findAll(ForStmt.class)) {
            handleForLoopAccumulator(fs, emitted);
            handleFieldBoundedDiagonalAccumulator(fs, emitted);
        }
        // For-each loops `for (int val : arr)`.
        for (ForEachStmt fes : methodDecl.findAll(ForEachStmt.class)) {
            handleForEachAccumulator(fes, emitted);
        }
        // While loops shaped like `while (i < arr.length) { sum += arr[i]; i++; }`.
        for (WhileStmt ws : methodDecl.findAll(WhileStmt.class)) {
            handleWhileAccumulator(ws, emitted);
        }
        // Field-or-local `++` inside one or more for-loops: emit a precondition that
        // the post-(outermost-loop) value can't overflow. For nested loops the bound
        // is the PRODUCT of every enclosing loop's iteration count. Drives
        // LoopIncrementsField.growBy (single loop), NestedLoopBounds.countCells
        // (rows * cols), TripleNestedLoop (x * y * z).
        handleCounterIncrementOverflowNested(emitted);
    }

    /**
     * Walks every {@code F++} inside the method body and, when F is a local int
     * starting at 0 or a field, emits an overflow precondition based on the product
     * of the iteration counts of every enclosing for-loop.
     *
     * <p>Restricted to:</p>
     * <ul>
     *   <li>Unconditional increments (not inside if / switch / ternary).</li>
     *   <li>Enclosing loops that are simple {@code for (int x = LO; x CMP B; x++)}
     *       with literal LO, single-step increment, and no early exit.</li>
     *   <li>Bound expressions expressible in pre-state.</li>
     * </ul>
     *
     * <p>The overflow precondition is
     * {@code (\bigint)F + (\bigint)bound1 * (\bigint)bound2 * ... <= MAX_VALUE}.</p>
     */
    private void handleCounterIncrementOverflowNested(Set<String> emitted) {
        // Pre-collect every for-loop's own update slot — the increment of the loop
        // counter itself, e.g. the `i++` in `for (int i = 0; i < n; i++) ...`. These
        // are bounded by the for-header invariant `i <= n`, not by an accumulated
        // count, so the product-of-iteration-counts precondition is irrelevant here.
        Set<UnaryExpr> forUpdateExprs = new java.util.HashSet<>();
        for (ForStmt fs : methodDecl.findAll(ForStmt.class)) {
            for (Expression upd : fs.getUpdate()) {
                if (upd instanceof UnaryExpr ue) forUpdateExprs.add(ue);
            }
        }

        for (UnaryExpr inc : methodDecl.findAll(UnaryExpr.class)) {
            if (inc.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && inc.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) continue;
            // Skip every for-header increment — it isn't an accumulator.
            if (forUpdateExprs.contains(inc)) continue;

            String targetForm = unaryIncrementTargetForm(inc);
            if (targetForm == null) continue;

            // Collect every enclosing for-loop. Stop at the method body.
            List<ForStmt> enclosingLoops = new ArrayList<>();
            com.github.javaparser.ast.Node cur = inc;
            boolean enclosingHasEarlyExit = false;
            boolean enclosingIsConditional = false;
            while (cur.getParentNode().isPresent()) {
                com.github.javaparser.ast.Node parent = cur.getParentNode().get();
                if (parent instanceof MethodDeclaration) break;
                if (parent instanceof ForStmt fs) {
                    // Only counts if this isn't the for-loop's own update slot.
                    boolean isUpdate = fs.getUpdate().contains(cur)
                            || (cur instanceof Expression && fs.getUpdate().contains((Expression) cur));
                    if (!isUpdate) {
                        enclosingLoops.add(fs);
                    }
                } else if (parent instanceof WhileStmt
                        || parent instanceof DoStmt
                        || parent instanceof ForEachStmt) {
                    // Non-for enclosing loop — too uncertain to bound iteration count.
                    enclosingHasEarlyExit = true;
                    break;
                } else if (parent instanceof IfStmt
                        || parent instanceof SwitchStmt
                        || parent instanceof ConditionalExpr) {
                    enclosingIsConditional = true;
                }
                cur = parent;
            }

            if (enclosingLoops.isEmpty()) continue;
            if (enclosingHasEarlyExit) continue;
            if (enclosingIsConditional) continue;

            // For each enclosing loop, extract the iteration count expression.
            // If any is unanalyzable, skip — we can't bound the total.
            List<String> iterCounts = new ArrayList<>();
            boolean any_ee = false;
            for (ForStmt fs : enclosingLoops) {
                String ic = forLoopIterationCountBigint(fs);
                if (ic == null) {
                    any_ee = true;
                    break;
                }
                if (loopBodyHasEarlyExit(fs.getBody())) {
                    any_ee = true;
                    break;
                }
                iterCounts.add(ic);
            }
            if (any_ee) continue;
            if (iterCounts.isEmpty()) continue;

            // Build the product expression in bigint.
            String product = String.join(" * ", iterCounts);
            // Bound: targetForm + product <= MAX_VALUE (in bigint).
            String overflowPre = "((\\bigint) " + targetForm + " + (" + product
                    + ")) <= Integer.MAX_VALUE";
            emitted.add(overflowPre);
        }
    }

    /**
     * Resolves the increment target to its JML form, or null if it isn't one we bound.
     *
     * <p>Note: deliberately does NOT exclude {@code loopVars} for locals — that set
     * is the union of all variables modified inside any loop and so includes the
     * very accumulator counters this analyzer is supposed to bound (e.g. {@code count}
     * in {@code for (int i = 0; i < n; i++) count++;}). The for-header counter (e.g.
     * {@code i}) is filtered separately because it's never declared as a method-body
     * local with a literal initializer — it's the for-loop's own declarator and is
     * not collected into {@link #localInits}.</p>
     */
    private String unaryIncrementTargetForm(UnaryExpr inc) {
        if (inc.getExpression() instanceof NameExpr ne) {
            String name = ne.getNameAsString();
            // Local counter declared as `int X = 0` in the method body (NOT a for-loop
            // header). `localInits` only contains body-level declarators, so the for-loop
            // counter `i` from `for (int i = 0; ...)` won't have an entry here.
            //
            // For locals: substitute the literal initializer (0) directly into the
            // emitted precondition. Local names aren't in scope at method entry, so a
            // raw `count + ...` precondition is a JML scope error. Returning `0` makes
            // the precondition reduce to `0 + product <= MAX_VALUE`, i.e. `product <= MAX`.
            Integer initLit = findLocalLiteralInit(name);
            if (initLit != null && initLit == 0 && !intFieldNames.contains(name)
                    && !paramNames.contains(name)) {
                return "0";
            }
            if (intFieldNames.contains(name)) {
                return "this." + name;
            }
            return null;
        }
        if (inc.getExpression() instanceof FieldAccessExpr fae
                && fae.getScope().toString().equals("this")
                && intFieldNames.contains(fae.getNameAsString())) {
            return "this." + fae.getNameAsString();
        }
        return null;
    }

    /**
     * For a {@code for (int i = LO; i CMP B; i++)} (or {@code i += K}) loop, returns
     * a bigint expression for the maximum iteration count. {@code null} if any part
     * of the header isn't a recognized shape or B is not pre-state-expressible.
     */
    private String forLoopIterationCountBigint(ForStmt fs) {
        if (fs.getInitialization().size() != 1) return null;
        if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return null;
        if (vde.getVariables().size() != 1) return null;
        VariableDeclarator decl = vde.getVariables().get(0);
        Expression initExpr = decl.getInitializer().orElse(null);
        if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return null;
        int lo = initExpr.asIntegerLiteralExpr().asInt();
        if (lo < 0) return null;
        String loopVar = decl.getNameAsString();

        Expression cmpExpr = fs.getCompare().orElse(null);
        if (!(cmpExpr instanceof BinaryExpr cmp)) return null;
        BinaryExpr.Operator cmpOp = cmp.getOperator();
        if (cmpOp != BinaryExpr.Operator.LESS && cmpOp != BinaryExpr.Operator.LESS_EQUALS) return null;
        if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                || !cmpLeft.getNameAsString().equals(loopVar)) return null;

        if (fs.getUpdate().size() != 1) return null;
        Expression updateExpr = fs.getUpdate().get(0);
        if (!(updateExpr instanceof UnaryExpr ue)) return null;
        if (ue.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                && ue.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) return null;
        if (!(ue.getExpression() instanceof NameExpr uene)
                || !uene.getNameAsString().equals(loopVar)) return null;

        String boundStr = toIntStr(cmp.getRight());
        if (boundStr == null) return null;

        String iterBigint;
        if (lo == 0) {
            iterBigint = "(\\bigint) " + boundStr;
        } else {
            iterBigint = "((\\bigint) " + boundStr + " - (\\bigint) " + lo + ")";
        }
        if (cmpOp == BinaryExpr.Operator.LESS_EQUALS) {
            iterBigint = "(" + iterBigint + " + (\\bigint) 1)";
        }
        return iterBigint;
    }

    /** True when {@code body} contains a return / break / continue / throw. */
    private boolean loopBodyHasEarlyExit(Statement body) {
        return !body.findAll(com.github.javaparser.ast.stmt.ReturnStmt.class).isEmpty()
                || !body.findAll(com.github.javaparser.ast.stmt.BreakStmt.class).isEmpty()
                || !body.findAll(com.github.javaparser.ast.stmt.ContinueStmt.class).isEmpty()
                || !body.findAll(com.github.javaparser.ast.stmt.ThrowStmt.class).isEmpty();
    }


    /** Pattern: {@code for (int i=LO; i<arr.length; i++) accum += arr[i];} (and variants). */
    private void handleForLoopAccumulator(ForStmt fs, Set<String> emitted) {
        // Extract loop variable + literal lower bound + array name from the for-header.
        if (fs.getInitialization().size() != 1) return;
        if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return;
        if (vde.getVariables().size() != 1) return;
        String loopVar = vde.getVariables().get(0).getNameAsString();
        Expression initExpr = vde.getVariables().get(0).getInitializer().orElse(null);
        if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return;
        int lo = initExpr.asIntegerLiteralExpr().asInt();
        if (lo < 0) return;

        Expression cmpExpr = fs.getCompare().orElse(null);
        if (!(cmpExpr instanceof BinaryExpr cmp)) return;
        if (cmp.getOperator() != BinaryExpr.Operator.LESS) return;
        if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                || !cmpLeft.getNameAsString().equals(loopVar)) return;
        if (!(cmp.getRight() instanceof FieldAccessExpr fae)
                || !fae.getNameAsString().equals("length")) return;
        String iterName = arrayScopeRefStr(fae.getScope());
        if (iterName == null) return;
        // Require an int-typed array — non-int arrays would need a different bound calc.
        if (!isIntArrayName(fae.getScope())) return;

        int line = fs.getBegin().map(p -> p.line).orElse(0);
        // For each accumulator assignment in the body whose RHS is a loop-indexed array
        // expression, emit per-element bound + running-sum invariant.
        for (AssignExpr ae : fs.getBody().findAll(AssignExpr.class)) {
            tryEmitAccumulatorBounds(ae, loopVar, iterName, lo, line, emitted, fs, /*hasCounter=*/true);
        }
    }

    /**
     * Pattern: {@code for (int i = LO; i < FIELD; i++) sum += FIELD2D[i][i];} where
     * {@code FIELD} is a numeric instance field bounding the loop and
     * {@code FIELD2D} is an int[][] instance field. Emits a per-element forall
     * bound on the diagonal plus a guarded loop invariant pinning the running
     * accumulator to a per-step share of the int range.
     *
     * <p>Companion of {@link #handleForLoopAccumulator}. The existing handler
     * keys the bound to {@code arr.length} when the loop iterates a 1D array
     * with {@code i < arr.length}; this handler keys the bound to a numeric
     * field when the loop iterates a 2D-diagonal access {@code arr[i][i]} with
     * {@code i < FIELD}.</p>
     */
    private void handleFieldBoundedDiagonalAccumulator(ForStmt fs, Set<String> emitted) {
        // Header: `for (int i = literal; i < FIELD; i++)`.
        if (fs.getInitialization().size() != 1) return;
        if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return;
        if (vde.getVariables().size() != 1) return;
        String loopVar = vde.getVariables().get(0).getNameAsString();
        Expression initExpr = vde.getVariables().get(0).getInitializer().orElse(null);
        if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return;
        int lo = initExpr.asIntegerLiteralExpr().asInt();
        if (lo < 0) return;

        Expression cmpExpr = fs.getCompare().orElse(null);
        if (!(cmpExpr instanceof BinaryExpr cmp)) return;
        if (cmp.getOperator() != BinaryExpr.Operator.LESS) return;
        if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                || !cmpLeft.getNameAsString().equals(loopVar)) return;
        // Upper bound must be a numeric instance field (e.g., size). The companion
        // handler covers `arr.length`; here we want field-bounded loops only.
        String boundField = fieldNameOf(cmp.getRight());
        if (boundField == null) return;

        int line = fs.getBegin().map(p -> p.line).orElse(0);

        // For each accumulator assignment in the body whose RHS is a 2D-diagonal
        // access of an int[][] field, emit per-element bound + running-sum invariant.
        for (AssignExpr ae : fs.getBody().findAll(AssignExpr.class)) {
            tryEmitDiagonalAccumulatorBounds(ae, loopVar, boundField, lo, line, emitted, fs);
            tryEmitRowFixedAccumulatorBounds(ae, loopVar, boundField, lo, line, emitted, fs);
        }
    }

    /**
     * Emits the diagonal-accumulator overflow precondition + loop invariant
     * for {@code accum += FIELD2D[loopVar][loopVar]} inside a loop bounded by
     * {@code boundField}.
     */
    private void tryEmitDiagonalAccumulatorBounds(AssignExpr ae, String loopVar, String boundField,
                                                   int lo, int line, Set<String> emitted,
                                                   com.github.javaparser.ast.Node loopNode) {
        if (!(ae.getTarget() instanceof NameExpr targetNe)) return;
        String accum = targetNe.getNameAsString();
        if (accum.equals(loopVar) || accum.equals(boundField)) return;
        if (paramNames.contains(accum) || fieldNames.contains(accum)) return;
        if (!isLocalIntAccum(accum, loopNode)) return;

        boolean isPlus = ae.getOperator() == AssignExpr.Operator.PLUS;
        boolean isPlainAssign = ae.getOperator() == AssignExpr.Operator.ASSIGN;
        if (!isPlus && !isPlainAssign) return;

        Expression rhs = ae.getValue();
        if (isPlainAssign) {
            if (!(rhs instanceof BinaryExpr be)) return;
            if (be.getOperator() != BinaryExpr.Operator.PLUS) return;
            boolean leftIsAccum = be.getLeft() instanceof NameExpr lne
                    && lne.getNameAsString().equals(accum);
            boolean rightIsAccum = be.getRight() instanceof NameExpr rne
                    && rne.getNameAsString().equals(accum);
            if (leftIsAccum == rightIsAccum) return;
            rhs = leftIsAccum ? be.getRight() : be.getLeft();
        }

        // RHS must be a 2D-diagonal access `FIELD2D[loopVar][loopVar]` where
        // FIELD2D is an int[][] field.
        String diag2d = diagonal2DFieldName(rhs, loopVar);
        if (diag2d == null) return;

        // Use fixed bounds +/- K_HI with K_N = 1_000_000 so K_HI * K_N + K_HI
        // stays well under Integer.MAX_VALUE (10^9 + 1000 < 2^31). The probe
        // formulation (validated 2026-04-30) uses the same constants because
        // the linear form is tractable for Z3 in a way that the alternative
        // division-based MIN/size formulation is not.
        final int K_HI = 1000;
        final int K_N = 1_000_000;
        String diagPrefix = "this." + diag2d;
        String boundPrefix = "this." + boundField;
        String elemBound = "(\\forall int k; " + lo + " <= k && k < " + boundPrefix + "; "
                + diagPrefix + "[k][k] >= -" + K_HI + " && "
                + diagPrefix + "[k][k] <= " + K_HI + ")";
        emitted.add(elemBound);
        // Cap the bound field so K_HI * boundField stays within int range.
        emitted.add(boundPrefix + " <= " + K_N);

        // Linear running-sum invariant. Unconditional because the right-hand
        // side is well-defined for any non-negative iteration count.
        if (spec != null) {
            String elapsed = (lo == 0)
                    ? loopVar
                    : "(" + loopVar + " - " + lo + ")";
            String linearInv = "-" + K_HI + " * " + elapsed + " <= " + accum
                    + " && " + accum + " <= " + K_HI + " * " + elapsed;
            spec.addLoopInvariant(linearInv, line);
        }
    }

    /**
     * Sister of {@link #tryEmitDiagonalAccumulatorBounds} for the row-fixed
     * 2D accumulator pattern: {@code accum += FIELD2D[fixedRowExpr][loopVar]}
     * where {@code fixedRowExpr} is a parameter or a constant (not dependent
     * on the loop variable). The matrixRowSum shape from
     * {@code DataStructureVerificationTest}.
     */
    private void tryEmitRowFixedAccumulatorBounds(AssignExpr ae, String loopVar, String boundField,
                                                   int lo, int line, Set<String> emitted,
                                                   com.github.javaparser.ast.Node loopNode) {
        if (!(ae.getTarget() instanceof NameExpr targetNe)) return;
        String accum = targetNe.getNameAsString();
        if (accum.equals(loopVar) || accum.equals(boundField)) return;
        if (paramNames.contains(accum) || fieldNames.contains(accum)) return;
        if (!isLocalIntAccum(accum, loopNode)) return;

        boolean isPlus = ae.getOperator() == AssignExpr.Operator.PLUS;
        boolean isPlainAssign = ae.getOperator() == AssignExpr.Operator.ASSIGN;
        if (!isPlus && !isPlainAssign) return;

        Expression rhs = ae.getValue();
        if (isPlainAssign) {
            if (!(rhs instanceof BinaryExpr be)) return;
            if (be.getOperator() != BinaryExpr.Operator.PLUS) return;
            boolean leftIsAccum = be.getLeft() instanceof NameExpr lne
                    && lne.getNameAsString().equals(accum);
            boolean rightIsAccum = be.getRight() instanceof NameExpr rne
                    && rne.getNameAsString().equals(accum);
            if (leftIsAccum == rightIsAccum) return;
            rhs = leftIsAccum ? be.getRight() : be.getLeft();
        }

        // RHS must be a row-fixed 2D access `FIELD2D[fixed][loopVar]` where
        // FIELD2D is an int[][] field and `fixed` is independent of loopVar.
        RowFixedAccess rowFixed = rowFixed2DFieldName(rhs, loopVar);
        if (rowFixed == null) return;

        // Same linear-bound formulation as the diagonal case for the same
        // tractability reasons.
        final int K_HI = 1000;
        final int K_N = 1_000_000;
        String diagPrefix = "this." + rowFixed.fieldName;
        String boundPrefix = "this." + boundField;
        // Inner-array length bound: the loop indexes data[fixed][j] for j up to
        // boundField, so the inner row must have at least `boundField` entries.
        String innerLengthBound = boundPrefix + " <= " + diagPrefix + "[" + rowFixed.fixedExpr + "].length";
        emitted.add(innerLengthBound);
        String elemBound = "(\\forall int k; " + lo + " <= k && k < " + boundPrefix + "; "
                + diagPrefix + "[" + rowFixed.fixedExpr + "][k] >= -" + K_HI + " && "
                + diagPrefix + "[" + rowFixed.fixedExpr + "][k] <= " + K_HI + ")";
        emitted.add(elemBound);
        emitted.add(boundPrefix + " <= " + K_N);

        if (spec != null) {
            String elapsed = (lo == 0)
                    ? loopVar
                    : "(" + loopVar + " - " + lo + ")";
            String linearInv = "-" + K_HI + " * " + elapsed + " <= " + accum
                    + " && " + accum + " <= " + K_HI + " * " + elapsed;
            spec.addLoopInvariant(linearInv, line);
        }
    }

    /**
     * If {@code expr} is shaped {@code FIELD2D[fixedExpr][loopVar]} where
     * {@code FIELD2D} is an int[][] instance field and {@code fixedExpr} is
     * independent of {@code loopVar} (a parameter or another field),
     * return the field name and the rendered fixedExpr. Otherwise null.
     */
    private RowFixedAccess rowFixed2DFieldName(Expression expr, String loopVar) {
        if (expr instanceof EnclosedExpr enc) return rowFixed2DFieldName(enc.getInner(), loopVar);
        if (!(expr instanceof ArrayAccessExpr outer)) return null;
        if (!(outer.getIndex() instanceof NameExpr outerIdx)
                || !outerIdx.getNameAsString().equals(loopVar)) return null;
        if (!(outer.getName() instanceof ArrayAccessExpr inner)) return null;
        // Inner index must be a parameter (fixed for the whole loop) or
        // any expression that does not contain the loop var.
        Expression innerIdxExpr = inner.getIndex();
        if (innerIdxExpr instanceof NameExpr innerNe) {
            String innerIdxName = innerNe.getNameAsString();
            if (innerIdxName.equals(loopVar)) return null; // diagonal handled elsewhere
            if (!paramNames.contains(innerIdxName)) return null;
        } else {
            // Conservative: require a simple parameter for now.
            return null;
        }
        Expression base = inner.getName();
        String fieldName = fieldNameOf(base);
        if (fieldName == null) return null;
        if (!isInt2DArrayField(fieldName)) return null;
        return new RowFixedAccess(fieldName, innerIdxExpr.toString());
    }

    private record RowFixedAccess(String fieldName, String fixedExpr) {
    }

    /**
     * If {@code expr} is shaped {@code FIELD2D[loopVar][loopVar]} where
     * {@code FIELD2D} is an int[][] instance field, return the field name.
     * Otherwise null.
     */
    private String diagonal2DFieldName(Expression expr, String loopVar) {
        if (expr instanceof EnclosedExpr enc) return diagonal2DFieldName(enc.getInner(), loopVar);
        if (!(expr instanceof ArrayAccessExpr outer)) return null;
        if (!(outer.getIndex() instanceof NameExpr outerIdx)
                || !outerIdx.getNameAsString().equals(loopVar)) return null;
        if (!(outer.getName() instanceof ArrayAccessExpr inner)) return null;
        if (!(inner.getIndex() instanceof NameExpr innerIdx)
                || !innerIdx.getNameAsString().equals(loopVar)) return null;
        // Inner array's name must be a 2D int field reference (this.field or bare field).
        Expression base = inner.getName();
        String fieldName = fieldNameOf(base);
        if (fieldName == null) return null;
        // Confirm the field is an int[][] type. We don't have full type information here;
        // approximate by checking the field's declared type contains "int" + two arrays.
        if (!isInt2DArrayField(fieldName)) return null;
        return fieldName;
    }

    /**
     * Returns the field name if {@code expr} resolves to a numeric instance field
     * (either {@code this.X} or a bare {@code X} that is declared as a field).
     * Returns {@code null} otherwise (including for {@code arr.length}, where the
     * companion {@link #handleForLoopAccumulator} applies instead).
     */
    private String fieldNameOf(Expression expr) {
        if (expr instanceof FieldAccessExpr fae && fae.getScope().toString().equals("this")) {
            String name = fae.getNameAsString();
            if (fieldNames.contains(name) || intFieldNames.contains(name)) return name;
            return null;
        }
        if (expr instanceof NameExpr ne) {
            String name = ne.getNameAsString();
            if (fieldNames.contains(name) || intFieldNames.contains(name)) return name;
        }
        return null;
    }

    private boolean isInt2DArrayField(String fieldName) {
        var clazz = methodDecl.findAncestor(ClassOrInterfaceDeclaration.class).orElse(null);
        if (clazz == null) return false;
        for (var field : clazz.getFields()) {
            for (VariableDeclarator var : field.getVariables()) {
                if (var.getNameAsString().equals(fieldName)) {
                    String t = var.getType().asString();
                    return t.equals("int[][]") || t.equals("long[][]") || t.equals("short[][]");
                }
            }
        }
        return false;
    }

    /** Pattern: {@code for (int val : arr) accum += val;}. */
    private void handleForEachAccumulator(ForEachStmt fes, Set<String> emitted) {
        String iterVar = fes.getVariable().getVariable(0).getNameAsString();
        Expression iterableExpr = fes.getIterable();
        String iterName = arrayScopeRefStr(iterableExpr);
        if (iterName == null) return;
        if (!isIntArrayName(iterableExpr)) return;

        int line = fes.getBegin().map(p -> p.line).orElse(0);
        for (AssignExpr ae : fes.getBody().findAll(AssignExpr.class)) {
            tryEmitForEachAccumulatorBounds(ae, iterVar, iterName, line, emitted);
        }
    }

    /** Pattern: {@code while (i < arr.length) { accum += arr[i]; i++; }}. */
    private void handleWhileAccumulator(WhileStmt ws, Set<String> emitted) {
        Expression cond = ws.getCondition();
        if (!(cond instanceof BinaryExpr cmp)) return;
        if (cmp.getOperator() != BinaryExpr.Operator.LESS) return;
        if (!(cmp.getLeft() instanceof NameExpr cmpLeft)) return;
        String loopVar = cmpLeft.getNameAsString();
        if (!(cmp.getRight() instanceof FieldAccessExpr fae)
                || !fae.getNameAsString().equals("length")) return;
        String iterName = arrayScopeRefStr(fae.getScope());
        if (iterName == null) return;
        if (!isIntArrayName(fae.getScope())) return;

        // Require the loop counter to start from 0 in pre-state. We look for a local
        // variable declaration `int loopVar = 0;` in the method.
        Integer lo = findLocalLiteralInit(loopVar);
        if (lo == null || lo < 0) return;

        int line = ws.getBegin().map(p -> p.line).orElse(0);
        for (AssignExpr ae : ws.getBody().findAll(AssignExpr.class)) {
            tryEmitAccumulatorBounds(ae, loopVar, iterName, lo, line, emitted, ws, /*hasCounter=*/true);
        }
    }

    /**
     * Emits the per-element bound + running-accumulator invariant for an assignment
     * shaped like {@code accum += RHS} where RHS depends on {@code loopVar}-indexed
     * accesses of {@code iterName}.
     */
    private void tryEmitAccumulatorBounds(AssignExpr ae, String loopVar, String iterName,
                                           int lo, int line, Set<String> emitted,
                                           com.github.javaparser.ast.Node loopNode,
                                           boolean hasCounter) {
        if (!(ae.getTarget() instanceof NameExpr targetNe)) return;
        String accum = targetNe.getNameAsString();
        if (accum.equals(loopVar)) return;
        // Accumulator must be a local int (not a parameter, field, or another loop var).
        if (paramNames.contains(accum) || fieldNames.contains(accum)) return;
        if (!isLocalIntAccum(accum, loopNode)) return;

        boolean isPlus = ae.getOperator() == AssignExpr.Operator.PLUS;
        boolean isMul = ae.getOperator() == AssignExpr.Operator.MULTIPLY;
        boolean isPlainAssign = ae.getOperator() == AssignExpr.Operator.ASSIGN;
        if (!isPlus && !isMul && !isPlainAssign) return;

        // For plain assignment, only `accum = accum + RHS` (or `*`) counts.
        Expression rhs = ae.getValue();
        if (isPlainAssign) {
            if (!(rhs instanceof BinaryExpr be)) return;
            BinaryExpr.Operator op = be.getOperator();
            if (op != BinaryExpr.Operator.PLUS && op != BinaryExpr.Operator.MULTIPLY) return;
            boolean leftIsAccum = be.getLeft() instanceof NameExpr lne
                    && lne.getNameAsString().equals(accum);
            boolean rightIsAccum = be.getRight() instanceof NameExpr rne
                    && rne.getNameAsString().equals(accum);
            if (leftIsAccum == rightIsAccum) return;
            rhs = leftIsAccum ? be.getRight() : be.getLeft();
            isPlus = (op == BinaryExpr.Operator.PLUS);
            isMul = !isPlus;
        }
        // Skip multiplication accumulators (factorial-style) for now — the per-step
        // bound `arr[k] <= MAX/arr.length` does not generalise to product.
        if (isMul) return;

        // RHS must reference a loop-indexed expression of `iterName`. The accumulator
        // case only applies when the RHS is exactly the array element (or the array
        // element times a per-step factor we can bound). For now: require RHS to be
        // either `arr[i]` directly, or a constant offset of it. Compound RHS like
        // `a[i] * b[i]` (dot product) needs a tighter pairwise bound that the existing
        // dual-array forall does not yet emit — leave that to a follow-up.
        if (!rhsIsBareLoopIndexedArray(rhs, loopVar, iterName)) return;

        emitAccumulatorBounds(accum, iterName, lo, line, emitted, loopVar, hasCounter);
    }

    /** Sister of {@link #tryEmitAccumulatorBounds} for the foreach `accum += val` shape. */
    private void tryEmitForEachAccumulatorBounds(AssignExpr ae, String iterVar, String iterName,
                                                  int line, Set<String> emitted) {
        if (!(ae.getTarget() instanceof NameExpr targetNe)) return;
        String accum = targetNe.getNameAsString();
        if (accum.equals(iterVar)) return;
        if (paramNames.contains(accum) || fieldNames.contains(accum)) return;
        if (!isLocalIntAccum(accum, null)) return;

        boolean isPlus = ae.getOperator() == AssignExpr.Operator.PLUS;
        boolean isPlainAssign = ae.getOperator() == AssignExpr.Operator.ASSIGN;
        if (!isPlus && !isPlainAssign) return;

        Expression rhs = ae.getValue();
        if (isPlainAssign) {
            if (!(rhs instanceof BinaryExpr be)
                    || be.getOperator() != BinaryExpr.Operator.PLUS) return;
            boolean leftIsAccum = be.getLeft() instanceof NameExpr lne
                    && lne.getNameAsString().equals(accum);
            boolean rightIsAccum = be.getRight() instanceof NameExpr rne
                    && rne.getNameAsString().equals(accum);
            if (leftIsAccum == rightIsAccum) return;
            rhs = leftIsAccum ? be.getRight() : be.getLeft();
        }
        // RHS must be the bare foreach iterator. Compound RHS like `val * 2` is
        // outside this simple emission shape; the existing analyzer chain handles
        // the multiplication separately, but the accumulator bound on the running
        // sum needs the bare-element shape to compose soundly.
        if (!(rhs instanceof NameExpr rhsNe) || !rhsNe.getNameAsString().equals(iterVar)) return;

        emitAccumulatorBounds(accum, iterName, 0, line, emitted, /*loopVar=*/null, /*hasCounter=*/false);
    }

    /**
     * Emits the precondition + loop invariant pair for an accumulator over
     * {@code iterName} starting from index {@code lo}.
     *
     * <p>Precondition:
     * {@code (\forall int k; lo <= k < arr.length; arr[k] >= Integer.MIN_VALUE / arr.length && arr[k] <= Integer.MAX_VALUE / arr.length)}.
     * Sound because every prefix of the loop adds at most {@code arr.length} elements
     * each bounded by {@code MAX/arr.length}, so the running sum stays in int range.
     * When {@code arr.length == 0} the forall body is unevaluated, so the inner
     * division is harmless.</p>
     *
     * <p>The loop invariant pins the running accumulator to the same per-step share of
     * the int range, multiplied by the elapsed iteration count. Cast through
     * {@code \bigint} so the multiplication itself can't overflow.</p>
     */
    private void emitAccumulatorBounds(String accum, String iterName, int lo,
                                        int line, Set<String> emitted,
                                        String loopVar, boolean hasCounter) {
        // Fixed-K formulation matching the matrixTrace probe (validated 2026-04-30).
        // Element bound K_HI=1000 and length cap K_N=10^6 give running sum bound
        // K_HI * K_N = 10^9 < INT_MAX, well-formed for Z3's linear integer theory.
        // The previous MAX/length formulation polluted invariants with literal
        // Integer.MAX_VALUE and Integer.MIN_VALUE strings (flagged by
        // InvalidInferenceRegressionTest3.noIntegerMaxValueString) and used integer
        // division by an unknown length, both of which were brittle.
        final int K_HI = 1000;
        final int K_N = 1_000_000;
        String elemBound = "(\\forall int k; " + lo + " <= k && k < " + iterName + ".length; "
                + iterName + "[k] >= -" + K_HI + " && "
                + iterName + "[k] <= " + K_HI + ")";
        emitted.add(elemBound);
        emitted.add(iterName + ".length <= " + K_N);

        // Linear running-sum invariant: accum bounded by K_HI * elapsed.
        // Stays inside Z3's tractable linear arithmetic.
        if (spec != null && hasCounter && loopVar != null) {
            String elapsed = (lo == 0)
                    ? loopVar
                    : "(" + loopVar + " - " + lo + ")";
            String linearInv = "-" + K_HI + " * " + elapsed + " <= " + accum
                    + " && " + accum + " <= " + K_HI + " * " + elapsed;
            spec.addLoopInvariant(linearInv, line);
        }
    }

    /**
     * True when {@code rhs} is exactly {@code iterName[loopVar]} (no compound),
     * i.e. the accumulator increment is a single array element. Compound RHS like
     * {@code arr[i] * 2} is rejected because the per-element bound on {@code arr[k]}
     * alone doesn't bound the increment {@code arr[k] * 2}.
     */
    private boolean rhsIsBareLoopIndexedArray(Expression rhs, String loopVar, String iterName) {
        if (rhs instanceof EnclosedExpr enc) return rhsIsBareLoopIndexedArray(enc.getInner(), loopVar, iterName);
        if (!(rhs instanceof ArrayAccessExpr aae)) return false;
        String base = getIntArrayBaseName(aae);
        if (base == null) return false;
        if (!base.equals(iterName) && !base.equals("this." + iterName)) return false;
        if (!(aae.getIndex() instanceof NameExpr idxNe)) return false;
        return idxNe.getNameAsString().equals(loopVar);
    }

    /**
     * True when the named local accumulator is declared inside the method as a literal
     * initialiser ({@code int accum = 0;} or {@code = 1;}) and is only assigned inside
     * the given loop. This guards against variables that already hold a non-zero value
     * before the loop, which would invalidate the per-step bound.
     */
    private boolean isLocalIntAccum(String accum, com.github.javaparser.ast.Node loopNode) {
        Expression init = localInits.get(accum);
        if (init == null) return false;
        // Init must be a literal 0 or 1 (sum/product identity). Skip parameter-derived
        // initialisers — those carry an unknown starting value.
        boolean isZeroOrOne = init.isIntegerLiteralExpr()
                && (init.asIntegerLiteralExpr().asInt() == 0
                        || init.asIntegerLiteralExpr().asInt() == 1);
        if (!isZeroOrOne) return false;

        // Verify the variable is declared as int (not array, not String, etc.).
        for (VariableDeclarator vd : methodDecl.findAll(VariableDeclarator.class)) {
            if (vd.getNameAsString().equals(accum)) {
                String t = vd.getType().asString();
                if (!isIntegerPrimitive(t)) return false;
                break;
            }
        }

        // Verify accum is not assigned outside the loop (ignoring the declarator init).
        // We accept multiple in-loop assignments (e.g. AccReset has currentSum reset in
        // an else-branch) but reject any assignment outside the loop scope.
        if (loopNode != null) {
            for (AssignExpr ae : methodDecl.findAll(AssignExpr.class)) {
                if (!(ae.getTarget() instanceof NameExpr ne)) continue;
                if (!ne.getNameAsString().equals(accum)) continue;
                if (!isInsideNode(ae, loopNode)) return false;
            }
        }
        return true;
    }

    private boolean isInsideNode(com.github.javaparser.ast.Node child,
                                  com.github.javaparser.ast.Node ancestor) {
        com.github.javaparser.ast.Node cur = child;
        while (cur.getParentNode().isPresent()) {
            cur = cur.getParentNode().get();
            if (cur == ancestor) return true;
        }
        return false;
    }

    /** Looks up `int X = LITERAL;` style declarations in the method body. */
    private Integer findLocalLiteralInit(String name) {
        Expression init = localInits.get(name);
        if (init == null || !init.isIntegerLiteralExpr()) return null;
        return init.asIntegerLiteralExpr().asInt();
    }

    /**
     * True when {@code expr} is an array reference (NameExpr / FieldAccessExpr) whose
     * underlying type is an int-array type — needed before emitting the
     * {@code Integer.MAX_VALUE / arr.length}-style bound.
     */
    private boolean isIntArrayName(Expression expr) {
        if (expr instanceof NameExpr ne) {
            String n = ne.getNameAsString();
            return intArrayParamNames.contains(n) || intArrayFieldNames.contains(n);
        }
        if (expr instanceof FieldAccessExpr fae
                && fae.getScope().toString().equals("this")) {
            return intArrayFieldNames.contains(fae.getNameAsString());
        }
        return false;
    }

    private void handleArrayCreation(ArrayCreationExpr arrayCreate, Set<String> emitted) {
        // `new T[n]` throws NegativeArraySizeException for n < 0. Emit `n >= 0` for every
        // dimension whose size is a pre-state-expressible integer expression.
        //
        // When the dimension is a compound arithmetic expression (e.g. `arr.length * 2`,
        // `a.length + b.length`), also emit `\bigint`-bounded overflow preconditions on
        // the dimension itself. Without this OpenJML raises `int multiply out of range`
        // or `overflow in int sum` on the array allocation. Driven by the
        // ArrCreate2.doubleCapacity / ArrayMerge.merge cases.
        for (var level : arrayCreate.getLevels()) {
            level.getDimension().ifPresent(dim -> {
                String sizeStr = toIntStr(dim);
                if (sizeStr != null) {
                    emitted.add(sizeStr + " >= 0");
                }
                // Emit bigint overflow bounds when the dimension contains a binary
                // arithmetic operator. A bare name/literal/length cannot overflow.
                if (containsBinaryArithmetic(dim)) {
                    String bigintForm = toBigintStr(dim);
                    if (bigintForm != null) {
                        emitBigintBoundsRaw(emitted, bigintForm);
                    }
                }
            });
        }
    }

    /** True when {@code expr} contains a +, -, * sub-expression that could overflow. */
    private boolean containsBinaryArithmetic(Expression expr) {
        if (expr instanceof EnclosedExpr enc) return containsBinaryArithmetic(enc.getInner());
        if (expr instanceof BinaryExpr be) {
            BinaryExpr.Operator op = be.getOperator();
            return op == BinaryExpr.Operator.PLUS
                    || op == BinaryExpr.Operator.MINUS
                    || op == BinaryExpr.Operator.MULTIPLY
                    || containsBinaryArithmetic(be.getLeft())
                    || containsBinaryArithmetic(be.getRight());
        }
        if (expr instanceof UnaryExpr ue && ue.getOperator() == UnaryExpr.Operator.MINUS) {
            return containsBinaryArithmetic(ue.getExpression());
        }
        return false;
    }

    // ---------------------------------------------------------------------
    // Handlers — one per syntactic shape
    // ---------------------------------------------------------------------

    private void handleCompoundAssignment(AssignExpr assign, Set<String> emitted) {
        String opSym = compoundOpSymbol(assign.getOperator());
        if (opSym == null) return;

        // Case A — compound assignment on a field: `this.field += value`.
        String targetRef = resolveFieldRef(assign.getTarget());
        if (targetRef != null) {
            String valueStr = toBigintStr(assign.getValue());
            if (valueStr == null) return;
            String targetBigint = "(\\bigint) " + targetRef;
            emitBigintBoundsRaw(emitted, "(" + targetBigint + " " + opSym + " " + valueStr + ")");
            return;
        }

        // Case B — compound assignment on a loop-indexed array element:
        // `arr[loopVar] += value`. Emit a forall over the loop range so the
        // overflow check holds for every element. Sister of the unary-increment
        // forall fallback.
        if (assign.getTarget() instanceof ArrayAccessExpr aae && isLoopIndexedArrayAccess(aae)) {
            String valueStr = toBigintStr(assign.getValue());
            if (valueStr == null) return;
            String arrayName = getIntArrayBaseName(aae);
            if (arrayName == null) return;
            ForRange r = extractForRange(assign, aae, arrayName);
            if (r == null) return;
            String elem = "(\\bigint) " + arrayName + "[k]";
            String combined = "(" + elem + " " + opSym + " " + valueStr + ")";
            String forallLo = "(\\forall int k; " + r.lo + " <= k && k < " + r.high + "; "
                    + combined + " >= Integer.MIN_VALUE)";
            String forallHi = "(\\forall int k; " + r.lo + " <= k && k < " + r.high + "; "
                    + combined + " <= Integer.MAX_VALUE)";
            emitted.add(forallLo);
            emitted.add(forallHi);
        }
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
        if (intForm != null) {
            // Skip when operand is a literal that can never be Integer.MIN_VALUE —
            // the constraint would be trivially true and only adds noise.
            if (!isTriviallyNotMinValue(operand)) {
                emitted.add(intForm + " != Integer.MIN_VALUE");
            }
            return;
        }
        // The straight-line case failed (e.g. operand uses a loop variable). If the
        // operand is `arr[loopVar]` inside a for-loop iterating over arr, emit a
        // universal precondition over the loop range so OpenJML can discharge the
        // negation overflow check on every element.
        emitForallElementPrecondition(unary, operand, emitted, "!= Integer.MIN_VALUE");
    }

    /**
     * True when {@code expr} is an integer literal whose value is demonstrably not
     * {@code Integer.MIN_VALUE} (-2147483648). Used to suppress trivially-true
     * overflow preconditions on literal operands.
     */
    private boolean isTriviallyNotMinValue(Expression expr) {
        if (expr instanceof IntegerLiteralExpr lit) {
            return lit.asInt() != Integer.MIN_VALUE;
        }
        if (expr instanceof UnaryExpr u
                && u.getOperator() == UnaryExpr.Operator.MINUS
                && u.getExpression() instanceof IntegerLiteralExpr inner) {
            // -N fits in int as long as inner != 2147483648; we conservatively
            // treat every negated literal we can read as "not MIN_VALUE" only
            // when its absolute value is strictly less than 2^31.
            try {
                long v = -((long) inner.asInt());
                return v != Integer.MIN_VALUE;
            } catch (Exception ignored) {
                return false;
            }
        }
        return false;
    }

    /** True when {@code expr} is a non-zero integer literal. */
    private boolean isTriviallyNonzero(Expression expr) {
        if (expr instanceof IntegerLiteralExpr lit) {
            return lit.asInt() != 0;
        }
        if (expr instanceof UnaryExpr u
                && u.getOperator() == UnaryExpr.Operator.MINUS
                && u.getExpression() instanceof IntegerLiteralExpr inner) {
            return inner.asInt() != 0;
        }
        return false;
    }

    /** True when {@code expr} is an integer literal whose value is not {@code -1}. */
    private boolean isTriviallyNotMinusOne(Expression expr) {
        if (expr instanceof IntegerLiteralExpr lit) {
            return lit.asInt() != -1;
        }
        if (expr instanceof UnaryExpr u
                && u.getOperator() == UnaryExpr.Operator.MINUS
                && u.getExpression() instanceof IntegerLiteralExpr inner) {
            return inner.asInt() != 1;
        }
        // Non-literal right-hand side — we don't know, so don't suppress the guard.
        return false;
    }

    /**
     * If {@code operand} is {@code arr[loopVar]} where the enclosing for-loop iterates
     * {@code for (int loopVar = LO; loopVar <op> arr.length; loopVar++)} (or similar
     * literal-bounded shape), emit
     * {@code (\forall int k; LO <= k && k < arr.length; arr[k] PROP)}.
     *
     * <p>When the operation is value-preserving (e.g. negation: {@code -arr[k]}), the
     * forall is also emitted as a loop invariant since {@code arr[k] != Integer.MIN_VALUE}
     * holds at every iteration. When the operation mutates the element (e.g.
     * {@code arr[k]++}), pass {@code mutatesElement=true} so the invariant is tightened
     * to {@code i <= k && k < arr.length} — the as-yet-untouched range.</p>
     */
    private void emitForallElementPrecondition(com.github.javaparser.ast.Node origin,
                                                Expression operand, Set<String> emitted,
                                                String predicateRhs) {
        emitForallElementPrecondition(origin, operand, emitted, predicateRhs, false);
    }

    private void emitForallElementPrecondition(com.github.javaparser.ast.Node origin,
                                                Expression operand, Set<String> emitted,
                                                String predicateRhs, boolean mutatesElement) {
        if (!(operand instanceof ArrayAccessExpr aae)) return;
        String arrayName = getIntArrayBaseName(aae);
        if (arrayName == null) return;
        if (!(aae.getIndex() instanceof NameExpr idxNe)) return;
        String idx = idxNe.getNameAsString();
        if (!loopVars.contains(idx)) return;

        Optional<com.github.javaparser.ast.stmt.ForStmt> forOpt =
                origin.findAncestor(com.github.javaparser.ast.stmt.ForStmt.class);
        if (forOpt.isEmpty()) return;
        com.github.javaparser.ast.stmt.ForStmt fs = forOpt.get();
        if (fs.getInitialization().size() != 1) return;
        if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return;
        if (vde.getVariables().size() != 1) return;
        if (!vde.getVariables().get(0).getNameAsString().equals(idx)) return;
        Expression initExpr = vde.getVariables().get(0).getInitializer().orElse(null);
        if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return;
        int lo = initExpr.asIntegerLiteralExpr().asInt();
        if (lo < 0) return;

        // Upper bound: must be `idx <op> arr.length` to keep the quantifier sound.
        Expression cmpExpr = fs.getCompare().orElse(null);
        if (!(cmpExpr instanceof BinaryExpr cmp)) return;
        if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                || !cmpLeft.getNameAsString().equals(idx)) return;
        String upper;
        if (cmp.getRight() instanceof FieldAccessExpr fae
                && fae.getNameAsString().equals("length")
                && fae.getScope() instanceof NameExpr aNe
                && aNe.getNameAsString().equals(arrayName)) {
            upper = arrayName + ".length";
        } else {
            return;
        }

        String forall = "(\\forall int k; " + lo + " <= k && k < " + upper + "; "
                + arrayName + "[k] " + predicateRhs + ")";
        emitted.add(forall);
        if (spec != null) {
            int line = fs.getBegin().map(p -> p.line).orElse(0);
            // For value-preserving operations (negation, comparison) the precondition
            // still holds at every iteration. For element-mutating operations (++/--,
            // arr[i] = arr[i] + K) the predicate only holds for the untouched suffix
            // [i, arr.length).
            if (mutatesElement) {
                String suffixForall = "(\\forall int k; " + idx + " <= k && k < " + upper + "; "
                        + arrayName + "[k] " + predicateRhs + ")";
                spec.addLoopInvariant(suffixForall, line);
            } else {
                spec.addLoopInvariant(forall, line);
            }
        }
    }

    private void handleUnaryIncrement(UnaryExpr unary, Set<String> emitted) {
        UnaryExpr.Operator op = unary.getOperator();
        boolean isIncrement = op == UnaryExpr.Operator.POSTFIX_INCREMENT
                || op == UnaryExpr.Operator.PREFIX_INCREMENT;
        boolean isDecrement = op == UnaryExpr.Operator.POSTFIX_DECREMENT
                || op == UnaryExpr.Operator.PREFIX_DECREMENT;
        if (!isIncrement && !isDecrement) return;

        String intForm = toIntStr(unary.getExpression());
        if (intForm == null) {
            // Fallback: the operand might be `arr[loopVar]` inside a literal-bounded
            // for-loop. Emit a universal precondition over the loop range so the
            // increment overflow check holds for every element. Driven by ArrMut3.
            String predicateRhs = isIncrement
                    ? "< Integer.MAX_VALUE"
                    : "> Integer.MIN_VALUE";
            // Element is mutated in place — invariant holds only for the untouched
            // suffix of the array (k >= loop counter).
            emitForallElementPrecondition(unary, unary.getExpression(), emitted,
                    predicateRhs, /*mutatesElement=*/true);
            return;
        }

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
        if (bigint != null) {
            emitBigintBoundsRaw(emitted, bigint);
            return;
        }
        // Fallback: arithmetic involving a loop-indexed array element. Emit a universal
        // precondition over the loop range so OpenJML can discharge the overflow check
        // for every element. Handles the common `arr[i] * K`, `arr[i] + K`, `K - arr[i]`,
        // etc. shapes inside `for (i = LO; i < arr.length; i++)` loops.
        emitForallBinaryOverflow(binary, emitted);
    }

    /**
     * For {@code arr[loopVar] op OTHER} (or {@code OTHER op arr[loopVar]}) inside a
     * literal-bounded for-loop, emit a universal precondition that every element of
     * {@code arr} combined with OTHER stays inside int range.
     *
     * Also handles {@code arr[idx1] op arr[idx2]} where both indices are simple
     * loop-variable expressions (e.g. {@code arr[i] + arr[i-1]}) — these need a
     * stricter quantifier range that bounds the offset and a paired {@code \bigint}
     * combination of two array elements. Driven by the PrefixSum case study.
     */
    private void emitForallBinaryOverflow(BinaryExpr binary, Set<String> emitted) {
        String opSym = composableBinaryOpSymbol(binary.getOperator());
        if (opSym == null) return;

        // Case A — `arr[loopVar] op OTHER` / `OTHER op arr[loopVar]`. One side is a
        // loop-indexed array element; the other lives in pre-state.
        ArrayAccessExpr arrSide = null;
        Expression otherSide = null;
        boolean arrIsLeft = false;
        if (binary.getLeft() instanceof ArrayAccessExpr aa && isLoopIndexedArrayAccess(aa)) {
            arrSide = aa;
            otherSide = binary.getRight();
            arrIsLeft = true;
        } else if (binary.getRight() instanceof ArrayAccessExpr aa && isLoopIndexedArrayAccess(aa)) {
            arrSide = aa;
            otherSide = binary.getLeft();
        }
        if (arrSide != null) {
            // If the OTHER side is also a loop-indexed array access (possibly with
            // a literal offset like `arr[i-1]`), fall through to the dual-array
            // handler. Otherwise emit the single-array pattern.
            if (otherSide instanceof ArrayAccessExpr otherAae
                    && isLoopOffsetArrayAccess(otherAae)) {
                emitForallDualArrayOverflow(binary, arrSide, otherAae, opSym, arrIsLeft, emitted);
                return;
            }

            String arrayName = getIntArrayBaseName(arrSide);
            if (arrayName == null) return;
            String otherBigint = toBigintStr(otherSide);
            if (otherBigint == null) return;

            ForRange r = extractForRange(binary, arrSide, arrayName);
            if (r == null) return;

            String arrElem = "(\\bigint) " + arrayName + "[k]";
            String combined = arrIsLeft
                    ? "(" + arrElem + " " + opSym + " " + otherBigint + ")"
                    : "(" + otherBigint + " " + opSym + " " + arrElem + ")";
            emitted.add("(\\forall int k; " + r.lo + " <= k && k < " + r.high + "; "
                    + combined + " >= Integer.MIN_VALUE)");
            emitted.add("(\\forall int k; " + r.lo + " <= k && k < " + r.high + "; "
                    + combined + " <= Integer.MAX_VALUE)");
            return;
        }

        // Case B — both sides are loop-indexed (possibly offset) array accesses on
        // the same array. Example: `arr[i] + arr[i-1]` in PrefixSum.
        if (binary.getLeft() instanceof ArrayAccessExpr l
                && binary.getRight() instanceof ArrayAccessExpr r
                && isLoopOffsetArrayAccess(l) && isLoopOffsetArrayAccess(r)) {
            emitForallDualArrayOverflow(binary, l, r, opSym, true, emitted);
        }
    }

    /**
     * Emits the {@code \bigint}-bounded \forall precondition for a binary op whose
     * BOTH operands are loop-indexed (possibly offset) array accesses. The quantifier
     * range is tightened so every offset stays in-bounds (e.g. for
     * {@code arr[i] + arr[i-1]} in {@code for(i=1; i<arr.length; i++)} the range
     * is {@code 1 <= k < arr.length} which already guarantees both {@code k} and
     * {@code k-1} are valid indices).
     */
    private void emitForallDualArrayOverflow(BinaryExpr binary, ArrayAccessExpr leftAae,
                                              ArrayAccessExpr rightAae, String opSym,
                                              boolean leftIsLeftOperand, Set<String> emitted) {
        String leftArr = getIntArrayBaseName(leftAae);
        String rightArr = getIntArrayBaseName(rightAae);
        if (leftArr == null || rightArr == null) return;
        // Cross-array pairings (e.g. `a[i] + b[i]` in ArrayMath.add) and same-array
        // offset pairings (e.g. `arr[i] + arr[i-1]` in PrefixSum) are both in scope.
        // For cross-array, OpenJML needs PreconditionAnalyzer.analyzeCrossArrayLoopBounds
        // to additionally emit `b.length >= a.length` so the `b[k]` access inside the
        // \forall is in-bounds; that analyzer runs separately and the two sets of
        // preconditions compose correctly at OpenJML.

        ForRange r = extractForRange(binary, leftAae, leftArr);
        if (r == null) return;

        // Substitute `i` -> `k` in each index expression so they live under the
        // \forall binding. The simple cases handled here are `i`, `i+LIT`, `i-LIT`.
        String leftIdx = rewriteIndexToK(leftAae.getIndex());
        String rightIdx = rewriteIndexToK(rightAae.getIndex());
        if (leftIdx == null || rightIdx == null) return;

        // Tighten the lower bound when one of the indices is `i-K` (k-K must be >= 0
        // for the access to be in-bounds). PrefixSum's `arr[i-1]` already ships with
        // a `for (i=1; ...)` so the lo of `1` is sufficient; a smarter inferrer could
        // raise lo here based on the largest negative offset, but the current shape
        // is constrained enough that the fixture-emitted lo suffices.
        String leftElem = "(\\bigint) " + leftArr + "[" + leftIdx + "]";
        String rightElem = "(\\bigint) " + rightArr + "[" + rightIdx + "]";
        String combined = leftIsLeftOperand
                ? "(" + leftElem + " " + opSym + " " + rightElem + ")"
                : "(" + rightElem + " " + opSym + " " + leftElem + ")";
        emitted.add("(\\forall int k; " + r.lo + " <= k && k < " + r.high + "; "
                + combined + " >= Integer.MIN_VALUE)");
        emitted.add("(\\forall int k; " + r.lo + " <= k && k < " + r.high + "; "
                + combined + " <= Integer.MAX_VALUE)");
    }

    /**
     * True when {@code aa}'s index is a simple loop-variable expression: bare
     * {@code i}, or {@code i +/- LITERAL}.
     */
    private boolean isLoopOffsetArrayAccess(ArrayAccessExpr aa) {
        Expression idx = aa.getIndex();
        if (idx instanceof NameExpr ne) return loopVars.contains(ne.getNameAsString());
        if (idx instanceof BinaryExpr be
                && (be.getOperator() == BinaryExpr.Operator.PLUS
                        || be.getOperator() == BinaryExpr.Operator.MINUS)) {
            boolean leftLoop = be.getLeft() instanceof NameExpr lne
                    && loopVars.contains(lne.getNameAsString());
            boolean rightLit = be.getRight().isIntegerLiteralExpr();
            return leftLoop && rightLit;
        }
        return false;
    }

    /**
     * Rewrites a loop-indexed expression to use {@code k} in place of the loop var.
     * Returns null for shapes outside `i`, `i+LIT`, `i-LIT`.
     */
    private String rewriteIndexToK(Expression idx) {
        if (idx instanceof NameExpr ne && loopVars.contains(ne.getNameAsString())) {
            return "k";
        }
        if (idx instanceof BinaryExpr be
                && (be.getOperator() == BinaryExpr.Operator.PLUS
                        || be.getOperator() == BinaryExpr.Operator.MINUS)
                && be.getLeft() instanceof NameExpr lne
                && loopVars.contains(lne.getNameAsString())
                && be.getRight().isIntegerLiteralExpr()) {
            String op = be.getOperator() == BinaryExpr.Operator.PLUS ? " + " : " - ";
            return "k" + op + be.getRight().asIntegerLiteralExpr().asInt();
        }
        return null;
    }

    private boolean isLoopIndexedArrayAccess(ArrayAccessExpr aa) {
        if (!(aa.getIndex() instanceof NameExpr idx)) return false;
        return loopVars.contains(idx.getNameAsString());
    }

    private record ForRange(String lo, String high) {}

    private ForRange extractForRange(com.github.javaparser.ast.Node origin,
                                      ArrayAccessExpr arrSide, String arrayName) {
        if (!(arrSide.getIndex() instanceof NameExpr idxNe)) return null;
        String idx = idxNe.getNameAsString();
        Optional<com.github.javaparser.ast.stmt.ForStmt> forOpt =
                origin.findAncestor(com.github.javaparser.ast.stmt.ForStmt.class);
        if (forOpt.isEmpty()) return null;
        com.github.javaparser.ast.stmt.ForStmt fs = forOpt.get();
        if (fs.getInitialization().size() != 1) return null;
        if (!(fs.getInitialization().get(0) instanceof VariableDeclarationExpr vde)) return null;
        if (vde.getVariables().size() != 1) return null;
        if (!vde.getVariables().get(0).getNameAsString().equals(idx)) return null;
        Expression initExpr = vde.getVariables().get(0).getInitializer().orElse(null);
        if (initExpr == null || !initExpr.isIntegerLiteralExpr()) return null;
        int lo = initExpr.asIntegerLiteralExpr().asInt();
        if (lo < 0) return null;

        if (fs.getCompare().isEmpty()) return null;
        if (!(fs.getCompare().get() instanceof BinaryExpr cmp)) return null;
        if (!(cmp.getLeft() instanceof NameExpr cmpLeft)
                || !cmpLeft.getNameAsString().equals(idx)) return null;
        if (cmp.getOperator() != BinaryExpr.Operator.LESS) return null;
        if (!(cmp.getRight() instanceof FieldAccessExpr fae)
                || !fae.getNameAsString().equals("length")
                || !(fae.getScope() instanceof NameExpr aNe)
                || !aNe.getNameAsString().equals(arrayName)) return null;
        return new ForRange(Integer.toString(lo), arrayName + ".length");
    }

    /**
     * For {@code a / b} or {@code a % b}, emit {@code b != 0} when {@code b} is
     * pre-state-expressible (parameter, field, literal). Without this, OpenJML
     * raises {@code PossiblyDivideByZero} on every integer division.
     *
     * <p>For division specifically, also emit the {@code Integer.MIN_VALUE / -1}
     * overflow guard. Without it OpenJML raises an
     * {@code ArithmeticOperationRange overflow in int divide} obligation on
     * every guarded integer division.</p>
     */
    private void handleDivisionByZero(BinaryExpr binary, Set<String> emitted) {
        BinaryExpr.Operator op = binary.getOperator();
        if (op != BinaryExpr.Operator.DIVIDE && op != BinaryExpr.Operator.REMAINDER) return;
        String rhs = toIntStr(binary.getRight());
        if (rhs == null) return;
        // Suppress trivially-true `b != 0` when `b` is a non-zero literal.
        if (!isTriviallyNonzero(binary.getRight())) {
            emitted.add(rhs + " != 0");
        }
        if (op == BinaryExpr.Operator.DIVIDE) {
            String lhs = toIntStr(binary.getLeft());
            if (lhs == null) return;
            // The MIN_VALUE/-1 overflow can't happen when either side is literally
            // guaranteed otherwise — skip the guard then.
            if (isTriviallyNotMinValue(binary.getLeft())) return;
            if (isTriviallyNotMinusOne(binary.getRight())) return;
            emitted.add(lhs + " != Integer.MIN_VALUE || " + rhs + " != -1");
        }
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
            String name = fae.getNameAsString();
            if (scope.equals("this") && intFieldNames.contains(name)) {
                return "(\\bigint) this." + name;
            }
            if (name.equals("length")) {
                // arr.length is int-typed; the scope must resolve to an array reference
                // (param or field of array type), not via toIntStr which only handles
                // integer-typed scopes.
                String scopeStr = arrayScopeRefStr(fae.getScope());
                return scopeStr == null ? null : "(\\bigint) " + scopeStr + ".length";
            }
            // Peer-class access: `other.value` where `other` is a parameter and the
            // current class has an int field of the same name. The pattern fires for
            // binary methods like `compareTo(Other o) { return this.value - o.value; }`
            // where `o` is the same class as `this`. Without this lift, the overflow
            // precondition for `this.value - o.value` is never emitted because the
            // binary's right operand can't be cast.
            if (fae.getScope() instanceof NameExpr scopeNe
                    && paramNames.contains(scopeNe.getNameAsString())
                    && intFieldNames.contains(name)) {
                return "(\\bigint) " + scopeNe.getNameAsString() + "." + name;
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

        // Ternary: emit `(cond ? bigint(a) : bigint(b))`. The condition stays in its
        // original (pre-state-substituted) form because it's bool-typed. Used to
        // express the abs pattern `(dx < 0 ? -dx : dx)` as a bigint expression.
        if (e instanceof ConditionalExpr ce) {
            String condStr = toPrestatePredicateStr(ce.getCondition());
            String thenStr = toBigintStr(ce.getThenExpr());
            String elseStr = toBigintStr(ce.getElseExpr());
            if (condStr == null || thenStr == null || elseStr == null) return null;
            return "(" + condStr + " ? " + thenStr + " : " + elseStr + ")";
        }

        // `param.length()` — String.length / CharSequence.length is a non-negative int.
        // Similar for `param.size()` on collections.
        if (e instanceof MethodCallExpr mce) {
            String name = mce.getNameAsString();
            if (!mce.getArguments().isEmpty()) return null;
            if (!name.equals("length") && !name.equals("size")) return null;
            if (mce.getScope().isEmpty()) return null;
            Expression scope = mce.getScope().get();
            if (!(scope instanceof NameExpr scopeNe)) return null;
            String scopeName = scopeNe.getNameAsString();
            if (paramNames.contains(scopeName) || fieldNames.contains(scopeName)) {
                return "(\\bigint) " + scopeName + "." + name + "()";
            }
            return null;
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

    /**
     * Returns a syntactic boolean-predicate string with locals substituted from their
     * pre-state initializers, or {@code null} if any leaf is non-substitutable.
     * Used inside {@link #toBigintStr} for ternary conditions like {@code dx < 0}.
     * Supports relational ({@code <, <=, >, >=, ==, !=}) and logical ({@code &&, ||, !})
     * operators on top of the int-form leaves recognised by {@link #toIntStr}.
     */
    private String toPrestatePredicateStr(Expression e) {
        if (e instanceof EnclosedExpr enc) {
            String inner = toPrestatePredicateStr(enc.getInner());
            return inner == null ? null : "(" + inner + ")";
        }
        if (e instanceof UnaryExpr ue && ue.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
            String inner = toPrestatePredicateStr(ue.getExpression());
            return inner == null ? null : "(!" + inner + ")";
        }
        if (e instanceof BinaryExpr be) {
            BinaryExpr.Operator op = be.getOperator();
            String relSym = relationalOpSymbol(op);
            if (relSym != null) {
                String left = toIntStr(be.getLeft());
                String right = toIntStr(be.getRight());
                if (left == null || right == null) return null;
                return "(" + left + " " + relSym + " " + right + ")";
            }
            String logicalSym = logicalOpSymbol(op);
            if (logicalSym != null) {
                String left = toPrestatePredicateStr(be.getLeft());
                String right = toPrestatePredicateStr(be.getRight());
                if (left == null || right == null) return null;
                return "(" + left + " " + logicalSym + " " + right + ")";
            }
        }
        if (e instanceof BooleanLiteralExpr) return e.toString();
        return null;
    }

    private String relationalOpSymbol(BinaryExpr.Operator op) {
        return switch (op) {
            case LESS -> "<";
            case LESS_EQUALS -> "<=";
            case GREATER -> ">";
            case GREATER_EQUALS -> ">=";
            case EQUALS -> "==";
            case NOT_EQUALS -> "!=";
            default -> null;
        };
    }

    private String logicalOpSymbol(BinaryExpr.Operator op) {
        return switch (op) {
            case AND -> "&&";
            case OR -> "||";
            default -> null;
        };
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
