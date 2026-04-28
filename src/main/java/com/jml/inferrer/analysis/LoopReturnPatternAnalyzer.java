package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Recognises common single-method "loop returning a local variable" patterns and emits
 * sound, quantifier-bearing postconditions for them.
 *
 * Each recognised pattern produces a JML-quantified ensures clause that can be discharged
 * by OpenJML on its own merits — none of them rely on assumed properties of array elements
 * that the inferrer cannot establish.
 *
 * Patterns covered:
 * <ul>
 *   <li>SUM_ARRAY: {@code int s = 0; for(...) s += arr[i] | x; return s;} →
 *       {@code arr.length == 0 ==> \result == 0}</li>
 *   <li>PRODUCT_ARRAY: {@code int p = 1; for(...) p *= arr[i] | x; return p;} →
 *       {@code arr.length == 0 ==> \result == 1}</li>
 *   <li>MAX_ARRAY/MIN_ARRAY: {@code int m = arr[0]; for(...) if(arr[i]>m) m = arr[i]; return m;}
 *       → {@code (\exists int k; 0 <= k && k < arr.length; \result == arr[k])} +
 *       {@code (\forall int k; 0 <= k && k < arr.length; \result >= arr[k])}</li>
 *   <li>CONDITIONAL_COUNTER: {@code int c = 0; for(...) if(cond) c++; return c;} →
 *       {@code \result >= 0 && \result <= arr.length}</li>
 *   <li>LINEAR_SEARCH_INDEX: {@code for(...) if(arr[i] == target) return i; return -1;} →
 *       {@code \result >= -1 && \result < arr.length}</li>
 *   <li>LINEAR_SEARCH_BOOLEAN: {@code for(...) if(arr[i] == target) return true; return false;}
 *       → {@code \result == (\exists int k; 0 <= k && k < arr.length; arr[k] == target)}</li>
 * </ul>
 */
class LoopReturnPatternAnalyzer {

    void analyze(MethodDeclaration methodDecl, Set<String> postconditions) {
        analyze(methodDecl, postconditions, null);
    }

    void analyze(MethodDeclaration methodDecl, Set<String> postconditions, MethodSpecification spec) {
        if (methodDecl.getBody().isEmpty()) return;

        // Linear-search patterns dispatch on the SHAPE of the returns, not on a single
        // accumulator local — handle them first as they don't fit the "return localVar" mould.
        analyzeLinearSearch(methodDecl, postconditions, spec);

        // Accumulator patterns: must end with `return localVar;` as the unique return.
        List<ReturnStmt> allReturns = methodDecl.findAll(ReturnStmt.class);
        if (allReturns.size() != 1) return;
        ReturnStmt rs = allReturns.get(0);
        if (rs.getExpression().isEmpty()) return;
        if (!(rs.getExpression().get() instanceof NameExpr returnName)) return;
        String varName = returnName.getNameAsString();

        // Skip params/fields — handled elsewhere
        boolean isParam = methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(varName));
        if (isParam) return;
        if (AnalysisUtils.isFieldReference(methodDecl, varName)) return;

        VariableDeclarator declarator = findDeclarator(methodDecl, varName);
        if (declarator == null || declarator.getInitializer().isEmpty()) return;
        Expression init = declarator.getInitializer().get();

        // Identify the single loop containing the modifications. If there are multiple loops
        // each touching the variable, the patterns below don't apply cleanly.
        List<Statement> modifyingLoops = findLoopsModifying(methodDecl, varName);
        if (modifyingLoops.size() != 1) return;
        Statement loop = modifyingLoops.get(0);

        // SUM accumulator: any monotonic-additive accumulator initialised to 0.
        // Sound observation: when the loop's iteration count is 0 the accumulator stays at 0.
        if (isIntegerLiteral(init, 0) && isPlainAccumulator(loop, varName, AssignExpr.Operator.PLUS)) {
            String emptyCond = emptyLoopCondition(loop, methodDecl);
            if (emptyCond != null) {
                String guarded = guardWithFieldNullChecks(emptyCond, methodDecl);
                postconditions.add(guarded + " ==> \\result == 0");
            }
            return;
        }

        // PRODUCT accumulator initialised to 1.
        if (isIntegerLiteral(init, 1) && isPlainAccumulator(loop, varName, AssignExpr.Operator.MULTIPLY)) {
            String emptyCond = emptyLoopCondition(loop, methodDecl);
            if (emptyCond != null) {
                String guarded = guardWithFieldNullChecks(emptyCond, methodDecl);
                postconditions.add(guarded + " ==> \\result == 1");
            }
            return;
        }

        // MAX / MIN tracking
        ArrayElementInit aei = asArrayFirstElement(init, methodDecl);
        if (aei != null) {
            BinaryExpr.Operator cmpOp = identifyMaxMinPattern(loop, varName, aei.arrayName);
            // Determine the index range. For `int max = arr[0]; for(int i = 1; i < arr.length; i++)`
            // the range is [0, arr.length). For `int max = arr[start]; for(int i = start+1; i < end; i++)`
            // the range is [start, end). We derive it from the for-loop's compare bound when
            // possible and fall back to [aei.indexExpr, arrayName.length) for [0, length).
            String[] range = inferIndexRange(loop, aei, methodDecl);
            if (range == null) return;
            String low = range[0];
            String high = range[1];
            if (cmpOp == BinaryExpr.Operator.GREATER || cmpOp == BinaryExpr.Operator.GREATER_EQUALS) {
                emitMaxEnsures(postconditions, aei.arrayName, low, high);
                emitMaxMinInvariants(loop, varName, aei.arrayName, low, ">=", spec);
                return;
            }
            if (cmpOp == BinaryExpr.Operator.LESS || cmpOp == BinaryExpr.Operator.LESS_EQUALS) {
                emitMinEnsures(postconditions, aei.arrayName, low, high);
                emitMaxMinInvariants(loop, varName, aei.arrayName, low, "<=", spec);
                return;
            }
        }

        // CONDITIONAL counter
        if (isIntegerLiteral(init, 0) && isConditionalIncrement(loop, varName)) {
            String iterableName = extractIterableName(loop);
            if (iterableName != null) {
                postconditions.add("\\result >= 0");
                postconditions.add("\\result <= " + iterableName + ".length");
            }
            return;
        }

        // MAX/MIN INDEX: `int maxIdx = 0; for(int i = 1; i < arr.length; i++) if(arr[i] > arr[maxIdx]) maxIdx = i; return maxIdx;`
        // Distinct from MAX/MIN VALUE: init is an integer literal and the body assigns the
        // loop variable (not arr[i]) to varName.
        if (isNonNegativeIntegerLiteral(init)
                && isLoopIndexAssignmentPattern(loop, varName)) {
            String iterableName = extractIterableName(loop);
            if (iterableName != null) {
                postconditions.add("\\result >= 0");
                postconditions.add("\\result < " + iterableName + ".length");
                // Matching invariants — needed both to discharge the postcondition AND
                // to prove the in-loop access `arr[varName]` stays in bounds.
                if (loop instanceof ForStmt fs && spec != null) {
                    int line = fs.getBegin().map(p -> p.line).orElse(0);
                    spec.addLoopInvariant(varName + " >= 0", line);
                    spec.addLoopInvariant(varName + " < " + iterableName + ".length", line);
                }
            }
            return;
        }

        // FACTORIAL-like: `T result = 1; for(int i = INIT; i <= n; i++) result *= i;`
        // Empty loop case is sound: when the upper bound is below INIT, result stays at 1.
        if (isIntegerLiteral(init, 1)
                && isLoopVarMultiplyAccumulator(loop, varName)) {
            String emptyCond = emptyLoopCondition(loop, methodDecl);
            if (emptyCond != null) {
                postconditions.add(emptyCond + " ==> \\result == 1");
            }
            return;
        }

        // FLAG-BASED EXISTS: `boolean found = false; for(...) if(P) found = true; return found;`
        // → \result == (\exists int k; 0 <= k && k < arr.length; P[arr[k]/arr[i]])
        if (isBooleanLiteral(init, false)
                && methodDecl.getType().toString().equals("boolean")) {
            ArrayPredicateGuard apg = identifyFlagSetPattern(loop, varName, methodDecl);
            if (apg != null) {
                String iterableName = extractIterableName(loop);
                if (iterableName != null) {
                    postconditions.add("\\result == (\\exists int k; 0 <= k && k < "
                            + iterableName + ".length; " + apg.arrayName + "[k] "
                            + opString(apg.matchOp) + " " + apg.targetExpr + ")");
                    // Matching invariant — without it the postcondition fails to verify
                    // because the prover has no link between `found` and the prefix
                    // [0, i). Sound at every iteration: found is true iff a matching
                    // element has already been seen.
                    if (loop instanceof ForStmt fs && spec != null) {
                        String counter = extractForCounterName(fs);
                        if (counter != null) {
                            int line = fs.getBegin().map(p -> p.line).orElse(0);
                            spec.addLoopInvariant(varName + " == (\\exists int k; 0 <= k && k < "
                                    + counter + "; " + apg.arrayName + "[k] "
                                    + opString(apg.matchOp) + " " + apg.targetExpr + ")", line);
                        }
                    }
                }
            }
            return;
        }
    }

    /**
     * Recognises a body shape {@code if (arr[i] OP target) varName = true;} where {@code i}
     * is the loop index. Returns the predicate guard, or null otherwise (any non-conforming
     * write to {@code varName} disqualifies the pattern).
     */
    private ArrayPredicateGuard identifyFlagSetPattern(Statement loop, String varName,
                                                         MethodDeclaration methodDecl) {
        Statement body = loopBody(loop);
        if (body == null) return null;
        ArrayPredicateGuard found = null;
        for (AssignExpr a : body.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) return null;
            if (a.getOperator() != AssignExpr.Operator.ASSIGN) return null;
            if (!isBooleanLiteral(a.getValue(), true)) return null;
            Optional<IfStmt> ifOpt = a.findAncestor(IfStmt.class);
            if (ifOpt.isEmpty()) return null;
            ArrayPredicateGuard apg = asArrayPredicateGuard(ifOpt.get().getCondition(), methodDecl);
            if (apg == null) return null;
            if (found != null) return null; // multiple sets — don't summarise
            found = apg;
        }
        for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
            if (u.getExpression() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) return null;
        }
        return found;
    }

    // -----------------------------------------------------------------------
    // Linear search
    // -----------------------------------------------------------------------

    private void analyzeLinearSearch(MethodDeclaration methodDecl, Set<String> postconditions,
                                       MethodSpecification spec) {
        // Two returns: one inside a loop (early exit on match), one after the loop (sentinel).
        List<ReturnStmt> returns = methodDecl.findAll(ReturnStmt.class);
        if (returns.size() != 2) return;

        ReturnStmt insideLoop = null;
        ReturnStmt afterLoop = null;
        for (ReturnStmt r : returns) {
            if (PreconditionAnalyzer.isInsideLoop(r)) insideLoop = r;
            else afterLoop = r;
        }
        if (insideLoop == null || afterLoop == null) return;
        if (insideLoop.getExpression().isEmpty() || afterLoop.getExpression().isEmpty()) return;

        Expression matchExpr = insideLoop.getExpression().get();
        Expression sentinelExpr = afterLoop.getExpression().get();

        // The early-exit return must be guarded by `arr[i] OP something`
        Optional<IfStmt> guard = insideLoop.findAncestor(IfStmt.class);
        if (guard.isEmpty()) return;
        Expression cond = guard.get().getCondition();

        ArrayPredicateGuard apg = asArrayPredicateGuard(cond, methodDecl);
        if (apg == null) return;

        // INDEX form: `return i;` where `i` is the loop index, and sentinel is a negative
        // integer literal (typically -1).
        if (matchExpr instanceof NameExpr returnedName
                && returnedName.getNameAsString().equals(apg.indexVar)
                && isNegativeIntegerLiteral(sentinelExpr)) {
            int sentinel = literalIntValue(sentinelExpr);
            postconditions.add("\\result >= " + sentinel);
            postconditions.add("\\result < " + apg.arrayName + ".length");
            // For == matches we can also assert arr[\result] satisfies the predicate.
            if (apg.matchOp == BinaryExpr.Operator.EQUALS) {
                postconditions.add("\\result == " + sentinel + " || " + apg.arrayName
                        + "[\\result] == " + apg.targetExpr);
            }
            // Matching "universal so far" invariant so the sentinel-return postcondition
            // and the arr[\result] == target postcondition can both discharge.
            BinaryExpr.Operator negated = negateRelOp(apg.matchOp);
            if (negated != null) {
                emitLinearSearchInvariant(insideLoop, apg, negated, spec);
            }
            return;
        }

        // BOOLEAN form: matching return is true/false, sentinel is the opposite.
        // (a) "any P": `if (P(arr[i])) return true; ... return false;`
        //     → \result == (\exists int k; 0 <= k && k < arr.length; arr[k] OP target)
        // (b) "all P": `if (!P(arr[i])) return false; ... return true;`
        //     The guard's OP is the NEGATED predicate, so the universal property uses the
        //     flipped operator over the same arr[k]/target. Emit both polarities so OpenJML
        //     can pick the form it can discharge.
        if (isBooleanLiteral(matchExpr, true) && isBooleanLiteral(sentinelExpr, false)) {
            postconditions.add("\\result == (\\exists int k; 0 <= k && k < " + apg.arrayName
                    + ".length; " + apg.arrayName + "[k] " + opString(apg.matchOp)
                    + " " + apg.targetExpr + ")");
            // Matching invariant: at iteration i, no earlier element has matched
            // (otherwise the early-return-true would have fired). The negated guard
            // operator is what holds for indices already iterated.
            BinaryExpr.Operator negated = negateRelOp(apg.matchOp);
            if (negated != null) {
                emitLinearSearchInvariant(insideLoop, apg, negated, spec);
            }
            return;
        }
        if (isBooleanLiteral(matchExpr, false) && isBooleanLiteral(sentinelExpr, true)) {
            // The early-exit guard fires when an element FAILS the universal property.
            // Universal property: every element satisfies the negation of the guard.
            BinaryExpr.Operator universalOp = negateRelOp(apg.matchOp);
            if (universalOp == null) return;
            postconditions.add("\\result == (\\forall int k; 0 <= k && k < " + apg.arrayName
                    + ".length; " + apg.arrayName + "[k] " + opString(universalOp)
                    + " " + apg.targetExpr + ")");
            // Matching invariant: at iteration i, every prefix element already
            // satisfies the universal property (otherwise we'd have early-returned false).
            emitLinearSearchInvariant(insideLoop, apg, universalOp, spec);
        }
    }

    // -----------------------------------------------------------------------
    // Pattern detection helpers
    // -----------------------------------------------------------------------

    private boolean isPlainAccumulator(Statement loop, String varName, AssignExpr.Operator op) {
        Statement body = loopBody(loop);
        if (body == null) return false;
        // The body must contain at least one `varName op= expr;` and no other writes to varName.
        boolean foundCorrect = false;
        for (AssignExpr a : body.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne)) continue;
            if (!ne.getNameAsString().equals(varName)) continue;
            if (a.getOperator() != op) return false;
            foundCorrect = true;
        }
        for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
            if (u.getExpression() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) {
                return false;
            }
        }
        return foundCorrect;
    }

    private boolean isConditionalIncrement(Statement loop, String varName) {
        Statement body = loopBody(loop);
        if (body == null) return false;
        boolean foundIncrement = false;
        for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
            if (!(u.getExpression() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) continue;
            if (u.getOperator() != UnaryExpr.Operator.POSTFIX_INCREMENT
                    && u.getOperator() != UnaryExpr.Operator.PREFIX_INCREMENT) return false;
            // Must be inside an if-stmt (conditional)
            if (u.findAncestor(IfStmt.class).isEmpty()) return false;
            foundIncrement = true;
        }
        for (AssignExpr a : body.findAll(AssignExpr.class)) {
            if (a.getTarget() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) {
                return false;
            }
        }
        return foundIncrement;
    }

    /**
     * Returns the comparison operator (GREATER for max, LESS for min) if the loop body looks
     * like {@code if (arr[i] OP varName) varName = arr[i];}; null otherwise.
     */
    private BinaryExpr.Operator identifyMaxMinPattern(Statement loop, String varName, String arrayName) {
        Statement body = loopBody(loop);
        if (body == null) return null;

        BinaryExpr.Operator detectedOp = null;

        for (AssignExpr a : body.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) return null;
            if (a.getOperator() != AssignExpr.Operator.ASSIGN) return null;
            // RHS should be `arr[i]` (an ArrayAccessExpr referencing arrayName)
            if (!(a.getValue() instanceof ArrayAccessExpr aa)) return null;
            if (!aa.getName().toString().equals(arrayName)) return null;
            // Must be inside an if whose condition compares arr[i] to varName
            Optional<IfStmt> ifOpt = a.findAncestor(IfStmt.class);
            if (ifOpt.isEmpty()) return null;
            Expression cond = ifOpt.get().getCondition();
            if (!(cond instanceof BinaryExpr be)) return null;
            BinaryExpr.Operator op = be.getOperator();
            String left = be.getLeft().toString();
            String right = be.getRight().toString();
            // Forms: arr[i] > max  OR  max < arr[i]
            boolean leftIsArrAccess = (be.getLeft() instanceof ArrayAccessExpr leftAA
                    && leftAA.getName().toString().equals(arrayName));
            boolean rightIsArrAccess = (be.getRight() instanceof ArrayAccessExpr rightAA
                    && rightAA.getName().toString().equals(arrayName));
            BinaryExpr.Operator effective;
            if (leftIsArrAccess && right.equals(varName)) effective = op;
            else if (rightIsArrAccess && left.equals(varName)) effective = flipOp(op);
            else return null;
            if (detectedOp != null && detectedOp != effective) return null;
            detectedOp = effective;
        }
        for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
            if (u.getExpression() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) return null;
        }
        return detectedOp;
    }

    private BinaryExpr.Operator flipOp(BinaryExpr.Operator op) {
        return switch (op) {
            case LESS -> BinaryExpr.Operator.GREATER;
            case LESS_EQUALS -> BinaryExpr.Operator.GREATER_EQUALS;
            case GREATER -> BinaryExpr.Operator.LESS;
            case GREATER_EQUALS -> BinaryExpr.Operator.LESS_EQUALS;
            default -> op;
        };
    }

    private void emitMaxEnsures(Set<String> postconditions, String arrayName, String low, String high) {
        postconditions.add("(\\exists int k; " + low + " <= k && k < " + high + "; \\result == "
                + arrayName + "[k])");
        postconditions.add("(\\forall int k; " + low + " <= k && k < " + high + "; \\result >= "
                + arrayName + "[k])");
    }

    private void emitMinEnsures(Set<String> postconditions, String arrayName, String low, String high) {
        postconditions.add("(\\exists int k; " + low + " <= k && k < " + high + "; \\result == "
                + arrayName + "[k])");
        postconditions.add("(\\forall int k; " + low + " <= k && k < " + high + "; \\result <= "
                + arrayName + "[k])");
    }

    /**
     * Emits the universal-so-far invariant needed by the boolean linear-search
     * pattern. The {@code insideLoopReturn} is the early-return statement; we walk
     * up to the enclosing for-loop and bind the loop counter into a {@code \forall}.
     */
    private void emitLinearSearchInvariant(ReturnStmt insideLoopReturn, ArrayPredicateGuard apg,
                                            BinaryExpr.Operator negatedOp, MethodSpecification spec) {
        if (spec == null) return;
        Optional<ForStmt> forOpt = insideLoopReturn.findAncestor(ForStmt.class);
        if (forOpt.isEmpty()) return;
        ForStmt fs = forOpt.get();
        String counter = extractForCounterName(fs);
        if (counter == null) return;
        int line = fs.getBegin().map(p -> p.line).orElse(0);
        spec.addLoopInvariant("(\\forall int k; 0 <= k && k < " + counter + "; "
                + apg.arrayName + "[k] " + opString(negatedOp) + " " + apg.targetExpr + ")", line);
    }

    /**
     * Emits the running max/min loop invariants needed to discharge the matching ensures
     * clauses. For a max loop (op = "&gt;="), invariants are:
     * <pre>
     *   (\forall int k; low &lt;= k &amp;&amp; k &lt; counter; varName &gt;= arr[k])
     *   (\exists int k; low &lt;= k &amp;&amp; k &lt; counter; varName == arr[k])
     * </pre>
     * The counter is the for-loop variable; absent a usable for-loop, no invariant is
     * emitted (the postcondition will then almost certainly fail to verify, but the
     * loop pattern was probably non-standard anyway).
     */
    private void emitMaxMinInvariants(Statement loop, String varName, String arrayName,
                                       String low, String op, MethodSpecification spec) {
        if (spec == null) return;
        if (!(loop instanceof ForStmt fs)) return;
        String counter = extractForCounterName(fs);
        if (counter == null) return;
        int line = fs.getBegin().map(p -> p.line).orElse(0);
        String forall = "(\\forall int k; " + low + " <= k && k < " + counter + "; "
                + varName + " " + op + " " + arrayName + "[k])";
        String exists = "(\\exists int k; " + low + " <= k && k < " + counter + "; "
                + varName + " == " + arrayName + "[k])";
        spec.addLoopInvariant(forall, line);
        spec.addLoopInvariant(exists, line);
    }

    /**
     * Returns the single declared loop-variable name from a for-loop's initialiser, or null
     * when the init isn't a single-variable declaration.
     */
    private String extractForCounterName(ForStmt fs) {
        if (fs.getInitialization().size() != 1) return null;
        Expression init = fs.getInitialization().get(0);
        if (!(init instanceof VariableDeclarationExpr vde)) return null;
        if (vde.getVariables().size() != 1) return null;
        return vde.getVariables().get(0).getNameAsString();
    }

    /**
     * Determines the [low, high) index range that the running max/min/index loop covers.
     * For {@code for(int i = X; i < Y; i++)} returns [aei.indexExpr, Y) provided both are
     * method-scope safe. Defaults to [0, arrayName.length) for the literal-0 init case.
     */
    private String[] inferIndexRange(Statement loop, ArrayElementInit aei, MethodDeclaration methodDecl) {
        SymbolicExecutor scope = new SymbolicExecutor();
        Set<String> paramNames = new LinkedHashSet<>();
        for (var p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());

        String low = aei.indexExpr;
        String high = aei.arrayName + ".length";

        if (loop instanceof ForStmt fs && fs.getCompare().isPresent()
                && fs.getCompare().get() instanceof BinaryExpr be
                && (be.getOperator() == BinaryExpr.Operator.LESS
                    || be.getOperator() == BinaryExpr.Operator.LESS_EQUALS)) {
            String r = be.getRight().toString();
            if (scope.isMethodScopeSafe(r, methodDecl, paramNames)) {
                high = r;
                if (be.getOperator() == BinaryExpr.Operator.LESS_EQUALS) {
                    high = "(" + r + " + 1)";
                }
            }
        }
        if (!scope.isMethodScopeSafe(low, methodDecl, paramNames)) return null;
        if (!scope.isMethodScopeSafe(high, methodDecl, paramNames)) return null;
        return new String[]{low, high};
    }

    // -----------------------------------------------------------------------
    // Tiny structural helpers
    // -----------------------------------------------------------------------

    private record ArrayElementInit(String arrayName, String indexExpr) {}
    private record ArrayMatchGuard(String arrayName, String indexVar, String targetExpr) {}
    private record ArrayPredicateGuard(String arrayName, String indexVar, String targetExpr,
                                       BinaryExpr.Operator matchOp) {}

    /**
     * Recognises {@code arr[idx]} (or {@code this.arr[idx]}) as the initialiser.
     * {@code idx} may be any method-scope-safe expression (literal {@code 0}, a parameter
     * like {@code start}, etc.).
     */
    private ArrayElementInit asArrayFirstElement(Expression init, MethodDeclaration methodDecl) {
        if (!(init instanceof ArrayAccessExpr aa)) return null;

        SymbolicExecutor scope = new SymbolicExecutor();
        Set<String> paramNames = new LinkedHashSet<>();
        for (var p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());
        String idxStr = aa.getIndex().toString();
        if (!scope.isMethodScopeSafe(idxStr, methodDecl, paramNames)) return null;

        Expression name = aa.getName();
        if (name instanceof NameExpr ne) return new ArrayElementInit(ne.getNameAsString(), idxStr);
        if (name instanceof FieldAccessExpr fa && fa.getScope().toString().equals("this")) {
            return new ArrayElementInit("this." + fa.getNameAsString(), idxStr);
        }
        return null;
    }

    /**
     * Recognises a guard of the form {@code arr[i] OP target} (or its mirror
     * {@code target OP arr[i]}) where OP is any of ==, !=, <, <=, >, >=,
     * {@code arr} is a parameter/field array, and {@code i} is a loop variable in scope.
     * Returns a record carrying the array name, index variable, target expression, and the
     * effective match operator ALWAYS oriented as {@code arr[i] OP target}.
     */
    private ArrayPredicateGuard asArrayPredicateGuard(Expression cond, MethodDeclaration methodDecl) {
        if (!(cond instanceof BinaryExpr be)) return null;
        BinaryExpr.Operator op = be.getOperator();
        if (!isComparisonOp(op)) return null;

        ArrayPredicateGuard g = matchPredicateSide(be.getLeft(), be.getRight(), op, methodDecl);
        if (g != null) return g;
        // mirror: target OP arr[i]  →  arr[i] flippedOp target
        return matchPredicateSide(be.getRight(), be.getLeft(), flipRelOp(op), methodDecl);
    }

    private ArrayPredicateGuard matchPredicateSide(Expression maybeArrAccess, Expression maybeTarget,
                                                    BinaryExpr.Operator op, MethodDeclaration methodDecl) {
        if (!(maybeArrAccess instanceof ArrayAccessExpr aa)) return null;
        Expression arrExpr = aa.getName();
        String arrayName;
        if (arrExpr instanceof NameExpr ne) arrayName = ne.getNameAsString();
        else if (arrExpr instanceof FieldAccessExpr fa && fa.getScope().toString().equals("this")) {
            arrayName = "this." + fa.getNameAsString();
        } else return null;

        if (!(aa.getIndex() instanceof NameExpr indexNe)) return null;
        String indexVar = indexNe.getNameAsString();

        SymbolicExecutor scope = new SymbolicExecutor();
        Set<String> paramNames = new LinkedHashSet<>();
        for (var p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());
        if (!scope.isMethodScopeSafe(maybeTarget.toString(), methodDecl, paramNames)) return null;

        return new ArrayPredicateGuard(arrayName, indexVar, maybeTarget.toString(), op);
    }

    private boolean isComparisonOp(BinaryExpr.Operator op) {
        return op == BinaryExpr.Operator.EQUALS || op == BinaryExpr.Operator.NOT_EQUALS
                || op == BinaryExpr.Operator.LESS || op == BinaryExpr.Operator.LESS_EQUALS
                || op == BinaryExpr.Operator.GREATER || op == BinaryExpr.Operator.GREATER_EQUALS;
    }

    private BinaryExpr.Operator flipRelOp(BinaryExpr.Operator op) {
        return switch (op) {
            case LESS -> BinaryExpr.Operator.GREATER;
            case LESS_EQUALS -> BinaryExpr.Operator.GREATER_EQUALS;
            case GREATER -> BinaryExpr.Operator.LESS;
            case GREATER_EQUALS -> BinaryExpr.Operator.LESS_EQUALS;
            default -> op; // ==, != are symmetric
        };
    }

    private BinaryExpr.Operator negateRelOp(BinaryExpr.Operator op) {
        return switch (op) {
            case EQUALS -> BinaryExpr.Operator.NOT_EQUALS;
            case NOT_EQUALS -> BinaryExpr.Operator.EQUALS;
            case LESS -> BinaryExpr.Operator.GREATER_EQUALS;
            case LESS_EQUALS -> BinaryExpr.Operator.GREATER;
            case GREATER -> BinaryExpr.Operator.LESS_EQUALS;
            case GREATER_EQUALS -> BinaryExpr.Operator.LESS;
            default -> null;
        };
    }

    private String opString(BinaryExpr.Operator op) {
        return switch (op) {
            case EQUALS -> "==";
            case NOT_EQUALS -> "!=";
            case LESS -> "<";
            case LESS_EQUALS -> "<=";
            case GREATER -> ">";
            case GREATER_EQUALS -> ">=";
            default -> op.asString();
        };
    }

    private boolean isNegativeIntegerLiteral(Expression expr) {
        if (expr.isUnaryExpr()) {
            UnaryExpr u = expr.asUnaryExpr();
            return u.getOperator() == UnaryExpr.Operator.MINUS
                    && u.getExpression().isIntegerLiteralExpr()
                    && u.getExpression().asIntegerLiteralExpr().asInt() > 0;
        }
        return expr.isIntegerLiteralExpr() && expr.asIntegerLiteralExpr().asInt() < 0;
    }

    private int literalIntValue(Expression expr) {
        if (expr.isIntegerLiteralExpr()) return expr.asIntegerLiteralExpr().asInt();
        if (expr.isUnaryExpr()) {
            UnaryExpr u = expr.asUnaryExpr();
            if (u.getOperator() == UnaryExpr.Operator.MINUS && u.getExpression().isIntegerLiteralExpr()) {
                return -u.getExpression().asIntegerLiteralExpr().asInt();
            }
        }
        return 0;
    }

    /**
     * Returns the iterable name (for-each) or the upper bound array name (for-i) of the loop
     * that drives this accumulator, or null if the loop's iteration bound isn't a clear
     * {@code arr.length} reference.
     */
    private String extractIterableName(Statement loop) {
        if (loop instanceof ForEachStmt fes) {
            return fes.getIterable().toString();
        }
        if (loop instanceof ForStmt fs && fs.getCompare().isPresent()) {
            Expression cmp = fs.getCompare().get();
            if (cmp instanceof BinaryExpr be) {
                String r = be.getRight().toString();
                if (r.endsWith(".length")) return r.substring(0, r.length() - ".length".length());
            }
        }
        return null;
    }

    /**
     * Returns the JML-friendly condition under which the loop body executes 0 times, or
     * null if it can't be expressed at method scope.
     *
     * For-each over {@code arr}: {@code arr.length == 0}.
     * For-i with single-variable initialiser and binary compare:
     *   {@code i < end} → {@code start >= end},
     *   {@code i <= end} → {@code start > end},
     *   {@code i > end} → {@code start <= end},
     *   {@code i >= end} → {@code start < end}.
     * Both {@code start} and {@code end} must be method-scope safe (no loop-locals).
     */
    /**
     * Wraps {@code condition} with not-null preconditions for any instance fields it
     * dereferences (e.g. {@code data.length} requires {@code this.data != null}).
     * Without these, a postcondition like {@code data.length == 0 ==> \result == 0}
     * is unprovable when the method has a {@code signals} clause for {@code data == null}
     * (the spec is checked against all states, not just the throw paths). Drives the
     * exception-flow split for ExcFlow2.sum.
     *
     * <p>If no field dereferences appear in the condition, returns the condition as-is.</p>
     */
    private String guardWithFieldNullChecks(String condition, MethodDeclaration methodDecl) {
        if (condition == null || condition.isEmpty()) return condition;
        Set<String> classFields = methodDecl.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .map(v -> v.getNameAsString())
                        .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new)))
                .orElseGet(LinkedHashSet::new);
        Set<String> referenceFields = methodDecl.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(cls -> cls.getFields().stream()
                        .filter(f -> {
                            String t = f.getCommonType().asString();
                            return t.endsWith("[]") || (!t.equals("int") && !t.equals("long")
                                    && !t.equals("short") && !t.equals("byte")
                                    && !t.equals("char") && !t.equals("boolean")
                                    && !t.equals("float") && !t.equals("double"));
                        })
                        .flatMap(f -> f.getVariables().stream())
                        .map(v -> v.getNameAsString())
                        .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new)))
                .orElseGet(LinkedHashSet::new);
        // Skip params with the same name (parameter shadows field).
        Set<String> paramNames = new LinkedHashSet<>();
        methodDecl.getParameters().forEach(p -> paramNames.add(p.getNameAsString()));

        List<String> nullGuards = new ArrayList<>();
        for (String f : referenceFields) {
            if (paramNames.contains(f)) continue;
            // Field is referenced if `f.` appears (with no preceding identifier char) in
            // the condition — captures both bare `f.length` and qualified `this.f.length`.
            java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                    "(?<![\\w.])" + java.util.regex.Pattern.quote(f) + "\\.");
            java.util.regex.Pattern pq = java.util.regex.Pattern.compile(
                    "this\\." + java.util.regex.Pattern.quote(f) + "\\.");
            if (p.matcher(condition).find() || pq.matcher(condition).find()) {
                nullGuards.add("this." + f + " != null");
            }
        }
        if (nullGuards.isEmpty()) return condition;
        return String.join(" && ", nullGuards) + " && " + condition;
    }

    private String emptyLoopCondition(Statement loop, MethodDeclaration methodDecl) {
        if (loop instanceof ForEachStmt fes) {
            String iterable = fes.getIterable().toString();
            return iterable + ".length == 0";
        }
        if (loop instanceof ForStmt fs && fs.getCompare().isPresent()) {
            // Need exactly one initialiser variable to read a `start` value
            String start = null;
            String iVar = null;
            for (Expression init : fs.getInitialization()) {
                if (init instanceof VariableDeclarationExpr vde) {
                    var vars = vde.getVariables();
                    if (vars.size() != 1) return null;
                    iVar = vars.get(0).getNameAsString();
                    if (vars.get(0).getInitializer().isEmpty()) return null;
                    start = vars.get(0).getInitializer().get().toString();
                }
            }
            if (start == null || iVar == null) return null;

            Expression cmp = fs.getCompare().get();
            return emptyConditionFromCompare(cmp, iVar, start, methodDecl);
        }
        if (loop instanceof WhileStmt ws) {
            // For a while loop we need: a single counter `i` declared with a literal start
            // before the loop, and a guard of the form `i OP boundary`. Locate the start by
            // walking siblings of the while statement upward, finding the most recent decl.
            Expression cond = ws.getCondition();
            if (!(cond instanceof BinaryExpr be)) return null;
            String left = be.getLeft().toString();
            String start = findRecentInitializerBefore(ws, left);
            if (start == null) return null;
            return emptyConditionFromCompare(cond, left, start, methodDecl);
        }
        return null;
    }

    /**
     * Returns the literal (or simple expression) initialiser of variable {@code varName}
     * declared in a sibling/ancestor before {@code beforeNode}, or null if not found.
     */
    private String findRecentInitializerBefore(com.github.javaparser.ast.Node beforeNode,
                                                String varName) {
        Optional<MethodDeclaration> methodOpt = beforeNode.findAncestor(MethodDeclaration.class);
        if (methodOpt.isEmpty()) return null;
        MethodDeclaration md = methodOpt.get();
        int beforeLine = beforeNode.getBegin().map(p -> p.line).orElse(Integer.MAX_VALUE);
        String found = null;
        int bestLine = -1;
        for (com.github.javaparser.ast.body.VariableDeclarator vd
                : md.findAll(com.github.javaparser.ast.body.VariableDeclarator.class)) {
            if (!vd.getNameAsString().equals(varName)) continue;
            if (vd.getInitializer().isEmpty()) continue;
            int vdLine = vd.getBegin().map(p -> p.line).orElse(-1);
            if (vdLine < 0 || vdLine >= beforeLine) continue;
            if (vdLine > bestLine) {
                bestLine = vdLine;
                found = vd.getInitializer().get().toString();
            }
        }
        return found;
    }

    private String emptyConditionFromCompare(Expression cmp, String iVar, String start,
                                              MethodDeclaration methodDecl) {
        if (!(cmp instanceof BinaryExpr be)) return null;
        String left = be.getLeft().toString();
        if (!left.equals(iVar)) return null;
        String end = be.getRight().toString();

        SymbolicExecutor scope = new SymbolicExecutor();
        Set<String> paramNames = new LinkedHashSet<>();
        for (var p : methodDecl.getParameters()) paramNames.add(p.getNameAsString());
        if (!scope.isMethodScopeSafe(start, methodDecl, paramNames)) return null;
        if (!scope.isMethodScopeSafe(end, methodDecl, paramNames)) return null;

        return switch (be.getOperator()) {
            case LESS -> start + " >= " + end;
            case LESS_EQUALS -> start + " > " + end;
            case GREATER -> start + " <= " + end;
            case GREATER_EQUALS -> start + " < " + end;
            default -> null;
        };
    }

    /**
     * Recognises the body shape {@code if (...) varName = i;} where {@code i} is the loop
     * variable -- typical of "find max-by-index" and "find min-by-index" patterns.
     */
    private boolean isLoopIndexAssignmentPattern(Statement loop, String varName) {
        if (!(loop instanceof ForStmt fs)) return false;
        // Identify the loop variable
        String iVar = null;
        for (Expression init : fs.getInitialization()) {
            if (init instanceof VariableDeclarationExpr vde && vde.getVariables().size() == 1) {
                iVar = vde.getVariables().get(0).getNameAsString();
            }
        }
        if (iVar == null) return false;
        Statement body = fs.getBody();
        boolean foundCorrect = false;
        for (AssignExpr a : body.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) return false;
            if (a.getOperator() != AssignExpr.Operator.ASSIGN) return false;
            if (!(a.getValue() instanceof NameExpr rhs) || !rhs.getNameAsString().equals(iVar)) return false;
            if (a.findAncestor(IfStmt.class).isEmpty()) return false;
            foundCorrect = true;
        }
        for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
            if (u.getExpression() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) return false;
        }
        return foundCorrect;
    }

    /**
     * Recognises the body shape {@code varName *= i;} where {@code i} is the for-loop
     * variable — characteristic of factorial-style products.
     */
    private boolean isLoopVarMultiplyAccumulator(Statement loop, String varName) {
        if (!(loop instanceof ForStmt fs)) return false;
        String iVar = null;
        for (Expression init : fs.getInitialization()) {
            if (init instanceof VariableDeclarationExpr vde && vde.getVariables().size() == 1) {
                iVar = vde.getVariables().get(0).getNameAsString();
            }
        }
        if (iVar == null) return false;
        Statement body = fs.getBody();
        boolean foundCorrect = false;
        for (AssignExpr a : body.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) return false;
            if (a.getOperator() != AssignExpr.Operator.MULTIPLY) return false;
            if (!(a.getValue() instanceof NameExpr rhs) || !rhs.getNameAsString().equals(iVar)) return false;
            foundCorrect = true;
        }
        for (UnaryExpr u : body.findAll(UnaryExpr.class)) {
            if (u.getExpression() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) return false;
        }
        return foundCorrect;
    }

    private boolean isNonNegativeIntegerLiteral(Expression expr) {
        return expr.isIntegerLiteralExpr() && expr.asIntegerLiteralExpr().asInt() >= 0;
    }

    private List<Statement> findLoopsModifying(MethodDeclaration methodDecl, String varName) {
        // Return the OUTERMOST enclosing loop for each modification — i.e. the iteration
        // driver. For nested loops (`for(i) for(j) sum += a[i][j]`) the empty-loop case is
        // governed by the outer loop, not the inner one.
        Set<Statement> loops = new LinkedHashSet<>();
        for (AssignExpr a : methodDecl.findAll(AssignExpr.class)) {
            if (!(a.getTarget() instanceof NameExpr ne) || !ne.getNameAsString().equals(varName)) continue;
            findOutermostEnclosingLoop(a, methodDecl).ifPresent(loops::add);
        }
        for (UnaryExpr u : methodDecl.findAll(UnaryExpr.class)) {
            if (u.getExpression() instanceof NameExpr ne && ne.getNameAsString().equals(varName)) {
                findOutermostEnclosingLoop(u, methodDecl).ifPresent(loops::add);
            }
        }
        return new ArrayList<>(loops);
    }

    private Optional<Statement> findOutermostEnclosingLoop(com.github.javaparser.ast.Node node,
                                                            MethodDeclaration boundary) {
        com.github.javaparser.ast.Node cur = node;
        Statement outermost = null;
        while (cur.getParentNode().isPresent()) {
            cur = cur.getParentNode().get();
            if (cur == boundary) break;
            if (cur instanceof ForStmt || cur instanceof ForEachStmt
                    || cur instanceof WhileStmt || cur instanceof DoStmt) {
                outermost = (Statement) cur;
            }
        }
        return Optional.ofNullable(outermost);
    }

    private Statement loopBody(Statement loop) {
        if (loop instanceof ForStmt fs) return fs.getBody();
        if (loop instanceof ForEachStmt fes) return fes.getBody();
        if (loop instanceof WhileStmt ws) return ws.getBody();
        if (loop instanceof DoStmt ds) return ds.getBody();
        return null;
    }

    private VariableDeclarator findDeclarator(MethodDeclaration methodDecl, String varName) {
        for (VariableDeclarator vd : methodDecl.findAll(VariableDeclarator.class)) {
            if (vd.getNameAsString().equals(varName)) return vd;
        }
        return null;
    }

    private boolean isIntegerLiteral(Expression expr, int value) {
        if (expr.isIntegerLiteralExpr()) return expr.asIntegerLiteralExpr().asInt() == value;
        if (expr.isUnaryExpr()) {
            UnaryExpr u = expr.asUnaryExpr();
            if (u.getOperator() == UnaryExpr.Operator.MINUS && u.getExpression().isIntegerLiteralExpr()) {
                return -u.getExpression().asIntegerLiteralExpr().asInt() == value;
            }
        }
        return false;
    }

    private boolean isBooleanLiteral(Expression expr, boolean value) {
        return expr.isBooleanLiteralExpr() && expr.asBooleanLiteralExpr().getValue() == value;
    }
}
