package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.jml.inferrer.model.MethodSpecification;

import java.util.*;

/**
 * Recognises the binary-search shape and emits the bounds preconditions and loop
 * invariants needed to discharge OpenJML's {@code arr[mid]} index obligations.
 *
 * <h3>Pattern</h3>
 * <pre>{@code
 *   while (lo OP hi) {                      // OP in <, <=
 *       int mid = lo + (hi - lo) / 2;       // or (lo + hi) / 2
 *       ...arr[mid]...
 *       lo = mid + 1; / hi = mid - 1; / hi = mid;
 *   }
 * }</pre>
 *
 * <h3>Two variants</h3>
 * <ol>
 *   <li><b>Local-bound</b>: {@code lo}, {@code hi} are local declarations
 *       initialised to {@code 0} / {@code arr.length - 1} respectively. Emits only
 *       loop invariants — the bounds hold by construction at loop entry.</li>
 *   <li><b>Parameter-bound</b>: {@code lo}, {@code hi} are method parameters.
 *       Emits both preconditions ({@code 0 <= lo && lo <= hi+1 && hi < arr.length})
 *       and matching loop invariants.</li>
 * </ol>
 *
 * <p>Soundness note: at the back-edge after {@code lo = mid + 1}, {@code lo} can
 * become {@code hi + 1} when {@code mid == hi}. The invariant {@code lo <= hi + 1}
 * (rather than {@code lo <= hi}) accounts for this.</p>
 */
class BinarySearchPatternAnalyzer {

    void analyze(MethodDeclaration methodDecl, MethodSpecification spec) {
        if (methodDecl.getBody().isEmpty()) return;

        Set<String> paramNames = new LinkedHashSet<>();
        Set<String> arrayParams = new LinkedHashSet<>();
        for (Parameter p : methodDecl.getParameters()) {
            paramNames.add(p.getNameAsString());
            if (p.getType().asString().contains("[]")) {
                arrayParams.add(p.getNameAsString());
            }
        }

        for (WhileStmt ws : methodDecl.findAll(WhileStmt.class)) {
            BinarySearchShape shape = recogniseBinarySearch(ws, methodDecl, paramNames, arrayParams);
            if (shape == null) continue;
            emitInvariantsAndPreconditions(shape, ws, methodDecl, spec);
        }
    }

    /**
     * Returns a BinarySearchShape if the loop matches the binary-search pattern,
     * otherwise null. Match requires:
     * <ul>
     *   <li>guard {@code lo OP hi} with OP in {@code <, <=}</li>
     *   <li>body assigning {@code mid = lo + (hi - lo) / 2} or {@code (lo + hi) / 2}</li>
     *   <li>at least one access to a recognised array at {@code arr[mid]}</li>
     * </ul>
     */
    private BinarySearchShape recogniseBinarySearch(WhileStmt ws, MethodDeclaration methodDecl,
                                                     Set<String> paramNames, Set<String> arrayParams) {
        if (!(ws.getCondition() instanceof BinaryExpr cond)) return null;
        BinaryExpr.Operator op = cond.getOperator();
        if (op != BinaryExpr.Operator.LESS && op != BinaryExpr.Operator.LESS_EQUALS) return null;
        if (!(cond.getLeft() instanceof NameExpr loNe)) return null;
        if (!(cond.getRight() instanceof NameExpr hiNe)) return null;
        String lo = loNe.getNameAsString();
        String hi = hiNe.getNameAsString();
        if (lo.equals(hi)) return null;

        // Find `int mid = lo + (hi - lo) / 2` or `int mid = (lo + hi) / 2` in body
        String mid = findMidpointName(ws, lo, hi);
        if (mid == null) return null;

        // Find arr[mid] access on a known array (param or field)
        String arrayName = findArrayAccessedAtMid(ws, mid, arrayParams, methodDecl);
        if (arrayName == null) return null;

        // Determine the source of lo/hi
        boolean loIsParam = paramNames.contains(lo);
        boolean hiIsParam = paramNames.contains(hi);

        String loInitExpr = loIsParam ? null : findLocalInit(methodDecl, lo);
        String hiInitExpr = hiIsParam ? null : findLocalInit(methodDecl, hi);

        BinarySearchShape shape = new BinarySearchShape();
        shape.lo = lo;
        shape.hi = hi;
        shape.mid = mid;
        shape.arrayName = arrayName;
        shape.loIsParam = loIsParam;
        shape.hiIsParam = hiIsParam;
        shape.loInitExpr = loInitExpr;
        shape.hiInitExpr = hiInitExpr;
        return shape;
    }

    /**
     * Walks the loop body for the first {@code int mid = lo + (hi - lo) / 2} or
     * {@code int mid = (lo + hi) / 2} declaration. Returns {@code mid}'s name, or
     * null if no such midpoint expression is found.
     */
    private String findMidpointName(WhileStmt ws, String lo, String hi) {
        for (VariableDeclarationExpr vde : ws.getBody().findAll(VariableDeclarationExpr.class)) {
            for (VariableDeclarator vd : vde.getVariables()) {
                if (vd.getInitializer().isEmpty()) continue;
                Expression init = vd.getInitializer().get();
                if (isMidpointExpr(init, lo, hi)) {
                    return vd.getNameAsString();
                }
            }
        }
        return null;
    }

    /**
     * True when {@code expr} matches one of the canonical midpoint shapes:
     * <ul>
     *   <li>{@code lo + (hi - lo) / 2}</li>
     *   <li>{@code (lo + hi) / 2}</li>
     * </ul>
     */
    private boolean isMidpointExpr(Expression expr, String lo, String hi) {
        if (expr instanceof EnclosedExpr en) return isMidpointExpr(en.getInner(), lo, hi);

        // Shape 1: lo + (hi - lo) / 2
        if (expr instanceof BinaryExpr be && be.getOperator() == BinaryExpr.Operator.PLUS) {
            if (be.getLeft() instanceof NameExpr loN && loN.getNameAsString().equals(lo)) {
                Expression right = unwrap(be.getRight());
                if (right instanceof BinaryExpr div && div.getOperator() == BinaryExpr.Operator.DIVIDE
                        && div.getRight().isIntegerLiteralExpr()
                        && div.getRight().asIntegerLiteralExpr().asInt() == 2) {
                    Expression sub = unwrap(div.getLeft());
                    if (sub instanceof BinaryExpr subBe
                            && subBe.getOperator() == BinaryExpr.Operator.MINUS
                            && subBe.getLeft() instanceof NameExpr hiN && hiN.getNameAsString().equals(hi)
                            && subBe.getRight() instanceof NameExpr loN2 && loN2.getNameAsString().equals(lo)) {
                        return true;
                    }
                }
            }
        }

        // Shape 2: (lo + hi) / 2
        if (expr instanceof BinaryExpr div && div.getOperator() == BinaryExpr.Operator.DIVIDE
                && div.getRight().isIntegerLiteralExpr()
                && div.getRight().asIntegerLiteralExpr().asInt() == 2) {
            Expression sum = unwrap(div.getLeft());
            if (sum instanceof BinaryExpr sumBe && sumBe.getOperator() == BinaryExpr.Operator.PLUS) {
                String l = sumBe.getLeft().toString();
                String r = sumBe.getRight().toString();
                if ((l.equals(lo) && r.equals(hi)) || (l.equals(hi) && r.equals(lo))) {
                    return true;
                }
            }
        }
        return false;
    }

    private Expression unwrap(Expression e) {
        while (e instanceof EnclosedExpr en) e = en.getInner();
        return e;
    }

    /**
     * Returns the array (param) name on which {@code arr[mid]} is accessed inside the
     * loop body, or null if no such access exists. Tries parameters first; class fields
     * second.
     */
    private String findArrayAccessedAtMid(WhileStmt ws, String mid, Set<String> arrayParams,
                                           MethodDeclaration methodDecl) {
        for (ArrayAccessExpr aae : ws.getBody().findAll(ArrayAccessExpr.class)) {
            if (!(aae.getIndex() instanceof NameExpr midNe)) continue;
            if (!midNe.getNameAsString().equals(mid)) continue;
            // Param array
            if (aae.getName() instanceof NameExpr arrNe && arrayParams.contains(arrNe.getNameAsString())) {
                return arrNe.getNameAsString();
            }
            // Field array
            if (aae.getName() instanceof FieldAccessExpr fa && fa.getScope().toString().equals("this")) {
                return "this." + fa.getNameAsString();
            }
            if (aae.getName() instanceof NameExpr arrNe2
                    && AnalysisUtils.isFieldReference(methodDecl, arrNe2.getNameAsString())) {
                return "this." + arrNe2.getNameAsString();
            }
        }
        return null;
    }

    /**
     * Looks up the most recent local-variable initialiser for {@code name} in the
     * enclosing method. Returns the initialiser expression (as a string), or null
     * if the variable has no initialiser or isn't a local in this method.
     */
    private String findLocalInit(MethodDeclaration methodDecl, String name) {
        if (methodDecl.getBody().isEmpty()) return null;
        for (VariableDeclarator vd : methodDecl.getBody().get().findAll(VariableDeclarator.class)) {
            if (vd.getNameAsString().equals(name) && vd.getInitializer().isPresent()) {
                return vd.getInitializer().get().toString();
            }
        }
        return null;
    }

    /**
     * Emits the bounds preconditions (when lo/hi are parameters) and the loop
     * invariants needed for OpenJML to discharge {@code arr[mid]} index obligations.
     *
     * <p>The invariants are the inductive lifting of the preconditions: at every
     * iteration of the loop, {@code 0 <= lo && lo <= hi + 1 && hi <= arr.length - 1}
     * (using {@code hi + 1} because {@code lo = mid + 1} can push {@code lo} to
     * exactly {@code hi + 1} on the back-edge).</p>
     */
    private void emitInvariantsAndPreconditions(BinarySearchShape shape, WhileStmt ws,
                                                  MethodDeclaration methodDecl,
                                                  MethodSpecification spec) {
        String lo = shape.lo;
        String hi = shape.hi;
        String arr = shape.arrayName;
        String arrLen = arr + ".length";

        // Determine the loop ordinal so invariants attach to the right loop
        int loopOrdinal = computeLoopOrdinal(methodDecl, ws);

        // Preconditions for parameter lo/hi
        if (shape.loIsParam) {
            spec.addPrecondition("0 <= " + lo, MethodSpecification.ConfidenceLevel.HIGH);
        }
        if (shape.loIsParam && shape.hiIsParam) {
            // Allow lo == hi + 1 at exit only (loop entry needs lo <= hi or lo < hi)
            // Match the exit condition of the loop body.
            spec.addPrecondition(lo + " <= " + hi + " + 1",
                    MethodSpecification.ConfidenceLevel.HIGH);
        }
        if (shape.hiIsParam) {
            // hi must be a valid index OR hi + 1 == 0 (i.e. hi == -1 at exit when array empty)
            // For binary search with strict guard `lo < hi` and update `hi = mid`, this is
            // less strict, but `hi <= arr.length - 1` is the canonical bound.
            spec.addPrecondition(hi + " <= " + arrLen + " - 1",
                    MethodSpecification.ConfidenceLevel.HIGH);
        }

        // Loop invariants — always emit. For local lo (init = 0) and local hi (init =
        // arr.length - 1), the invariants are sound at loop entry by construction.
        // For parameter lo/hi, the matching preconditions above ensure entry validity.
        spec.addLoopInvariant("0 <= " + lo, loopOrdinal);
        spec.addLoopInvariant(lo + " <= " + hi + " + 1", loopOrdinal);
        spec.addLoopInvariant(hi + " <= " + arrLen + " - 1", loopOrdinal);
    }

    /**
     * Computes the document-order ordinal of {@code targetWs} among all loops in
     * {@code methodDecl}. The {@link LoopInvariantAnalyzer.LoopInvariantVisitor}
     * uses the same ordering when emitting its own invariants.
     */
    private int computeLoopOrdinal(MethodDeclaration methodDecl, WhileStmt targetWs) {
        if (methodDecl.getBody().isEmpty()) return 0;
        int ordinal = 0;
        for (Statement s : methodDecl.getBody().get().findAll(Statement.class)) {
            if (s instanceof ForStmt || s instanceof WhileStmt
                    || s instanceof ForEachStmt || s instanceof DoStmt) {
                if (s == targetWs) return ordinal;
                ordinal++;
            }
        }
        return ordinal;
    }

    /**
     * Captures the recognised binary-search structure: the names of the lo/hi/mid
     * variables, the underlying array's name, and whether lo/hi are parameters
     * (which determines whether to emit preconditions).
     */
    private static class BinarySearchShape {
        String lo;
        String hi;
        String mid;
        String arrayName;
        boolean loIsParam;
        boolean hiIsParam;
        String loInitExpr;
        String hiInitExpr;
    }
}
