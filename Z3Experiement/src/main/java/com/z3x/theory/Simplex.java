package com.z3x.theory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Dutertre & de Moura general Simplex for DPLL(T): each variable carries a current value and
 * lower/upper bounds. Basic variables are expressed as linear combinations of non-basics
 * via a tableau, and we pivot when a basic violates its bound.
 *
 * Variables are referred to by integer ids assigned by {@link #addVariable(boolean)}.
 * The first variables are normally "external" (one per arithmetic term in the input);
 * fresh basic variables are introduced as needed for compound expressions.
 *
 * Bounds are pushed via {@link #pushBound} and undone with {@link #pushLevel}/{@link #popLevel}.
 *
 * On {@link #check()} we attempt to bring all basic variables inside their bounds. Returns
 * {@code null} on success, or a list of bound-ids whose conjunction is unsatisfiable on failure
 * (the standard "explanation by Farkas" extracted from the failing pivot row).
 */
public final class Simplex {

    /** Per-variable state. */
    private static final class Var {
        Rational value = Rational.ZERO;
        Rational lower = null; // null = -infinity
        Rational upper = null; // null = +infinity
        /** Bound-id (literal) backing the current lower/upper, or 0 if none. */
        int lowerReason = 0;
        int upperReason = 0;
        boolean basic;
        /** Row coefficients if basic: var-id -> coefficient. */
        LinkedHashMap<Integer, Rational> row;
    }

    private final List<Var> vars = new ArrayList<>();

    /** Trail of undoable events. */
    private interface Event { void undo(); }
    private final List<Event> trail = new ArrayList<>();
    private final List<Integer> levelMarks = new ArrayList<>();

    /** Conflict explanation populated when {@link #check()} returns false. */
    public int[] lastConflict;

    /** Allocate a new variable. {@code basic=false} means non-basic by default. */
    public int addVariable(boolean basic) {
        Var v = new Var();
        v.basic = basic;
        if (basic) v.row = new LinkedHashMap<>();
        vars.add(v);
        return vars.size() - 1;
    }

    public int numVars() { return vars.size(); }

    /** Make a basic variable equal to a linear combination of others (on creation). */
    public void defineBasic(int basicId, Map<Integer, Rational> coeffs) {
        Var b = vars.get(basicId);
        if (!b.basic) throw new IllegalStateException("not basic: " + basicId);
        b.row.clear();
        for (Map.Entry<Integer, Rational> e : coeffs.entrySet()) {
            if (!e.getValue().isZero()) b.row.put(e.getKey(), e.getValue());
        }
        recomputeBasicValue(basicId);
    }

    public Rational valueOf(int v) { return vars.get(v).value; }

    public void pushLevel() { levelMarks.add(trail.size()); }

    public void popLevel() {
        if (levelMarks.isEmpty()) return;
        int mark = levelMarks.remove(levelMarks.size() - 1);
        while (trail.size() > mark) trail.remove(trail.size() - 1).undo();
    }

    /** Discard the most-recent {@link #pushLevel} mark without undoing any trail events.
     *  Effectively merges the most recent pushed level into its parent — useful when a sub-check
     *  has succeeded and its bounds should persist as part of the outer scope. */
    public void discardLastLevel() {
        if (!levelMarks.isEmpty()) levelMarks.remove(levelMarks.size() - 1);
    }

    /** Push a lower bound {@code v >= bound} backed by literal {@code reason}. */
    public boolean pushLower(int vId, Rational bound, int reason) {
        Var v = vars.get(vId);
        if (v.upper != null && bound.gt(v.upper)) {
            lastConflict = new int[] { reason, v.upperReason };
            return false;
        }
        if (v.lower != null && bound.le(v.lower)) {
            return true; // weaker, ignore
        }
        Rational oldLower = v.lower;
        int oldReason = v.lowerReason;
        Rational oldValue = v.value;
        v.lower = bound;
        v.lowerReason = reason;
        if (!v.basic && v.value.lt(bound)) {
            update(vId, bound);
        }
        trail.add(() -> {
            v.lower = oldLower;
            v.lowerReason = oldReason;
            if (!v.basic) v.value = oldValue;
        });
        return true;
    }

    /** Push an upper bound {@code v <= bound} backed by literal {@code reason}. */
    public boolean pushUpper(int vId, Rational bound, int reason) {
        Var v = vars.get(vId);
        if (v.lower != null && bound.lt(v.lower)) {
            lastConflict = new int[] { reason, v.lowerReason };
            return false;
        }
        if (v.upper != null && bound.ge(v.upper)) {
            return true;
        }
        Rational oldUpper = v.upper;
        int oldReason = v.upperReason;
        Rational oldValue = v.value;
        v.upper = bound;
        v.upperReason = reason;
        if (!v.basic && v.value.gt(bound)) {
            update(vId, bound);
        }
        trail.add(() -> {
            v.upper = oldUpper;
            v.upperReason = oldReason;
            if (!v.basic) v.value = oldValue;
        });
        return true;
    }

    /** Update the value of non-basic v to delta, propagating to dependent basic rows. */
    private void update(int vId, Rational newVal) {
        Var v = vars.get(vId);
        Rational diff = newVal.sub(v.value);
        v.value = newVal;
        for (int j = 0; j < vars.size(); j++) {
            Var b = vars.get(j);
            if (!b.basic) continue;
            Rational a = b.row.get(vId);
            if (a == null) continue;
            b.value = b.value.add(a.mul(diff));
        }
    }

    private void recomputeBasicValue(int bId) {
        Var b = vars.get(bId);
        Rational acc = Rational.ZERO;
        for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
            acc = acc.add(e.getValue().mul(vars.get(e.getKey()).value));
        }
        b.value = acc;
    }

    /** Pivot: swap basic and non-basic, rewriting the row that contains them. */
    private void pivot(int basicId, int nonBasicId) {
        Var b = vars.get(basicId);
        Var n = vars.get(nonBasicId);
        Rational a = b.row.remove(nonBasicId);
        if (a == null) throw new IllegalStateException("pivot called with non-basic not in basic row");
        // basic row was: x_b = sum_k c_k x_k + a x_n. Solve for x_n.
        // x_n = (1/a)(x_b - sum_k c_k x_k)
        LinkedHashMap<Integer, Rational> newNonBasicRow = new LinkedHashMap<>();
        Rational invA = Rational.ONE.div(a);
        newNonBasicRow.put(basicId, invA);
        for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
            newNonBasicRow.put(e.getKey(), e.getValue().negate().mul(invA));
        }
        // Substitute n in all other basic rows.
        for (int j = 0; j < vars.size(); j++) {
            if (j == basicId) continue;
            Var v = vars.get(j);
            if (!v.basic) continue;
            Rational c = v.row.get(nonBasicId);
            if (c == null) continue;
            v.row.remove(nonBasicId);
            for (Map.Entry<Integer, Rational> e : newNonBasicRow.entrySet()) {
                Rational add = c.mul(e.getValue());
                Rational existing = v.row.get(e.getKey());
                Rational sum = existing == null ? add : existing.add(add);
                if (sum.isZero()) v.row.remove(e.getKey());
                else v.row.put(e.getKey(), sum);
            }
        }
        // Swap basic / non-basic flags.
        b.basic = false;
        b.row = null;
        n.basic = true;
        n.row = newNonBasicRow;
    }

    /** Pivot and update in one step: x_b moves to {@code newVbasic}, then we pivot on x_b/x_n. */
    private void pivotAndUpdate(int basicId, int nonBasicId, Rational newBasicValue) {
        Var b = vars.get(basicId);
        Rational a = b.row.get(nonBasicId);
        Rational diff = newBasicValue.sub(b.value).div(a);
        Var n = vars.get(nonBasicId);
        Rational newN = n.value.add(diff);
        // Update value of n and propagate to all basics' values.
        for (int j = 0; j < vars.size(); j++) {
            Var v = vars.get(j);
            if (!v.basic) continue;
            Rational c = v.row.get(nonBasicId);
            if (c == null) continue;
            v.value = v.value.add(c.mul(diff));
        }
        n.value = newN;
        b.value = newBasicValue;
        pivot(basicId, nonBasicId);
    }

    /**
     * Run the Bland-rule pivoting search: while some basic violates its bound, find a non-basic
     * that can be moved to fix it. If none, the violating row is a Farkas-style conflict.
     * Returns true on success; populates {@link #lastConflict} on failure.
     */
    public boolean check() {
        for (int safety = 0; safety < 100_000; safety++) {
            int badBasic = -1;
            boolean tooLow = false;
            // Bland's rule: pick the lowest-id basic violating bounds.
            for (int i = 0; i < vars.size(); i++) {
                Var v = vars.get(i);
                if (!v.basic) continue;
                if (v.lower != null && v.value.lt(v.lower)) { badBasic = i; tooLow = true; break; }
                if (v.upper != null && v.value.gt(v.upper)) { badBasic = i; tooLow = false; break; }
            }
            if (badBasic == -1) return true; // all bounds satisfied
            Var b = vars.get(badBasic);
            // Find a suitable non-basic to pivot with.
            int chosen = -1;
            for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
                int nb = e.getKey();
                Rational a = e.getValue();
                Var n = vars.get(nb);
                if (tooLow) {
                    // Need to increase b.value. pivot delta sign = sign(a).
                    if (a.signum() > 0 && (n.upper == null || n.value.lt(n.upper))) { chosen = nb; break; }
                    if (a.signum() < 0 && (n.lower == null || n.value.gt(n.lower))) { chosen = nb; break; }
                } else {
                    if (a.signum() > 0 && (n.lower == null || n.value.gt(n.lower))) { chosen = nb; break; }
                    if (a.signum() < 0 && (n.upper == null || n.value.lt(n.upper))) { chosen = nb; break; }
                }
            }
            if (chosen == -1) {
                // No pivot — extract conflict explanation.
                buildConflict(badBasic, tooLow);
                return false;
            }
            Rational newBasicValue = tooLow ? b.lower : b.upper;
            pivotAndUpdate(badBasic, chosen, newBasicValue);
        }
        // Ran out of pivots — should not happen; declare unknown via empty conflict.
        lastConflict = new int[0];
        return false;
    }

    private void buildConflict(int badBasic, boolean tooLow) {
        Var b = vars.get(badBasic);
        List<Integer> reasons = new ArrayList<>();
        if (tooLow && b.lowerReason != 0) reasons.add(b.lowerReason);
        if (!tooLow && b.upperReason != 0) reasons.add(b.upperReason);
        for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
            int nb = e.getKey();
            Var n = vars.get(nb);
            Rational a = e.getValue();
            // Whichever bound prevents us from using nb in the desired direction.
            if (tooLow) {
                if (a.signum() > 0) {
                    if (n.upperReason != 0) reasons.add(n.upperReason);
                } else {
                    if (n.lowerReason != 0) reasons.add(n.lowerReason);
                }
            } else {
                if (a.signum() > 0) {
                    if (n.lowerReason != 0) reasons.add(n.lowerReason);
                } else {
                    if (n.upperReason != 0) reasons.add(n.upperReason);
                }
            }
        }
        int[] arr = new int[reasons.size()];
        for (int i = 0; i < arr.length; i++) arr[i] = reasons.get(i);
        lastConflict = arr;
    }

    /** Quick visibility for tests. */
    public Rational lowerOf(int v) { return vars.get(v).lower; }
    public Rational upperOf(int v) { return vars.get(v).upper; }
    public boolean isBasic(int v) { return vars.get(v).basic; }
}
