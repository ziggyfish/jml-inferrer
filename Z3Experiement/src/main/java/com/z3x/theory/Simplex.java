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

    /** Inverted index as IntList (avoids Integer boxing). For each non-basic var id, the list of
     *  basic var ids whose row references it. The remove(int) implementation is O(n) — fine because
     *  rows are sparse and removed-basic count per non-basic stays small. */
    private final List<IntList> usedIn = new ArrayList<>();

    private static final class IntList {
        int[] data = new int[4];
        int size = 0;
        void add(int v) {
            if (size == data.length) {
                int[] n = new int[data.length * 2];
                System.arraycopy(data, 0, n, 0, size);
                data = n;
            }
            data[size++] = v;
        }
        boolean remove(int v) {
            for (int i = 0; i < size; i++) {
                if (data[i] == v) {
                    System.arraycopy(data, i + 1, data, i, size - i - 1);
                    size--;
                    return true;
                }
            }
            return false;
        }
        int[] snapshot() {
            int[] out = new int[size];
            System.arraycopy(data, 0, out, 0, size);
            return out;
        }
    }

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
        usedIn.add(new IntList());
        return vars.size() - 1;
    }

    public int numVars() { return vars.size(); }

    /** Make a basic variable equal to a linear combination of others (on creation).
     *  If any coefficient references a variable that is currently basic, substitute that
     *  variable's row in. Otherwise simplex invariants would be violated (basic rows must be
     *  expressed over non-basics only). */
    public void defineBasic(int basicId, Map<Integer, Rational> coeffs) {
        Var b = vars.get(basicId);
        if (!b.basic) throw new IllegalStateException("not basic: " + basicId);
        if (!b.row.isEmpty()) {
            for (Integer nb : b.row.keySet()) usedIn.get(nb).remove(basicId);
        }
        b.row.clear();
        // Expand basic-referencing entries.
        LinkedHashMap<Integer, Rational> expanded = new LinkedHashMap<>();
        for (Map.Entry<Integer, Rational> e : coeffs.entrySet()) {
            int v = e.getKey();
            Rational c = e.getValue();
            if (c.isZero()) continue;
            Var nv = vars.get(v);
            if (nv.basic && v != basicId) {
                // substitute nv's row scaled by c
                for (Map.Entry<Integer, Rational> sub : nv.row.entrySet()) {
                    Rational add = c.mul(sub.getValue());
                    expanded.merge(sub.getKey(), add, Rational::add);
                }
            } else {
                expanded.merge(v, c, Rational::add);
            }
        }
        for (Map.Entry<Integer, Rational> e : expanded.entrySet()) {
            if (!e.getValue().isZero()) {
                b.row.put(e.getKey(), e.getValue());
                usedIn.get(e.getKey()).add(basicId);
            }
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
            pendingConflict = true;
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
            pendingConflict = true;
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

    /** Update the value of non-basic v to delta, propagating to dependent basic rows.
     *  Uses {@link #usedIn} so the iteration is O(rows-mentioning-v) instead of O(B). */
    private void update(int vId, Rational newVal) {
        Var v = vars.get(vId);
        Rational diff = newVal.sub(v.value);
        v.value = newVal;
        IntList uses = usedIn.get(vId);
        int[] arr = uses.data;
        int sz = uses.size;
        for (int i = 0; i < sz; i++) {
            Var b = vars.get(arr[i]);
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
        usedIn.get(nonBasicId).remove(basicId);
        for (Integer nbId : b.row.keySet()) usedIn.get(nbId).remove(basicId);
        LinkedHashMap<Integer, Rational> newNonBasicRow = new LinkedHashMap<>();
        Rational invA = Rational.ONE.div(a);
        newNonBasicRow.put(basicId, invA);
        for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
            newNonBasicRow.put(e.getKey(), e.getValue().negate().mul(invA));
        }
        int[] rowsUsingN = usedIn.get(nonBasicId).snapshot();
        for (int j : rowsUsingN) {
            if (j == basicId) continue;
            Var v = vars.get(j);
            if (!v.basic) continue;
            Rational c = v.row.get(nonBasicId);
            if (c == null) continue;
            v.row.remove(nonBasicId);
            usedIn.get(nonBasicId).remove(j);
            for (Map.Entry<Integer, Rational> e : newNonBasicRow.entrySet()) {
                Rational add = c.mul(e.getValue());
                Rational existing = v.row.get(e.getKey());
                Rational sum = existing == null ? add : existing.add(add);
                if (sum.isZero()) {
                    if (existing != null) {
                        v.row.remove(e.getKey());
                        usedIn.get(e.getKey()).remove(j);
                    }
                } else {
                    if (existing == null) usedIn.get(e.getKey()).add(j);
                    v.row.put(e.getKey(), sum);
                }
            }
        }
        b.basic = false;
        b.row = null;
        n.basic = true;
        n.row = newNonBasicRow;
        for (Integer nbId : newNonBasicRow.keySet()) usedIn.get(nbId).add(nonBasicId);
    }

    /** Pivot and update in one step: x_b moves to {@code newVbasic}, then we pivot on x_b/x_n. */
    private void pivotAndUpdate(int basicId, int nonBasicId, Rational newBasicValue) {
        Var b = vars.get(basicId);
        Rational a = b.row.get(nonBasicId);
        Rational diff = newBasicValue.sub(b.value).div(a);
        Var n = vars.get(nonBasicId);
        Rational newN = n.value.add(diff);
        IntList uses = usedIn.get(nonBasicId);
        int[] arr = uses.data;
        int sz = uses.size;
        for (int i = 0; i < sz; i++) {
            Var v = vars.get(arr[i]);
            if (!v.basic) continue;
            Rational c = v.row.get(nonBasicId);
            if (c == null) continue;
            v.value = v.value.add(c.mul(diff));
        }
        n.value = newN;
        b.value = newBasicValue;
        pivot(basicId, nonBasicId);
    }

    /** Set by pushLower/pushUpper when a bound directly contradicts another. */
    public boolean pendingConflict = false;

    /**
     * Run the Bland-rule pivoting search: while some basic violates its bound, find a non-basic
     * that can be moved to fix it. If none, the violating row is a Farkas-style conflict.
     * Returns true on success; populates {@link #lastConflict} on failure.
     */
    public boolean check() {
        if (pendingConflict) { pendingConflict = false; return false; }
        for (int safety = 0; safety < 100_000; safety++) {
            int badBasic = -1;
            boolean tooLow = false;
            int N = vars.size();
            // Bland's rule: lowest-id violator.
            for (int i = 0; i < N; i++) {
                Var v = vars.get(i);
                if (!v.basic) continue;
                if (v.lower != null && v.value.lt(v.lower)) { badBasic = i; tooLow = true; break; }
                if (v.upper != null && v.value.gt(v.upper)) { badBasic = i; tooLow = false; break; }
            }
            if (badBasic == -1) return true;
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
    public int lowerReasonOf(int v) { return vars.get(v).lowerReason; }
    public int upperReasonOf(int v) { return vars.get(v).upperReason; }
    public boolean isBasic(int v) { return vars.get(v).basic; }

    /** Read access to the row coefficients of a basic variable. Caller must not mutate. */
    public Map<Integer, Rational> rowOf(int basicId) {
        Var v = vars.get(basicId);
        return v.basic ? v.row : null;
    }

    /** True iff the variable's value is uniquely determined by the asserted bounds. Direct case:
     *  lower == upper. Transitive case: var is basic and every non-basic in its row is pinned.
     *  {@code reasonsOut}, if non-null, is populated with the literal IDs that justify the pinning. */
    public boolean isPinned(int vId, java.util.Set<Integer> reasonsOut) {
        return isPinnedRec(vId, reasonsOut, new java.util.HashSet<>());
    }
    private boolean isPinnedRec(int vId, java.util.Set<Integer> reasonsOut, java.util.Set<Integer> visited) {
        if (!visited.add(vId)) return false; // cycle guard (shouldn't happen)
        Var v = vars.get(vId);
        if (v.lower != null && v.upper != null && v.lower.compareTo(v.upper) == 0) {
            if (reasonsOut != null) {
                if (v.lowerReason != 0) reasonsOut.add(v.lowerReason);
                if (v.upperReason != 0) reasonsOut.add(v.upperReason);
            }
            return true;
        }
        if (!v.basic) return false;
        for (Map.Entry<Integer, Rational> e : v.row.entrySet()) {
            if (!isPinnedRec(e.getKey(), reasonsOut, visited)) return false;
        }
        return true;
    }

    /** Compute implied [lo, hi] of a basic variable from the row coefficients combined with
     *  the bounds on its non-basic constituents. {@code null} on an end means unbounded.
     *  Also populates {@code reasons} with the literal ids (lowerReason/upperReason) that
     *  bound each non-basic in the relevant direction. */
    public Rational[] impliedBounds(int basicId, java.util.Set<Integer> reasons) {
        Var b = vars.get(basicId);
        if (!b.basic) {
            // Treat as a row of just itself.
            Rational[] out = new Rational[2];
            if (b.lower != null) { out[0] = b.lower; if (b.lowerReason != 0) reasons.add(b.lowerReason); }
            if (b.upper != null) { out[1] = b.upper; if (b.upperReason != 0) reasons.add(b.upperReason); }
            return out;
        }
        Rational lo = Rational.ZERO;
        Rational hi = Rational.ZERO;
        boolean loInf = false, hiInf = false;
        for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
            int nb = e.getKey();
            Var nv = vars.get(nb);
            Rational c = e.getValue();
            if (c.signum() > 0) {
                // contributes c*lower(nb) to lo, c*upper(nb) to hi
                if (nv.lower == null) loInf = true; else lo = lo.add(c.mul(nv.lower));
                if (nv.upper == null) hiInf = true; else hi = hi.add(c.mul(nv.upper));
            } else {
                if (nv.upper == null) loInf = true; else lo = lo.add(c.mul(nv.upper));
                if (nv.lower == null) hiInf = true; else hi = hi.add(c.mul(nv.lower));
            }
        }
        // Collect reasons for the bounds we report (only after we know they're not infinite).
        if (!loInf) {
            for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
                int nb = e.getKey();
                Var nv = vars.get(nb);
                Rational c = e.getValue();
                int rsn = c.signum() > 0 ? nv.lowerReason : nv.upperReason;
                if (rsn != 0) reasons.add(rsn);
            }
        }
        if (!hiInf) {
            for (Map.Entry<Integer, Rational> e : b.row.entrySet()) {
                int nb = e.getKey();
                Var nv = vars.get(nb);
                Rational c = e.getValue();
                int rsn = c.signum() > 0 ? nv.upperReason : nv.lowerReason;
                if (rsn != 0) reasons.add(rsn);
            }
        }
        return new Rational[] { loInf ? null : lo, hiInf ? null : hi };
    }
}
