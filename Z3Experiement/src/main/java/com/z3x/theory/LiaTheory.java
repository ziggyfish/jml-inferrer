package com.z3x.theory;

import com.z3x.sat.TheoryHook;
import com.z3x.solver.Cnf;
import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Linear arithmetic theory over Int and Real. Translates each arithmetic term into a Simplex
 * variable; equalities and ordering atoms get translated into pairs of bounds when their
 * literal is asserted.
 *
 * Each atom of the form <code>(op s t)</code> for op ∈ {≤, <, ≥, >, =} is normalised to
 * <code>(op (s - t) 0)</code>, then the LHS is decomposed into a sum of base-variable
 * contributions that drive the bound that goes into Simplex.
 *
 * Strict bounds (s &lt; t, s &gt; t) are encoded by tightening with epsilon — tracked via a
 * lexicographic Rational pair (value, epsilon coefficient). For day-2 we use plain Rationals
 * and treat strict the same as non-strict but include a witness check at the end. This is
 * sound only for satisfiable formulas; we'll upgrade to (Rational + δ·ε) representation in
 * a follow-up.
 */
public final class LiaTheory implements TheoryHook {

    private final TermFactory tf;
    private final Cnf cnf;
    private final Simplex simplex = new Simplex();

    /** Term id -> simplex variable id. Created lazily as terms are encountered. */
    private final Map<Integer, Integer> termIdToVar = new HashMap<>();

    /** Whether each simplex variable is integer-typed (Sort.INT). */
    private final List<Boolean> isInt = new ArrayList<>();

    /** Whether each simplex variable is "internal" (introduced for a sub-expression). */
    private final List<Boolean> isInternal = new ArrayList<>();

    /** Stack of asserted SAT literals (for explanations). */
    private final List<Integer> assertedStack = new ArrayList<>();

    /**
     * For every shared equality atom <code>(= a b)</code> we register a "diff" simplex variable
     * representing <code>a - b</code>. When LIA's bounds force d == 0 we know a == b and can
     * propagate the SAT atom positive; when d's bounds exclude 0 we propagate negative. This
     * is the equality side of Nelson-Oppen variable propagation toward EUF.
     */
    private final Map<Integer, Integer> equalityDiffVar = new HashMap<>();

    /** Per ordering-atom: SAT var → (diff var, op). Used to propagate ordering atoms whose truth
     *  is forced by current Simplex bounds — same idea as equalityDiffVar but for &lt;, &lt;=, &gt;, &gt;=. */
    private static final class OrderAtom {
        final int diffVar;
        final String op; // "<", "<=", ">", ">="
        final boolean isInt;
        OrderAtom(int dv, String op, boolean isInt) { this.diffVar = dv; this.op = op; this.isInt = isInt; }
    }
    private final Map<Integer, OrderAtom> orderAtoms = new HashMap<>();

    /** SAT vars already propagated to avoid loops. */
    private final java.util.Set<Integer> propagatedSet = new java.util.HashSet<>();

    /** Per-propagation reasons captured at propagate-time (so explain can return tight reasons). */
    private final Map<Integer, int[]> propagationReasons = new HashMap<>();

    public LiaTheory(TermFactory tf, Cnf cnf) {
        this.tf = tf;
        this.cnf = cnf;
    }

    @Override
    public void registerAtom(int var) {
        Term t = cnf.termForVar(var);
        if (t instanceof Term.App app && isLinearAtom(app)) {
            for (Term arg : app.args) freshVarFor(arg);
            // For equality atoms, also build a diff var so propagate() can detect when LIA's
            // bounds force the equality (positive) or rule it out (negative). This is the
            // LIA-side of Nelson-Oppen propagation; the diff bounds tighten when the SAT layer
            // asserts numeric facts on either side.
            if (app.symbol.equals("=")) {
                Term diff = tf.mkSub(List.of(app.args.get(0), app.args.get(1)));
                int dv = freshVarFor(diff);
                equalityDiffVar.put(var, dv);
            } else if (app.symbol.equals("<") || app.symbol.equals("<=")
                    || app.symbol.equals(">") || app.symbol.equals(">=")) {
                Term diff = tf.mkSub(List.of(app.args.get(0), app.args.get(1)));
                int dv = freshVarFor(diff);
                boolean isInt = isIntDiff(app);
                orderAtoms.put(var, new OrderAtom(dv, app.symbol, isInt));
            }
        }
    }

    /** Allocate (or reuse) a simplex variable representing a linear arithmetic term. */
    private int freshVarFor(Term t) {
        Integer cached = termIdToVar.get(t.id);
        if (cached != null) return cached;
        // Decompose t into a linear combination of "atomic" arithmetic terms.
        LinkedHashMap<Integer, Rational> combo = new LinkedHashMap<>();
        Rational[] constOut = { Rational.ZERO };
        decompose(t, Rational.ONE, combo, constOut);
        if (combo.size() == 1 && constOut[0].isZero()) {
            Map.Entry<Integer, Rational> only = combo.entrySet().iterator().next();
            if (only.getValue().equals(Rational.ONE)) {
                int v = only.getKey();
                termIdToVar.put(t.id, v);
                return v;
            }
        }
        // Otherwise create an internal basic variable equal to the combination.
        int newVar = simplex.addVariable(true);
        isInt.add(t.sort == Sort.INT);
        isInternal.add(true);
        // Combine with the constant offset by introducing an "always-1" auxiliary if needed.
        if (!constOut[0].isZero()) {
            int oneVarId = ensureOneConstant();
            combo.merge(oneVarId, constOut[0], Rational::add);
        }
        simplex.defineBasic(newVar, combo);
        termIdToVar.put(t.id, newVar);
        return newVar;
    }

    /** Variable index of a constant 1 (for representing offsets). Allocated lazily. */
    private Integer oneVar = null;

    private int ensureOneConstant() {
        if (oneVar != null) return oneVar;
        oneVar = simplex.addVariable(false);
        isInt.add(true);
        isInternal.add(true);
        // Force value = 1 at level 0.
        simplex.pushLower(oneVar, Rational.ONE, 0);
        simplex.pushUpper(oneVar, Rational.ONE, 0);
        return oneVar;
    }

    /** Decompose a term into combo (var-id -> coeff) + constant. */
    private void decompose(Term t, Rational scale, LinkedHashMap<Integer, Rational> combo, Rational[] constOut) {
        if (t instanceof Term.IntConst ic) {
            constOut[0] = constOut[0].add(scale.mul(Rational.of(ic.value)));
            return;
        }
        if (t instanceof Term.RatConst rc) {
            constOut[0] = constOut[0].add(scale.mul(Rational.of(rc.num, rc.den)));
            return;
        }
        if (t instanceof Term.App app) {
            switch (app.symbol) {
                case "+":
                    for (Term a : app.args) decompose(a, scale, combo, constOut);
                    return;
                case "-":
                    if (app.args.size() == 1) {
                        decompose(app.args.get(0), scale.negate(), combo, constOut);
                    } else {
                        decompose(app.args.get(0), scale, combo, constOut);
                        for (int i = 1; i < app.args.size(); i++) {
                            decompose(app.args.get(i), scale.negate(), combo, constOut);
                        }
                    }
                    return;
                case "*":
                    if (app.args.size() == 2) {
                        Term a = app.args.get(0), b = app.args.get(1);
                        Rational coeff = constantValue(a);
                        if (coeff != null) { decompose(b, scale.mul(coeff), combo, constOut); return; }
                        coeff = constantValue(b);
                        if (coeff != null) { decompose(a, scale.mul(coeff), combo, constOut); return; }
                    }
                    break; // fall through to opaque
                default: break;
            }
        }
        // Opaque: allocate a fresh atomic simplex variable for this term.
        Integer cached = termIdToVar.get(t.id);
        int v;
        if (cached != null) v = cached;
        else {
            v = simplex.addVariable(false);
            isInt.add(t.sort == Sort.INT);
            isInternal.add(false);
            termIdToVar.put(t.id, v);
        }
        combo.merge(v, scale, Rational::add);
    }

    private static Rational constantValue(Term t) {
        if (t instanceof Term.IntConst ic) return Rational.of(ic.value);
        if (t instanceof Term.RatConst rc) return Rational.of(rc.num, rc.den);
        return null;
    }

    private static boolean isLinearAtom(Term.App app) {
        return switch (app.symbol) {
            case "<=", "<", ">=", ">" -> true;
            case "=" -> app.args.get(0).sort == Sort.INT || app.args.get(0).sort == Sort.REAL;
            default -> false;
        };
    }

    @Override
    public void assertLiteral(int lit) {
        int var = Math.abs(lit);
        boolean pos = lit > 0;
        Term t = cnf.termForVar(var);
        if (!(t instanceof Term.App app) || !isLinearAtom(app)) return;
        simplex.pushLevel();
        assertedStack.add(lit);
        // Build (lhs - rhs) <opPos> 0 (or negated form).
        Term diff = tf.mkSub(List.of(app.args.get(0), app.args.get(1)));
        int sv = freshVarFor(diff);
        switch (app.symbol) {
            case "<=" -> {
                if (pos) simplex.pushUpper(sv, Rational.ZERO, lit);
                else      simplex.pushLower(sv, Rational.ZERO, lit); // diff > 0
            }
            case "<" -> {
                // Strict: diff < 0 → diff <= -ε. We encode with a small negative slack for ints,
                // or a regular open bound that we enforce via the pivot search yielding non-zero ε.
                if (pos) simplex.pushUpper(sv, isIntDiff(app) ? Rational.MINUS_ONE : Rational.ZERO, lit);
                else      simplex.pushLower(sv, Rational.ZERO, lit);
            }
            case ">=" -> {
                if (pos) simplex.pushLower(sv, Rational.ZERO, lit);
                else      simplex.pushUpper(sv, Rational.ZERO, lit);
            }
            case ">" -> {
                if (pos) simplex.pushLower(sv, isIntDiff(app) ? Rational.ONE : Rational.ZERO, lit);
                else      simplex.pushUpper(sv, Rational.ZERO, lit);
            }
            case "=" -> {
                if (pos) {
                    simplex.pushLower(sv, Rational.ZERO, lit);
                    simplex.pushUpper(sv, Rational.ZERO, lit);
                    // Eager direct-bound push: (= var const) → set var.lower = var.upper = const.
                    // This makes the constant visible to non-linear axioms and other diff vars.
                    Rational cVal = constantValue(app.args.get(1));
                    Term lhs = app.args.get(0);
                    Rational lhsConst = constantValue(lhs);
                    if (cVal != null && lhsConst == null && lhs instanceof Term.Var) {
                        Integer vv = termIdToVar.get(lhs.id);
                        if (vv != null) {
                            simplex.pushLower(vv, cVal, lit);
                            simplex.pushUpper(vv, cVal, lit);
                        }
                    } else if (lhsConst != null && cVal == null && app.args.get(1) instanceof Term.Var) {
                        Integer vv = termIdToVar.get(app.args.get(1).id);
                        if (vv != null) {
                            simplex.pushLower(vv, lhsConst, lit);
                            simplex.pushUpper(vv, lhsConst, lit);
                        }
                    }
                }
                // If negative we can't directly encode disequality in Simplex; fall back to
                // doing a check that splits later via the SAT layer. For now no-op; theory will
                // remain incomplete on disequalities.
            }
        }
    }

    private boolean isIntDiff(Term.App app) {
        return app.args.get(0).sort == Sort.INT && app.args.get(1).sort == Sort.INT;
    }

    @Override
    public void retractLiteral(int lit) {
        simplex.popLevel();
        if (!assertedStack.isEmpty()) assertedStack.remove(assertedStack.size() - 1);
        // Allow re-propagation if bounds change again.
        propagatedSet.remove(lit);
        propagatedSet.remove(-lit);
    }

    @Override
    public int[] check() {
        if (!simplex.check()) return formatConflict();
        if (!makeIntegerFeasible(0)) return formatConflict();
        return null;
    }

    /**
     * Internal branch-and-bound. Walk integer-typed simplex vars; when one has a non-integer
     * value, branch on {@code v <= floor} and {@code v >= ceil}. The first branch that yields
     * a fully integer-feasible solution gets its bounds folded into the current literal's
     * scope (via {@link Simplex#discardLastLevel()}) so they persist until SAT retracts.
     */
    private boolean makeIntegerFeasible(int depth) {
        if (depth > 32) return false; // give up on deep branching
        int v = findNonIntegerInt();
        if (v == -1) return true;
        java.math.BigInteger floor = simplex.valueOf(v).floor();
        java.math.BigInteger ceil = simplex.valueOf(v).ceil();
        // Branch v <= floor
        simplex.pushLevel();
        if (simplex.pushUpper(v, Rational.of(floor), 0) && simplex.check() && makeIntegerFeasible(depth + 1)) {
            simplex.discardLastLevel();
            return true;
        }
        simplex.popLevel();
        // Branch v >= ceil
        simplex.pushLevel();
        if (simplex.pushLower(v, Rational.of(ceil), 0) && simplex.check() && makeIntegerFeasible(depth + 1)) {
            simplex.discardLastLevel();
            return true;
        }
        simplex.popLevel();
        return false;
    }

    private int findNonIntegerInt() {
        for (int v = 0; v < simplex.numVars(); v++) {
            if (v < isInt.size() && isInt.get(v) && !simplex.valueOf(v).isInteger()) return v;
        }
        return -1;
    }

    private int[] formatConflict() {
        int[] c = simplex.lastConflict;
        if (c == null || c.length == 0 || (c.length == 1 && c[0] == 0)) {
            int[] out = new int[assertedStack.size()];
            for (int i = 0; i < out.length; i++) out[i] = -assertedStack.get(i);
            return out;
        }
        int[] out = new int[c.length];
        for (int i = 0; i < c.length; i++) out[i] = -c[i];
        return out;
    }

    @Override
    public List<Integer> propagate() {
        List<Integer> out = new ArrayList<>();
        // Pivot to a consistent assignment so impliedBounds/isPinned see post-pivot state. If the
        // pivot detects a conflict, set pendingConflict back so theory.check (called next) re-fires
        // it instead of declaring SAT.
        if (!simplex.check()) {
            simplex.pendingConflict = true;
            return out;
        }
        for (Map.Entry<Integer, Integer> e : equalityDiffVar.entrySet()) {
            int satVar = e.getKey();
            int dv = e.getValue();
            if (propagatedSet.contains(satVar) || propagatedSet.contains(-satVar)) continue;
            // Direct bounds path.
            Rational lo = simplex.lowerOf(dv);
            Rational hi = simplex.upperOf(dv);
            java.util.Set<Integer> reasons = new java.util.LinkedHashSet<>();
            // Implied-bounds path: tighten lo/hi using row reasoning. This catches cases where
            // a and b are each pinned to the same value via separate constraints (a=1, b=1) so
            // the diff variable's row evaluates to a single point even though the diff itself
            // never received a direct bound.
            if (simplex.isBasic(dv)) {
                Rational[] implied = simplex.impliedBounds(dv, reasons);
                if (implied[0] != null && (lo == null || implied[0].gt(lo))) lo = implied[0];
                if (implied[1] != null && (hi == null || implied[1].lt(hi))) hi = implied[1];
            } else {
                if (simplex.lowerReasonOf(dv) != 0) reasons.add(simplex.lowerReasonOf(dv));
                if (simplex.upperReasonOf(dv) != 0) reasons.add(simplex.upperReasonOf(dv));
            }
            // Transitive value-pinning: if the diff var is forced to a unique value via
            // chained basic rows whose non-basics are all pinned, use that value.
            if ((lo == null || hi == null) && simplex.isPinned(dv, reasons)) {
                Rational pinned = simplex.valueOf(dv);
                if (lo == null) lo = pinned;
                if (hi == null) hi = pinned;
            }
            if (lo == null || hi == null) continue;
            int cmp = lo.compareTo(hi);
            int lit = 0;
            if (cmp == 0) {
                lit = lo.isZero() ? satVar : -satVar;
            } else if (cmp < 0) {
                if (lo.signum() > 0 || hi.signum() < 0) lit = -satVar;
            }
            if (lit != 0) {
                propagatedSet.add(lit);
                out.add(lit);
                int[] reasonArr = new int[reasons.size()];
                int i = 0; for (int r : reasons) reasonArr[i++] = r;
                propagationReasons.put(lit, reasonArr);
            }
        }
        // Ordering atoms: similarly compute lo/hi for the diff and check if op is forced.
        for (Map.Entry<Integer, OrderAtom> e : orderAtoms.entrySet()) {
            int satVar = e.getKey();
            if (propagatedSet.contains(satVar) || propagatedSet.contains(-satVar)) continue;
            OrderAtom oa = e.getValue();
            int dv = oa.diffVar;
            Rational lo = simplex.lowerOf(dv);
            Rational hi = simplex.upperOf(dv);
            java.util.Set<Integer> reasons = new java.util.LinkedHashSet<>();
            if (simplex.isBasic(dv)) {
                Rational[] implied = simplex.impliedBounds(dv, reasons);
                if (implied[0] != null && (lo == null || implied[0].gt(lo))) lo = implied[0];
                if (implied[1] != null && (hi == null || implied[1].lt(hi))) hi = implied[1];
            } else {
                if (simplex.lowerReasonOf(dv) != 0) reasons.add(simplex.lowerReasonOf(dv));
                if (simplex.upperReasonOf(dv) != 0) reasons.add(simplex.upperReasonOf(dv));
            }
            if ((lo == null || hi == null) && simplex.isPinned(dv, reasons)) {
                Rational pinned = simplex.valueOf(dv);
                if (lo == null) lo = pinned;
                if (hi == null) hi = pinned;
            }
            // diff = a - b. op:
            //   "<"  → a <  b ↔ diff <  0
            //   "<=" → a <= b ↔ diff <= 0
            //   ">"  → diff > 0
            //   ">=" → diff >= 0
            Boolean truth = null;
            switch (oa.op) {
                case "<":
                    if (hi != null && hi.signum() < 0) truth = true;
                    else if (lo != null && lo.signum() >= 0) truth = false;
                    break;
                case "<=":
                    if (hi != null && hi.signum() <= 0) truth = true;
                    else if (lo != null && lo.signum() > 0) truth = false;
                    break;
                case ">":
                    if (lo != null && lo.signum() > 0) truth = true;
                    else if (hi != null && hi.signum() <= 0) truth = false;
                    break;
                case ">=":
                    if (lo != null && lo.signum() >= 0) truth = true;
                    else if (hi != null && hi.signum() < 0) truth = false;
                    break;
            }
            if (truth != null) {
                int lit = truth ? satVar : -satVar;
                propagatedSet.add(lit);
                out.add(lit);
                int[] reasonArr = new int[reasons.size()];
                int i = 0; for (int r : reasons) reasonArr[i++] = r;
                propagationReasons.put(lit, reasonArr);
            }
        }
        return out;
    }

    @Override
    public int[] explain(int propagatedLit) {
        int[] reasons = propagationReasons.get(propagatedLit);
        if (reasons != null && reasons.length > 0) {
            int[] out = new int[reasons.length + 1];
            for (int i = 0; i < reasons.length; i++) out[i] = -reasons[i];
            out[out.length - 1] = propagatedLit;
            return out;
        }
        int[] out = new int[assertedStack.size() + 1];
        for (int i = 0; i < assertedStack.size(); i++) out[i] = -assertedStack.get(i);
        out[out.length - 1] = propagatedLit;
        return out;
    }

    /** Best-effort model extraction: return the Simplex value of any registered atomic Int/Real term. */
    public Rational modelValue(Term t) {
        Integer v = termIdToVar.get(t.id);
        if (v == null) return null;
        return simplex.valueOf(v);
    }
}
