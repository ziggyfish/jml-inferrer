package com.z3x.sat;

import com.z3x.solver.Cnf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Watched-literal CDCL SAT solver with VSIDS, 1UIP conflict analysis, learned clauses,
 * Luby restarts, and phase saving. Theory layer plugged in via {@link TheoryHook}.
 *
 * Variable indices are 1-based to match DIMACS / our CNF emitter.
 * Literals: positive int = positive literal, negative int = negated literal.
 *
 * Internal arrays are sized for vars + 1 to keep the 1-based indexing.
 */
public final class Cdcl {

    public enum Result { SAT, UNSAT }

    // ---------- problem state ----------
    private final int nVars;
    private final List<int[]> clauses = new ArrayList<>(); // initial + learned
    private final List<int[]> watchPos; // watchPos[v] = clauses watching +v
    private final List<int[]> watchNeg; // for -v
    // Each watch list is an int[] of clause indices; we maintain it as a packed array.

    // ---------- assignment state ----------
    /** value[v]: 0 = unassigned, 1 = true, -1 = false. */
    private final int[] value;
    /** decisionLevel[v]: level at which v was assigned. */
    private final int[] level;
    /** reason[v]: clause index of the unit clause that propagated v, or -1 if decision/T-prop. */
    private final int[] reason;
    /** trail: order of assignments. */
    private final int[] trail;
    private int trailSize = 0;
    private final int[] trailLim; // start of each level on the trail
    private int decisionLevel = 0;
    /** phase saving: last polarity for v. */
    private final int[] phase;

    // ---------- VSIDS ----------
    private final double[] activity;
    private double varInc = 1.0;
    private static final double VAR_DECAY = 0.95;
    private static final double VAR_RESCALE_LIMIT = 1e100;

    // ---------- learned clause activity ----------
    private final List<Double> clauseActivity = new ArrayList<>();
    private double claInc = 1.0;
    private static final double CLA_DECAY = 0.999;
    private static final double CLA_RESCALE_LIMIT = 1e20;
    private int firstLearned;

    // ---------- restart and reduce schedule ----------
    private long conflicts = 0;
    private long restartConflicts = 0;
    private int restartIndex = 1;
    private int reduceLimit;
    private static final int MIN_REDUCE = 2000;

    // ---------- theory ----------
    private final TheoryHook theory;
    private final Cnf cnf;

    // ---------- diagnostics ----------
    public long propagations = 0;
    public long decisions = 0;
    public long restarts = 0;
    public long conflictsTotal = 0;
    public long learnedClauses = 0;

    /** False if a level-0 conflict was found during initial clause loading. */
    private boolean okay = true;

    private static final boolean DEBUG = Boolean.getBoolean("z3x.cdcl.debug");

    public Cdcl(Cnf cnf, TheoryHook theory) {
        this.cnf = cnf;
        this.theory = theory;
        this.nVars = cnf.numVars();
        this.value = new int[nVars + 1];
        this.level = new int[nVars + 1];
        this.reason = new int[nVars + 1];
        Arrays.fill(reason, -1);
        this.trail = new int[nVars + 1];
        this.trailLim = new int[nVars + 1];
        this.phase = new int[nVars + 1]; // start unassigned phase = 0 -> default false
        this.activity = new double[nVars + 1];
        this.watchPos = new ArrayList<>(nVars + 1);
        this.watchNeg = new ArrayList<>(nVars + 1);
        for (int i = 0; i <= nVars; i++) {
            watchPos.add(new int[0]);
            watchNeg.add(new int[0]);
        }
        // Register theory atoms
        for (int v = 1; v <= nVars; v++) {
            if (cnf.isTheoryAtom(v)) theory.registerAtom(v);
        }
        // Add initial clauses
        for (Cnf.Clause c : cnf.clauses()) addInitialClause(c.lits);
        firstLearned = clauses.size();
        reduceLimit = Math.max(MIN_REDUCE, clauses.size() / 3);
    }

    /** Returns SAT or UNSAT. After SAT, call {@link #valueOf(int)} to read assignments. */
    public Result solve() {
        if (!okay) return Result.UNSAT;
        for (;;) {
            int conflict = propagate();
            if (conflict >= 0) {
                conflictsTotal++;
                if (DEBUG) System.err.println("[Cdcl] B-conflict on clause " + conflict + " = " + Arrays.toString(clauses.get(conflict)) + " dl=" + decisionLevel);
                if (decisionLevel == 0) return Result.UNSAT;
                int[] learnt = analyze(conflict);
                int btLevel = backtrackLevelFrom(learnt);
                cancelUntil(btLevel);
                int cIdx = addLearnedClause(learnt);
                boolean ok = (learnt.length == 1)
                        ? enqueue(learnt[0], -1)
                        : enqueue(learnt[0], cIdx);
                if (!ok) return Result.UNSAT;
                decayVarActivity();
                decayClauseActivity();
                conflicts++;
                if (conflicts >= restartConflicts) restart();
                if (clauses.size() - firstLearned >= reduceLimit) reduceDb();
                continue;
            }
            // No Boolean conflict — consult theory.
            // First, T-propagate.
            List<Integer> tp = theory.propagate();
            boolean propagated = false;
            for (int lit : tp) {
                int v = Math.abs(lit);
                if (value[v] == 0) {
                    if (!enqueue(lit, -2)) return Result.UNSAT;
                    propagated = true;
                } else if ((lit > 0 && value[v] == -1) || (lit < 0 && value[v] == 1)) {
                    // T-prop conflicts with current assignment.
                    int[] expl = theory.explain(lit);
                    if (DEBUG) System.err.println("[Cdcl] T-prop-conflict lit=" + lit + " expl=" + Arrays.toString(expl) + " dl=" + decisionLevel);
                    expl = sortConflictByLevelDesc(expl);
                    int btLevel = backtrackLevelFrom(expl);
                    if (decisionLevel == 0 && btLevel == 0) return Result.UNSAT;
                    int cIdx = addLearnedClause(expl);
                    cancelUntil(btLevel);
                    boolean ok = (expl.length == 1)
                            ? enqueue(expl[0], -1)
                            : enqueue(expl[0], cIdx);
                    if (!ok) return Result.UNSAT;
                    propagated = true;
                    break;
                }
            }
            if (propagated) continue;
            int[] tConflict = theory.check();
            if (tConflict != null) {
                if (DEBUG) {
                    int[] levels = new int[tConflict.length];
                    for (int i = 0; i < tConflict.length; i++) levels[i] = level[Math.abs(tConflict[i])];
                    System.err.println("[Cdcl] T-conflict: " + Arrays.toString(tConflict) + " levels=" + Arrays.toString(levels) + " dl=" + decisionLevel);
                }
                // Theory may return literals in arbitrary order; reorder so [0] = highest-level
                // (asserting) literal and [1] = second-highest level — required for CDCL.
                tConflict = sortConflictByLevelDesc(tConflict);
                if (DEBUG) System.err.println("[Cdcl] T-conflict-sorted: " + Arrays.toString(tConflict));
                int btLevel = backtrackLevelFrom(tConflict);
                if (decisionLevel == 0 && btLevel == 0) return Result.UNSAT;
                int cIdx = addLearnedClause(tConflict);
                cancelUntil(btLevel);
                boolean ok = (tConflict.length == 1)
                        ? enqueue(tConflict[0], -1)
                        : enqueue(tConflict[0], cIdx);
                if (!ok) return Result.UNSAT;
                continue;
            }
            // Pick the next decision.
            int next = pickBranchVar();
            if (next == 0) return Result.SAT;
            decisionLevel++;
            trailLim[decisionLevel] = trailSize;
            int lit = phase[next] >= 0 ? next : -next;
            enqueue(lit, -1);
            decisions++;
        }
    }

    public int valueOf(int var) { return value[var]; }

    // ---------- watch lists ----------

    private void addInitialClause(int[] origLits) {
        int[] lits = simplify(origLits);
        if (lits == null) {
            // Tautology — drop
            return;
        }
        if (lits.length == 0) {
            okay = false;
            return;
        }
        int idx = clauses.size();
        clauses.add(lits);
        clauseActivity.add(0.0);
        for (int l : lits) bumpVar(Math.abs(l));
        if (lits.length == 1) {
            int lit = lits[0];
            int v = Math.abs(lit);
            int needed = lit > 0 ? 1 : -1;
            if (value[v] == 0) {
                enqueue(lit, idx);
            } else if (value[v] != needed) {
                okay = false;
            }
        } else {
            attach(idx, lits[0]);
            attach(idx, lits[1]);
        }
    }

    private int addLearnedClause(int[] lits) {
        learnedClauses++;
        int idx = clauses.size();
        clauses.add(lits);
        clauseActivity.add(claInc);
        if (lits.length >= 2) {
            // Sort the first two by decision level (highest at index 1) so backtracking works.
            // Caller already ordered them but enforce.
            attach(idx, lits[0]);
            attach(idx, lits[1]);
        }
        for (int l : lits) bumpVar(Math.abs(l));
        return idx;
    }

    /** Remove duplicates and tautologies from a clause; null = tautology. */
    private static int[] simplify(int[] lits) {
        // Sort by absolute value to find pairs.
        int[] copy = lits.clone();
        Arrays.sort(copy);
        // Detect tautology (l and -l) and dedupe
        int n = 0;
        int[] out = new int[copy.length];
        for (int i = 0; i < copy.length; i++) {
            int l = copy[i];
            if (n > 0 && out[n - 1] == l) continue;
            if (n > 0 && out[n - 1] == -l) return null;
            out[n++] = l;
        }
        return Arrays.copyOf(out, n);
    }

    private void attach(int clauseIdx, int lit) {
        if (lit > 0) watchPos.set(lit, append(watchPos.get(lit), clauseIdx));
        else watchNeg.set(-lit, append(watchNeg.get(-lit), clauseIdx));
    }

    private void detach(int clauseIdx, int lit) {
        if (lit > 0) watchPos.set(lit, removeOne(watchPos.get(lit), clauseIdx));
        else watchNeg.set(-lit, removeOne(watchNeg.get(-lit), clauseIdx));
    }

    private static int[] append(int[] arr, int v) {
        int[] out = Arrays.copyOf(arr, arr.length + 1);
        out[arr.length] = v;
        return out;
    }

    private static int[] removeOne(int[] arr, int v) {
        for (int i = 0; i < arr.length; i++) {
            if (arr[i] == v) {
                int[] out = new int[arr.length - 1];
                System.arraycopy(arr, 0, out, 0, i);
                System.arraycopy(arr, i + 1, out, i, arr.length - 1 - i);
                return out;
            }
        }
        return arr;
    }

    // ---------- propagation ----------

    /** Returns true on success (or already-consistent), false if value disagrees at level 0. */
    private boolean enqueue(int lit, int reasonIdx) {
        int v = Math.abs(lit);
        int needed = lit > 0 ? 1 : -1;
        if (value[v] != 0) {
            if (value[v] == needed) return true;
            return false;
        }
        value[v] = needed;
        level[v] = decisionLevel;
        reason[v] = reasonIdx;
        phase[v] = needed;
        trail[trailSize++] = lit;
        if (DEBUG) System.err.println("[Cdcl] enq " + lit + " @lvl=" + decisionLevel + " reason=" + reasonIdx);
        if (cnf.isTheoryAtom(v)) theory.assertLiteral(lit);
        return true;
    }

    /** Returns clause index of a falsified clause (conflict), or -1 if no conflict. */
    private int propagate() {
        int qhead = trailSize;
        // Walk the trail forward processing each newly-assigned literal.
        // Reset qhead to the unprocessed start.
        // We track a separate qhead because enqueue() pushes onto trail.
        // Simpler model: walk from the head index of unprocessed at each iteration.
        // We'll restructure: maintain qhead as a field.
        // (Inline here to keep it simple: process from where we left off last time.)
        return propagateLoop();
    }

    private int qhead = 0;

    private int propagateLoop() {
        while (qhead < trailSize) {
            int lit = trail[qhead++];
            propagations++;
            // For each clause watching -lit, find a new watch or propagate / conflict.
            int negLit = -lit;
            int[] ws = (negLit > 0) ? watchPos.get(negLit) : watchNeg.get(-negLit);
            // Iterate a snapshot because we may detach.
            int[] snapshot = ws.clone();
            for (int cIdx : snapshot) {
                int[] cl = clauses.get(cIdx);
                if (cl.length < 2) continue;
                // Ensure cl[1] is the falsified watched literal (-lit may be cl[0] or cl[1])
                if (cl[0] == negLit) {
                    int tmp = cl[0]; cl[0] = cl[1]; cl[1] = tmp;
                }
                // cl[1] == negLit now
                // If cl[0] is true, clause is satisfied — keep watch.
                int v0 = Math.abs(cl[0]);
                if (value[v0] == (cl[0] > 0 ? 1 : -1)) continue;
                // Try to find a non-falsified literal at index >= 2.
                boolean foundNew = false;
                for (int i = 2; i < cl.length; i++) {
                    int li = cl[i];
                    int vi = Math.abs(li);
                    int valLi = (li > 0 ? value[vi] : -value[vi]);
                    if (valLi != -1) {
                        // swap and rewatch
                        cl[1] = li;
                        cl[i] = negLit;
                        detach(cIdx, negLit);
                        attach(cIdx, li);
                        foundNew = true;
                        break;
                    }
                }
                if (foundNew) continue;
                // No new watch — clause is unit or conflicting on cl[0].
                if (cl[0] > 0 ? value[v0] == -1 : value[v0] == 1) {
                    // conflict — qhead reset doesn't matter, caller will backtrack which resets it.
                    return cIdx;
                }
                // Propagate cl[0]
                enqueue(cl[0], cIdx);
            }
        }
        return -1;
    }

    // ---------- conflict analysis (1UIP) ----------

    private final boolean[] seen = new boolean[16]; // grown lazily

    private boolean[] seenArr() {
        if (seen.length <= nVars) return ensureSeen();
        return seen;
    }

    private boolean[] ensureSeen() {
        if (seenForAnalysis == null || seenForAnalysis.length <= nVars) {
            seenForAnalysis = new boolean[nVars + 1];
        }
        Arrays.fill(seenForAnalysis, false);
        return seenForAnalysis;
    }

    private boolean[] seenForAnalysis;

    private int[] analyze(int conflictIdx) {
        boolean[] seen = ensureSeen();
        List<Integer> learnt = new ArrayList<>();
        learnt.add(0); // placeholder for asserting literal
        int counter = 0;
        int[] cl = clauses.get(conflictIdx);
        bumpClauseActivity(conflictIdx);

        int p = 0;
        int idx = trailSize - 1;

        while (true) {
            for (int q : cl) {
                int v = Math.abs(q);
                if (!seen[v] && level[v] > 0) {
                    bumpVar(v);
                    seen[v] = true;
                    if (level[v] >= decisionLevel) counter++;
                    else learnt.add(q);
                }
            }
            // Walk back along trail to next seen literal.
            while (idx >= 0 && !seen[Math.abs(trail[idx])]) idx--;
            if (idx < 0) break;
            p = trail[idx];
            int pv = Math.abs(p);
            counter--;
            if (counter <= 0) { learnt.set(0, -p); break; }
            int rIdx = reason[pv];
            if (rIdx < 0) {
                // Decision or T-propagated without explanation: ask theory.
                if (rIdx == -2) {
                    int[] expl = theory.explain(p);
                    cl = expl;
                } else {
                    learnt.set(0, -p);
                    break;
                }
            } else {
                cl = clauses.get(rIdx);
                bumpClauseActivity(rIdx);
                // The reason clause has p as cl[0]; skip it during the next iteration.
                // We'll re-include it in the next loop but it's already seen so no harm.
            }
            seen[pv] = true;
            idx--;
        }
        // Learned clause is now `learnt`. Order so cl[0] = asserting literal, cl[1] = max-level remaining.
        int[] out = new int[learnt.size()];
        for (int i = 0; i < out.length; i++) out[i] = learnt.get(i);

        // Find second-highest level among out[1..] and put at out[1]
        if (out.length > 1) {
            int maxIdx = 1;
            int maxLvl = level[Math.abs(out[1])];
            for (int i = 2; i < out.length; i++) {
                int lv = level[Math.abs(out[i])];
                if (lv > maxLvl) { maxLvl = lv; maxIdx = i; }
            }
            int tmp = out[1]; out[1] = out[maxIdx]; out[maxIdx] = tmp;
        }
        return out;
    }

    /** Sort a theory-conflict clause so that the highest-level literal is at index 0
     *  (the asserting position) and the second-highest at index 1 (the watch). */
    private int[] sortConflictByLevelDesc(int[] cl) {
        if (cl.length <= 1) return cl;
        Integer[] boxed = new Integer[cl.length];
        for (int i = 0; i < cl.length; i++) boxed[i] = cl[i];
        Arrays.sort(boxed, (a, b) -> {
            int la = level[Math.abs(a)];
            int lb = level[Math.abs(b)];
            return Integer.compare(lb, la);
        });
        int[] out = new int[cl.length];
        for (int i = 0; i < cl.length; i++) out[i] = boxed[i];
        return out;
    }

    private int backtrackLevelFrom(int[] learnt) {
        if (learnt.length <= 1) return 0;
        return level[Math.abs(learnt[1])];
    }

    // ---------- backtracking ----------

    private void cancelUntil(int targetLevel) {
        if (decisionLevel <= targetLevel) return;
        for (int i = trailSize - 1; i >= trailLim[targetLevel + 1]; i--) {
            int lit = trail[i];
            int v = Math.abs(lit);
            phase[v] = value[v]; // save
            if (cnf.isTheoryAtom(v)) theory.retractLiteral(lit);
            value[v] = 0;
            reason[v] = -1;
        }
        trailSize = trailLim[targetLevel + 1];
        qhead = trailSize;
        decisionLevel = targetLevel;
    }

    // ---------- branching (VSIDS) ----------

    private int pickBranchVar() {
        int best = 0;
        double bestAct = -1;
        for (int v = 1; v <= nVars; v++) {
            if (value[v] == 0 && activity[v] > bestAct) {
                best = v;
                bestAct = activity[v];
            }
        }
        return best;
    }

    private void bumpVar(int v) {
        activity[v] += varInc;
        if (activity[v] > VAR_RESCALE_LIMIT) {
            for (int i = 1; i <= nVars; i++) activity[i] /= VAR_RESCALE_LIMIT;
            varInc /= VAR_RESCALE_LIMIT;
        }
    }

    private void decayVarActivity() {
        varInc /= VAR_DECAY;
    }

    private void bumpClauseActivity(int idx) {
        if (idx < firstLearned) return; // only learned clauses tracked
        clauseActivity.set(idx, clauseActivity.get(idx) + claInc);
        if (clauseActivity.get(idx) > CLA_RESCALE_LIMIT) {
            for (int i = firstLearned; i < clauseActivity.size(); i++) {
                clauseActivity.set(i, clauseActivity.get(i) / CLA_RESCALE_LIMIT);
            }
            claInc /= CLA_RESCALE_LIMIT;
        }
    }

    private void decayClauseActivity() {
        claInc /= CLA_DECAY;
    }

    // ---------- restart (Luby) ----------

    private void restart() {
        restarts++;
        cancelUntil(0);
        restartConflicts = conflicts + (long) (luby(restartIndex++) * 100);
    }

    private static double luby(int x) {
        // Standard Luby: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
        for (int size = 1, seq = 0; ; size = 2 * size + 1, seq++) {
            if (size >= x) {
                while (size != x) {
                    size = (size - 1) / 2;
                    seq--;
                    x %= size + 1;
                }
                return Math.pow(2, seq);
            }
        }
    }

    // ---------- DB reduction ----------

    private void reduceDb() {
        // Sort learned clauses by activity ascending; drop bottom half whose size > 2 and not reasons.
        int learnedCount = clauses.size() - firstLearned;
        Integer[] order = new Integer[learnedCount];
        for (int i = 0; i < learnedCount; i++) order[i] = firstLearned + i;
        Arrays.sort(order, (a, b) -> Double.compare(clauseActivity.get(a), clauseActivity.get(b)));
        boolean[] keep = new boolean[clauses.size()];
        Arrays.fill(keep, true);
        int toRemove = learnedCount / 2;
        int removed = 0;
        boolean[] usedAsReason = new boolean[clauses.size()];
        for (int v = 1; v <= nVars; v++) {
            if (reason[v] >= firstLearned) usedAsReason[reason[v]] = true;
        }
        for (int i = 0; i < order.length && removed < toRemove; i++) {
            int idx = order[i];
            if (clauses.get(idx).length <= 2) continue;
            if (usedAsReason[idx]) continue;
            keep[idx] = false;
            removed++;
        }
        if (removed == 0) {
            reduceLimit *= 2;
            return;
        }
        // Build a renumbering map and rebuild watches.
        int[] newIdx = new int[clauses.size()];
        Arrays.fill(newIdx, -1);
        List<int[]> newClauses = new ArrayList<>();
        List<Double> newAct = new ArrayList<>();
        for (int i = 0; i < clauses.size(); i++) {
            if (keep[i]) {
                newIdx[i] = newClauses.size();
                newClauses.add(clauses.get(i));
                newAct.add(clauseActivity.get(i));
            }
        }
        // Re-fix firstLearned to wherever the original first-learned clauses landed.
        int newFirstLearned = newClauses.size();
        for (int i = 0; i < firstLearned; i++) {
            if (keep[i]) newFirstLearned = Math.min(newFirstLearned, newIdx[i] + 1 - 0);
        }
        // Simpler: original-clauses are always kept (we never set keep[i]=false for i<firstLearned),
        // so newFirstLearned == firstLearned (no original removed).
        clauses.clear();
        clauses.addAll(newClauses);
        clauseActivity.clear();
        clauseActivity.addAll(newAct);
        for (int v = 1; v <= nVars; v++) {
            if (reason[v] >= 0) reason[v] = newIdx[reason[v]];
        }
        // Rebuild watches from scratch.
        for (int v = 0; v <= nVars; v++) {
            watchPos.set(v, new int[0]);
            watchNeg.set(v, new int[0]);
        }
        for (int i = 0; i < clauses.size(); i++) {
            int[] cl = clauses.get(i);
            if (cl.length >= 2) {
                attach(i, cl[0]);
                attach(i, cl[1]);
            }
        }
        reduceLimit = (int) (reduceLimit * 1.1);
    }
}
