package com.z3x.solver;

import com.z3x.term.Sort;
import com.z3x.term.Term;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Tseitin CNF transformation. Maps each Boolean term to a propositional variable,
 * adding clauses that encode the operator relating the variable to its sub-vars.
 *
 * Theory atoms (anything Boolean that isn't and/or/not/=>/ite/=) become opaque
 * variables but the original term is recorded in {@link #atomTerms()} so the
 * theory layer can attach meaning to them at search time.
 */
public final class Cnf {

    /** A clause is a list of integer literals. Variable indices are 1-based; sign encodes polarity. */
    public static final class Clause {
        public final int[] lits;
        public Clause(int[] lits) { this.lits = lits; }
        @Override public String toString() {
            StringBuilder sb = new StringBuilder("[");
            for (int i = 0; i < lits.length; i++) {
                if (i > 0) sb.append(' ');
                sb.append(lits[i]);
            }
            return sb.append(']').toString();
        }
    }

    private final Map<Term, Integer> termToVar = new HashMap<>();
    /** Inverse of {@link #termToVar}: var -> term. Index 0 unused. */
    private final List<Term> varToTerm = new ArrayList<>();

    /** Vars that are theory atoms (not pure Boolean structure). */
    private final List<Boolean> isTheoryAtom = new ArrayList<>();

    private final List<Clause> clauses = new ArrayList<>();
    private int nextVar = 1;

    public Cnf() {
        varToTerm.add(null); // index 0 sentinel
        isTheoryAtom.add(false);
    }

    /** Add the assertion `term` to the formula. Returns the top-level literal that must be true. */
    public int assertTerm(Term term) {
        if (term instanceof Term.BoolConst bc) {
            if (bc.value) return 0; // (assert true) — vacuous
            clauses.add(new Clause(new int[0])); // (assert false) — UNSAT
            return 0;
        }
        int v = encode(term);
        clauses.add(new Clause(new int[] { v }));
        return v;
    }

    public List<Clause> clauses() { return clauses; }

    public int numVars() { return nextVar - 1; }

    /** Term backing each variable, or null for the index-0 sentinel. */
    public Term termForVar(int var) { return varToTerm.get(var); }

    public boolean isTheoryAtom(int var) { return isTheoryAtom.get(var); }

    public List<Term> atomTerms() {
        List<Term> out = new ArrayList<>();
        for (int v = 1; v < varToTerm.size(); v++) {
            if (isTheoryAtom.get(v)) out.add(varToTerm.get(v));
        }
        return out;
    }

    /** Recursively encode a Boolean term, returning the literal that represents it. */
    private int encode(Term t) {
        if (t.sort != Sort.BOOL) {
            throw new IllegalStateException("Cnf.encode requires Bool: " + t);
        }
        Integer cached = termToVar.get(t);
        if (cached != null) return cached;

        // true / false constants
        if (t instanceof Term.BoolConst bc) {
            int v = newVar(t, false);
            // unit clause forcing the value
            clauses.add(new Clause(new int[] { bc.value ? v : -v }));
            return bc.value ? v : -v;
        }

        if (t instanceof Term.App app) {
            switch (app.symbol) {
                case "not": {
                    int sub = encode(app.args.get(0));
                    int v = -sub;
                    termToVar.put(t, v);
                    return v;
                }
                case "and": {
                    int v = newVar(t, false);
                    int[] big = new int[app.args.size() + 1];
                    big[0] = v; // (v \/ -a1 \/ -a2 ...)
                    for (int i = 0; i < app.args.size(); i++) {
                        int ai = encode(app.args.get(i));
                        big[i + 1] = -ai;
                        // (-v \/ ai)
                        clauses.add(new Clause(new int[] { -v, ai }));
                    }
                    clauses.add(new Clause(big));
                    return v;
                }
                case "or": {
                    int v = newVar(t, false);
                    int[] big = new int[app.args.size() + 1];
                    big[0] = -v;
                    for (int i = 0; i < app.args.size(); i++) {
                        int ai = encode(app.args.get(i));
                        big[i + 1] = ai;
                        clauses.add(new Clause(new int[] { v, -ai }));
                    }
                    clauses.add(new Clause(big));
                    return v;
                }
                case "ite": {
                    int c = encode(app.args.get(0));
                    int th = encode(app.args.get(1));
                    int el = encode(app.args.get(2));
                    int v = newVar(t, false);
                    // v <=> (c ? th : el)
                    // (-c \/ -th \/ v), (-c \/ th \/ -v), (c \/ -el \/ v), (c \/ el \/ -v)
                    clauses.add(new Clause(new int[] { -c, -th, v }));
                    clauses.add(new Clause(new int[] { -c, th, -v }));
                    clauses.add(new Clause(new int[] {  c, -el, v }));
                    clauses.add(new Clause(new int[] {  c, el, -v }));
                    return v;
                }
                case "=":
                    if (app.args.get(0).sort == Sort.BOOL) {
                        // Boolean equality = iff
                        int a = encode(app.args.get(0));
                        int b = encode(app.args.get(1));
                        int v = newVar(t, false);
                        clauses.add(new Clause(new int[] { -v, -a, b }));
                        clauses.add(new Clause(new int[] { -v, a, -b }));
                        clauses.add(new Clause(new int[] {  v, -a, -b }));
                        clauses.add(new Clause(new int[] {  v, a, b }));
                        return v;
                    }
                    // Else fall through: theory atom
                    break;
                default:
                    break;
            }
        }
        // Theory atom: opaque to SAT, tagged for the theory.
        return newVar(t, true);
    }

    private int newVar(Term t, boolean theory) {
        int v = nextVar++;
        varToTerm.add(t);
        isTheoryAtom.add(theory);
        termToVar.put(t, v);
        return v;
    }
}
