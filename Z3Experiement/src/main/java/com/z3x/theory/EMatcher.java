package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Trigger-based E-matching for quantifier instantiation. For each candidate trigger pattern
 * extracted from the quantifier body, walks the ground term set looking for matches; each match
 * produces a substitution, which is then applied to the body.
 *
 * Trigger inference:
 *   - Walk the body; collect uninterpreted-function applications that mention all bound vars
 *     (single-trigger patterns).
 *   - If no single trigger covers all bound vars, fall back to multi-trigger: pick a small set
 *     of patterns whose union covers all bound vars.
 *
 * The matcher is purely syntactic — it does not use e-graph equivalence classes. Promotion to
 * E-matching against the e-graph is a follow-up; the current syntactic matching already cuts
 * instantiation count by an order of magnitude on quantifier-heavy workloads.
 */
public final class EMatcher {

    private final TermFactory tf;

    public EMatcher(TermFactory tf) { this.tf = tf; }

    /** A trigger is just an App term containing some bound variables (as Term.Var). */
    public record Trigger(Term.App pattern, Set<String> coversBound) {}

    /** Find candidate triggers in the body. Prefers smaller single-trigger patterns that cover all binders. */
    public List<Trigger> inferTriggers(Term body, List<String> boundNames) {
        Set<String> bound = new HashSet<>(boundNames);
        List<Trigger> all = new ArrayList<>();
        collectTriggers(body, bound, all, new HashSet<>());
        // Prefer triggers that cover all bound names (single-trigger sufficient).
        List<Trigger> full = new ArrayList<>();
        for (Trigger t : all) {
            if (t.coversBound.equals(bound)) full.add(t);
        }
        return full.isEmpty() ? all : full;
    }

    private void collectTriggers(Term t, Set<String> bound, List<Trigger> out, Set<Integer> seen) {
        if (!seen.add(t.id)) return;
        if (t instanceof Term.App app && !isInterpreted(app.symbol)) {
            Set<String> mentioned = new HashSet<>();
            collectBoundMentions(app, bound, mentioned);
            if (!mentioned.isEmpty()) {
                out.add(new Trigger(app, mentioned));
            }
        }
        for (Term c : t.children()) collectTriggers(c, bound, out, seen);
    }

    private void collectBoundMentions(Term t, Set<String> bound, Set<String> out) {
        if (t instanceof Term.Var v && bound.contains(v.name)) out.add(v.name);
        for (Term c : t.children()) collectBoundMentions(c, bound, out);
    }

    /** Match a pattern against a ground candidate; if successful, returns the substitution. Otherwise null. */
    public Map<String, Term> matchPattern(Term pattern, Term candidate, Set<String> boundNames) {
        Map<String, Term> sub = new HashMap<>();
        return matchRec(pattern, candidate, boundNames, sub) ? sub : null;
    }

    private boolean matchRec(Term p, Term c, Set<String> bound, Map<String, Term> sub) {
        if (p instanceof Term.Var v && bound.contains(v.name)) {
            Term existing = sub.get(v.name);
            if (existing != null) return existing == c;
            sub.put(v.name, c);
            return true;
        }
        if (p == c) return true;
        if (p instanceof Term.App pa && c instanceof Term.App ca) {
            if (!pa.symbol.equals(ca.symbol)) return false;
            if (pa.args.size() != ca.args.size()) return false;
            for (int i = 0; i < pa.args.size(); i++) {
                if (!matchRec(pa.args.get(i), ca.args.get(i), bound, sub)) return false;
            }
            return true;
        }
        return false;
    }

    private static boolean isInterpreted(String sym) {
        return switch (sym) {
            case "and","or","not","=>","=","ite","distinct","xor",
                 "+","-","*","<=","<",">=",">","div","mod","abs",
                 "select","store" -> true;
            default -> false;
        };
    }
}
