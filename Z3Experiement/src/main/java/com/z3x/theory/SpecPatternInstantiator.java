package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Fast path for the dominant quantifier shape in JML-Inferrer's verification corpus:
 *
 *   (forall ((k Int))
 *     (=&gt; (and (&lt;= lo k) (&lt; k hi))
 *         body_using_k_and_select))
 *
 * General ground instantiation would expand body for every ground integer in the formula.
 * This pass instead:
 *   1. Detects the pattern.
 *   2. Extracts (lo, hi) — they may be variables or constants.
 *   3. Filters ground integer terms to those proved to lie in [lo, hi) by simple arithmetic
 *      (only constant lo and hi are pruned today; symbolic bounds widen the candidate set).
 *
 * The result is dramatically fewer instances on real corpora: a forall over 8 declared int
 * constants but a constant range [0, 4) emits 4 instances instead of 8.
 *
 * The class is invoked by {@link Quantifiers} as a pre-pass; if the pattern doesn't match,
 * fall back to the standard cartesian instantiation.
 */
public final class SpecPatternInstantiator {

    private final TermFactory tf;

    public SpecPatternInstantiator(TermFactory tf) { this.tf = tf; }

    /** Recognised pattern result. Null if the quantifier doesn't match. */
    public record RangedForall(String boundName, Term lo, Term hi, Term body, boolean loInclusive, boolean hiInclusive) {}

    /** Try to match. Returns null if {@code q} is not in the recognised shape. */
    public RangedForall match(Term.Quantifier q) {
        if (q.kind != Term.Quantifier.Kind.FORALL) return null;
        if (q.boundNames.size() != 1) return null;
        if (!Sort.equal(q.boundSorts.get(0), Sort.INT)) return null;
        String name = q.boundNames.get(0);
        Term body = q.body;
        if (!(body instanceof Term.App app)) return null;
        // Body must be (=> guard body') OR (or (not guard) body').
        Term guard, kept;
        if (app.symbol.equals("=>") && app.args.size() == 2) {
            guard = app.args.get(0);
            kept = app.args.get(1);
        } else if (app.symbol.equals("or") && app.args.size() == 2
                && app.args.get(0) instanceof Term.App neg && neg.symbol.equals("not")) {
            guard = neg.args.get(0);
            kept = app.args.get(1);
        } else {
            return null;
        }
        // Guard must be conjunction of (<=/< lo k) and (</<= k hi) where k is the bound name.
        Term lo = null, hi = null;
        boolean loIncl = false, hiIncl = false;
        List<Term> conjuncts = unconj(guard);
        for (Term c : conjuncts) {
            if (!(c instanceof Term.App ca)) return null;
            switch (ca.symbol) {
                case "<=":
                case "<": {
                    boolean strict = ca.symbol.equals("<");
                    Term a = ca.args.get(0), b = ca.args.get(1);
                    if (a instanceof Term.Var av && av.name.equals(name)) {
                        // k op b → upper bound
                        if (hi != null) return null;
                        hi = b;
                        hiIncl = !strict;
                    } else if (b instanceof Term.Var bv && bv.name.equals(name)) {
                        // a op k → lower bound
                        if (lo != null) return null;
                        lo = a;
                        loIncl = !strict;
                    } else return null;
                    break;
                }
                default: return null;
            }
        }
        if (lo == null || hi == null) return null;
        return new RangedForall(name, lo, hi, kept, loIncl, hiIncl);
    }

    private static List<Term> unconj(Term t) {
        if (t instanceof Term.App a && a.symbol.equals("and")) return a.args;
        return List.of(t);
    }

    /**
     * Instantiate the matched pattern over the ground int set. If lo and hi are integer constants,
     * only ground integers in {@code [lo, hi)} (or whatever inclusivity matched) are used.
     * Otherwise, all ground integers in the input are considered.
     */
    public List<Term> instantiate(RangedForall p, Set<Term> groundInts, int cap) {
        BigInteger loConst = constInt(p.lo);
        BigInteger hiConst = constInt(p.hi);
        List<Term> instances = new ArrayList<>();
        Set<BigInteger> seen = new HashSet<>();
        for (Term g : groundInts) {
            BigInteger gv = constInt(g);
            if (loConst != null && gv != null) {
                int cmp = gv.compareTo(loConst);
                if (p.loInclusive ? cmp < 0 : cmp <= 0) continue;
            }
            if (hiConst != null && gv != null) {
                int cmp = gv.compareTo(hiConst);
                if (p.hiInclusive ? cmp > 0 : cmp >= 0) continue;
            }
            if (gv != null && !seen.add(gv)) continue;
            Map<String, Term> sub = new HashMap<>();
            sub.put(p.boundName, g);
            instances.add(Quantifiers.substitute(p.body, sub));
            if (instances.size() >= cap) break;
        }
        // Also enumerate the constant range fully when both bounds are constants — adds the
        // values that aren't yet in groundInts.
        if (loConst != null && hiConst != null) {
            BigInteger from = p.loInclusive ? loConst : loConst.add(BigInteger.ONE);
            BigInteger to = p.hiInclusive ? hiConst : hiConst.subtract(BigInteger.ONE);
            for (BigInteger i = from; i.compareTo(to) <= 0; i = i.add(BigInteger.ONE)) {
                if (instances.size() >= cap) break;
                if (!seen.add(i)) continue;
                Map<String, Term> sub = new HashMap<>();
                sub.put(p.boundName, tf.mkInt(i));
                instances.add(Quantifiers.substitute(p.body, sub));
            }
        }
        return instances;
    }

    private static BigInteger constInt(Term t) {
        if (t instanceof Term.IntConst ic) return ic.value;
        return null;
    }
}
