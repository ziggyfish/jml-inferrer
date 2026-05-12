package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Concrete evaluation of {@code (str.in_re LITERAL_STRING REGEX)} via Brzozowski derivatives.
 *
 * The regex is represented by its term-level S-expression structure:
 *   (str.to_re "abc")  → literal sub-string match
 *   (re.++ a b c)      → concatenation
 *   (re.union a b c)   → alternation
 *   (re.* a)           → Kleene star
 *   (re.+ a)           → one-or-more
 *   (re.opt a)         → zero-or-one
 *   (re.range "a" "z") → single-character range
 *   re.allchar         → any single character
 *   re.all             → any string
 *   re.none            → empty language
 *
 * For each matching membership query where the input string is a literal AND the regex tree
 * uses only the supported constructors over literals, we emit an axiom equating the membership
 * predicate to true / false. Symbolic strings or symbolic regexes are left opaque.
 */
public final class RegexEval {

    private final TermFactory tf;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seen = new HashSet<>();

    public RegexEval(TermFactory tf) { this.tf = tf; }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) { walk(t); }

    private void walk(Term t) {
        if (!seen.add(t.id)) return;
        for (Term c : t.children()) walk(c);
        if (t instanceof Term.App app && app.symbol.equals("str.in_re") && app.args.size() == 2) {
            Term s = app.args.get(0);
            Term re = app.args.get(1);
            if (s instanceof Term.StrConst sc) {
                Boolean m = matches(sc.value, re);
                if (m != null) axioms.add(tf.mkEq((Term) app, tf.mkBool(m)));
            }
        }
    }

    /** Try to evaluate {@code s ∈ L(re)}. Returns null if the regex contains symbolic parts. */
    private Boolean matches(String s, Term re) {
        if (re instanceof Term.App app) {
            switch (app.symbol) {
                case "str.to_re": {
                    if (app.args.size() == 1 && app.args.get(0) instanceof Term.StrConst lit) {
                        return s.equals(lit.value);
                    }
                    return null;
                }
                case "re.++":
                    return matchesConcat(s, app.args, 0);
                case "re.union":
                    for (Term a : app.args) {
                        Boolean m = matches(s, a);
                        if (m == null) return null;
                        if (m) return true;
                    }
                    return false;
                case "re.inter":
                    for (Term a : app.args) {
                        Boolean m = matches(s, a);
                        if (m == null) return null;
                        if (!m) return false;
                    }
                    return true;
                case "re.*":
                    if (app.args.size() == 1) return matchesStar(s, app.args.get(0));
                    return null;
                case "re.+":
                    if (app.args.size() == 1) {
                        if (s.isEmpty()) return false;
                        return matchesStar(s, app.args.get(0));
                    }
                    return null;
                case "re.opt":
                    if (app.args.size() == 1) {
                        if (s.isEmpty()) return true;
                        return matches(s, app.args.get(0));
                    }
                    return null;
                case "re.range":
                    if (app.args.size() == 2 && app.args.get(0) instanceof Term.StrConst lo
                            && app.args.get(1) instanceof Term.StrConst hi
                            && lo.value.length() == 1 && hi.value.length() == 1
                            && s.length() == 1) {
                        char c = s.charAt(0);
                        return c >= lo.value.charAt(0) && c <= hi.value.charAt(0);
                    }
                    return null;
                case "re.diff":
                    if (app.args.size() == 2) {
                        Boolean a = matches(s, app.args.get(0));
                        Boolean b = matches(s, app.args.get(1));
                        if (a == null || b == null) return null;
                        return a && !b;
                    }
                    return null;
                case "re.comp":
                    if (app.args.size() == 1) {
                        Boolean inner = matches(s, app.args.get(0));
                        if (inner == null) return null;
                        return !inner;
                    }
                    return null;
                case "re.none":
                    return false;
                case "re.all":
                    return true;
                case "re.allchar":
                    return s.length() == 1;
                default:
                    return null;
            }
        }
        if (re instanceof Term.Var v) {
            if (v.name.equals("re.none")) return false;
            if (v.name.equals("re.all")) return true;
            if (v.name.equals("re.allchar")) return s.length() == 1;
        }
        return null;
    }

    /** Try every split point: s = prefix + suffix where prefix matches args[i] and suffix matches re.++ args[i+1..]. */
    private Boolean matchesConcat(String s, List<Term> args, int idx) {
        if (idx == args.size()) return s.isEmpty();
        if (idx == args.size() - 1) return matches(s, args.get(idx));
        Term head = args.get(idx);
        boolean unknown = false;
        for (int split = 0; split <= s.length(); split++) {
            String pre = s.substring(0, split);
            String post = s.substring(split);
            Boolean preM = matches(pre, head);
            if (preM == null) { unknown = true; continue; }
            if (!preM) continue;
            Boolean postM = matchesConcat(post, args, idx + 1);
            if (postM == null) { unknown = true; continue; }
            if (postM) return true;
        }
        return unknown ? null : false;
    }

    /** s ∈ L(re*) iff s = e1 + e2 + ... + en, each ei ∈ L(re). */
    private Boolean matchesStar(String s, Term re) {
        if (s.isEmpty()) return true;
        boolean unknown = false;
        // Try non-empty splits to avoid infinite recursion on empty matches.
        for (int split = 1; split <= s.length(); split++) {
            String pre = s.substring(0, split);
            String post = s.substring(split);
            Boolean preM = matches(pre, re);
            if (preM == null) { unknown = true; continue; }
            if (!preM) continue;
            Boolean postM = matchesStar(post, re);
            if (postM == null) { unknown = true; continue; }
            if (postM) return true;
        }
        return unknown ? null : false;
    }
}
