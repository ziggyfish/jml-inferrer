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
 * Quantifier preprocessing: skolemise outermost existentials, then ground-instantiate
 * universals against the set of all ground terms appearing in the input.
 *
 * Existentials at positive position (top-level forall body that's an existential, or top-level
 * exists) are Skolemised — bound variable replaced by fresh constants. Universals at positive
 * position are kept and ground-instantiated.
 *
 * Ground instantiation strategy:
 *   1. Collect all closed (variable-free) subterms of the input.
 *   2. For each forall (∀ x. body), build the trigger set = the body's outermost
 *      uninterpreted function applications that mention x.
 *   3. For each ground term g in the corpus that matches a trigger (same head, sort-compatible),
 *      derive a substitution and emit body[x := g_arg].
 *   4. Repeat until fixpoint OR a per-quantifier instantiation cap is reached.
 *
 * This is eager and incomplete — it works well for shallow inferrer-style quantifier shapes
 * (∀ k. lo ≤ k ∧ k &lt; n ⇒ P(arr[k])) where the trigger arr[k] matches every concrete index in the
 * input. For deeper quantifier alternation an MBQI / E-matching upgrade is needed.
 */
public final class Quantifiers {

    private final TermFactory tf;
    private final Map<Integer, Term> rewriteCache = new HashMap<>();
    private final List<Term> sideAssertions = new ArrayList<>();
    /** Per-quantifier instantiation cap to prevent runaway expansion. */
    private static final int MAX_INSTANCES_PER_FORALL = 64;
    private int skolemCounter = 0;

    public Quantifiers(TermFactory tf) { this.tf = tf; }

    public List<Term> sideAssertions() { return sideAssertions; }

    /** Top-level entry: rewrite an asserted formula in positive polarity. */
    public Term rewrite(Term t) {
        // Phase 1: skolemise existentials at positive polarity.
        Term skolemised = skolemise(t, true);
        // Phase 2: collect ground terms from the input + already-emitted side assertions.
        Set<Term> ground = collectGround(skolemised);
        for (Term s : sideAssertions) ground.addAll(collectGround(s));
        // Phase 3: instantiate universals.
        return instantiate(skolemised, ground, true);
    }

    /**
     * Multi-assertion entry: skolemises each top-level assertion, gathers a global ground
     * set, then instantiates universals against it. Returns the rewritten assertions; any
     * additional ground instances get appended to {@link #sideAssertions()}.
     */
    public List<Term> rewriteAll(List<Term> assertions) {
        activeFactory.set(tf);
        try {
            // Phase 1: skolemise each.
            List<Term> skolemised = new ArrayList<>(assertions.size());
            for (Term t : assertions) skolemised.add(skolemise(t, true));
            // Phase 2: build the global ground set from ALL skolemised assertions.
            Set<Term> ground = new HashSet<>();
            for (Term t : skolemised) ground.addAll(collectGround(t));
            // Phase 3: instantiate each. Side assertions are emitted into sideAssertions list.
            List<Term> out = new ArrayList<>(skolemised.size());
            for (Term t : skolemised) out.add(instantiate(t, ground, true));
            return out;
        } finally {
            activeFactory.remove();
        }
    }

    // ---------- Skolemisation ----------

    private Term skolemise(Term t, boolean positive) {
        if (t instanceof Term.Quantifier q) {
            Term.Quantifier.Kind k = q.kind;
            // exists in positive position OR forall in negative position → skolem.
            boolean isExistsInPos = (k == Term.Quantifier.Kind.EXISTS && positive)
                    || (k == Term.Quantifier.Kind.FORALL && !positive);
            if (isExistsInPos) {
                Map<String, Term> sub = new HashMap<>();
                for (int i = 0; i < q.boundNames.size(); i++) {
                    String name = "$sk" + (skolemCounter++) + "_" + q.boundNames.get(i);
                    tf.declareFunction(name, List.of(), q.boundSorts.get(i));
                    sub.put(q.boundNames.get(i), tf.mkVar(name, q.boundSorts.get(i)));
                }
                return skolemise(substitute(q.body, sub), positive);
            }
            // forall in positive (or exists in negative) → leave as is, but recurse into body
            // with bound names tracked so their inner skolems aren't done. Body's polarity stays.
            return tf.mkQuantifier(q.kind, q.boundNames, q.boundSorts, skolemise(q.body, positive));
        }
        if (t instanceof Term.App app) {
            String s = app.symbol;
            switch (s) {
                case "not":
                    return tf.mkNot(skolemise(app.args.get(0), !positive));
                case "=>": {
                    Term l = skolemise(app.args.get(0), !positive);
                    Term r = skolemise(app.args.get(1), positive);
                    return tf.mkImplies(l, r);
                }
                case "and": {
                    List<Term> nargs = new ArrayList<>(app.args.size());
                    for (Term a : app.args) nargs.add(skolemise(a, positive));
                    return tf.mkAnd(nargs);
                }
                case "or": {
                    List<Term> nargs = new ArrayList<>(app.args.size());
                    for (Term a : app.args) nargs.add(skolemise(a, positive));
                    return tf.mkOr(nargs);
                }
                case "ite": {
                    Term cT = skolemise(app.args.get(0), positive);
                    Term tT = skolemise(app.args.get(1), positive);
                    Term eT = skolemise(app.args.get(2), positive);
                    return tf.mkIte(cT, tT, eT);
                }
                default: return t;
            }
        }
        return t;
    }

    // ---------- Ground collection ----------

    private Set<Term> collectGround(Term t) {
        Set<Term> ground = new HashSet<>();
        collectGround(t, new HashSet<>(), ground);
        return ground;
    }

    private void collectGround(Term t, Set<String> bound, Set<Term> ground) {
        if (t instanceof Term.Quantifier q) {
            Set<String> nb = new HashSet<>(bound);
            nb.addAll(q.boundNames);
            collectGround(q.body, nb, ground);
            return;
        }
        if (t instanceof Term.Var v && bound.contains(v.name)) return;
        if (mentions(t, bound)) {
            for (Term c : t.children()) collectGround(c, bound, ground);
            return;
        }
        ground.add(t);
        for (Term c : t.children()) collectGround(c, bound, ground);
    }

    private boolean mentions(Term t, Set<String> names) {
        if (t instanceof Term.Var v) return names.contains(v.name);
        for (Term c : t.children()) if (mentions(c, names)) return true;
        return false;
    }

    // ---------- Instantiation ----------

    private Term instantiate(Term t, Set<Term> ground, boolean positive) {
        if (t instanceof Term.Quantifier q) {
            // forall in positive position: emit instances of body for each ground match;
            // also keep the original quantifier term as a top-level true (its body's instances
            // are added to side assertions so the SAT layer sees them).
            if (q.kind == Term.Quantifier.Kind.FORALL && positive) {
                emitInstances(q, ground);
                return tf.mkBool(true);
            }
            // exists in negative position is unsound to ground-instantiate (would falsely
            // discharge a forall with a finite witness set). Leave as an opaque Bool atom so
            // SAT can satisfy `not(opaque)` by choosing opaque = false.
            return t;
        }
        if (t instanceof Term.App app) {
            switch (app.symbol) {
                case "not":
                    return tf.mkNot(instantiate(app.args.get(0), ground, !positive));
                case "=>":
                    return tf.mkImplies(
                            instantiate(app.args.get(0), ground, !positive),
                            instantiate(app.args.get(1), ground, positive));
                case "and": {
                    List<Term> nargs = new ArrayList<>(app.args.size());
                    for (Term a : app.args) nargs.add(instantiate(a, ground, positive));
                    return tf.mkAnd(nargs);
                }
                case "or": {
                    List<Term> nargs = new ArrayList<>(app.args.size());
                    for (Term a : app.args) nargs.add(instantiate(a, ground, positive));
                    return tf.mkOr(nargs);
                }
                case "ite": {
                    Term c = instantiate(app.args.get(0), ground, positive);
                    Term tt = instantiate(app.args.get(1), ground, positive);
                    Term ee = instantiate(app.args.get(2), ground, positive);
                    return tf.mkIte(c, tt, ee);
                }
                default: return t;
            }
        }
        return t;
    }

    private void emitInstances(Term.Quantifier q, Set<Term> ground) {
        // Fast path: try the JML-Inferrer spec-pattern shape first.
        SpecPatternInstantiator spi = new SpecPatternInstantiator(tf);
        SpecPatternInstantiator.RangedForall ranged = spi.match(q);
        if (ranged != null) {
            Set<Term> groundInts = new HashSet<>();
            for (Term g : ground) if (Sort.equal(g.sort, Sort.INT)) groundInts.add(g);
            for (Term inst : spi.instantiate(ranged, groundInts, MAX_INSTANCES_PER_FORALL)) {
                // Recursively instantiate nested quantifiers exposed by the substitution.
                sideAssertions.add(instantiate(inst, ground, true));
            }
            return;
        }
        // Fallback: general cartesian product.
        int emitted = 0;
        Set<List<Term>> seenSubs = new HashSet<>();
        for (List<Term> sub : enumerateSubs(q.boundNames, q.boundSorts, ground)) {
            if (emitted >= MAX_INSTANCES_PER_FORALL) break;
            if (!seenSubs.add(sub)) continue;
            Map<String, Term> map = new HashMap<>();
            for (int i = 0; i < q.boundNames.size(); i++) map.put(q.boundNames.get(i), sub.get(i));
            Term inst = substitute(q.body, map);
            // Recursively instantiate any nested forall that surfaces after substitution.
            sideAssertions.add(instantiate(inst, ground, true));
            emitted++;
        }
    }

    private List<List<Term>> enumerateSubs(List<String> names, List<Sort> sorts, Set<Term> ground) {
        List<List<Term>> bySort = new ArrayList<>();
        for (Sort s : sorts) {
            List<Term> matches = new ArrayList<>();
            for (Term g : ground) {
                if (Sort.equal(g.sort, s)) matches.add(g);
            }
            // Always include at least one default value to prevent empty product.
            if (matches.isEmpty()) {
                if (s == Sort.INT) matches.add(tf.mkInt(0));
                else if (s == Sort.BOOL) matches.add(tf.mkBool(false));
            }
            bySort.add(matches);
        }
        // Cartesian product, capped.
        List<List<Term>> out = new ArrayList<>();
        out.add(new ArrayList<>());
        for (List<Term> opts : bySort) {
            List<List<Term>> next = new ArrayList<>();
            for (List<Term> prefix : out) {
                for (Term opt : opts) {
                    if (next.size() >= MAX_INSTANCES_PER_FORALL) break;
                    List<Term> ext = new ArrayList<>(prefix);
                    ext.add(opt);
                    next.add(ext);
                }
            }
            out = next;
        }
        return out;
    }

    // ---------- Substitution ----------

    public static Term substitute(Term t, Map<String, Term> sub) {
        return new Substituter(sub).go(t);
    }

    private static final class Substituter {
        private final Map<String, Term> sub;
        private final Map<Integer, Term> cache = new HashMap<>();
        Substituter(Map<String, Term> sub) { this.sub = sub; }
        Term go(Term t) {
            Term cached = cache.get(t.id);
            if (cached != null) return cached;
            Term out = doGo(t);
            cache.put(t.id, out);
            return out;
        }
        Term doGo(Term t) {
            if (t instanceof Term.Var v) {
                Term r = sub.get(v.name);
                return r != null ? r : t;
            }
            if (t instanceof Term.App app) {
                List<Term> nargs = new ArrayList<>(app.args.size());
                boolean changed = false;
                for (Term c : app.args) {
                    Term r = go(c);
                    if (r != c) changed = true;
                    nargs.add(r);
                }
                if (!changed) return t;
                // Use the same factory rebuild logic as preprocessors.
                return rebuildApp(app, nargs);
            }
            if (t instanceof Term.Quantifier q) {
                // Body substitution must skip names bound by q.
                Map<String, Term> filtered = new HashMap<>(sub);
                for (String n : q.boundNames) filtered.remove(n);
                if (filtered.isEmpty()) return t;
                // Capture avoidance: if any RHS in filtered mentions a name bound by q,
                // alpha-rename q's binders. For our ground-instantiation use case the RHS
                // is always a ground term, so this branch normally never fires — but cover it.
                TermFactory f = activeFactory.get();
                List<String> newNames = q.boundNames;
                List<Sort> newSorts = q.boundSorts;
                Term body = q.body;
                if (needsAlphaRename(q.boundNames, filtered)) {
                    Map<String, Term> alpha = new HashMap<>();
                    newNames = new ArrayList<>(q.boundNames.size());
                    for (int i = 0; i < q.boundNames.size(); i++) {
                        String fresh = q.boundNames.get(i) + "$" + System.identityHashCode(this);
                        newNames.add(fresh);
                        alpha.put(q.boundNames.get(i), f.mkVar(fresh, q.boundSorts.get(i)));
                    }
                    body = new Substituter(alpha).go(body);
                }
                Term newBody = new Substituter(filtered).go(body);
                if (newBody == q.body && newNames == q.boundNames) return t;
                return f.mkQuantifier(q.kind, newNames, newSorts, newBody);
            }
            return t;
        }
    }

    private static boolean needsAlphaRename(List<String> bound, Map<String, Term> sub) {
        Set<String> capture = new HashSet<>(bound);
        for (Term rhs : sub.values()) if (mentionsAny(rhs, capture)) return true;
        return false;
    }

    private static boolean mentionsAny(Term t, Set<String> names) {
        if (t instanceof Term.Var v) return names.contains(v.name);
        for (Term c : t.children()) if (mentionsAny(c, names)) return true;
        return false;
    }

    private static Term rebuildApp(Term.App app, List<Term> newArgs) {
        // We need a TermFactory to rebuild. Stash a thread-local one set by the entry point.
        TermFactory f = activeFactory.get();
        return switch (app.symbol) {
            case "and" -> f.mkAnd(newArgs);
            case "or"  -> f.mkOr(newArgs);
            case "not" -> f.mkNot(newArgs.get(0));
            case "ite" -> f.mkIte(newArgs.get(0), newArgs.get(1), newArgs.get(2));
            case "="   -> f.mkEq(newArgs.get(0), newArgs.get(1));
            case "+"   -> f.mkAdd(newArgs);
            case "-"   -> f.mkSub(newArgs);
            case "*"   -> f.mkMul(newArgs);
            case "<="  -> f.mkLe(newArgs.get(0), newArgs.get(1));
            case "<"   -> f.mkLt(newArgs.get(0), newArgs.get(1));
            case ">="  -> f.mkGe(newArgs.get(0), newArgs.get(1));
            case ">"   -> f.mkGt(newArgs.get(0), newArgs.get(1));
            default    -> f.mkAppRaw(app.symbol, newArgs, app.sort);
        };
    }

    private static final ThreadLocal<TermFactory> activeFactory = new ThreadLocal<>();

    /** Wrap rewrite() to set the active factory for the substituter. */
    public Term rewriteWithFactory(Term t) {
        activeFactory.set(tf);
        try {
            return rewrite(t);
        } finally {
            activeFactory.remove();
        }
    }
}
