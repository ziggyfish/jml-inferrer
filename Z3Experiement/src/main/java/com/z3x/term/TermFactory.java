package com.z3x.term;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Hash-consing factory. Every term has a stable integer id; structurally equal terms
 * share that id. Sort-checking happens here so callers don't have to.
 *
 * Built-in operators understood by the factory:
 *   Boolean: and, or, not, =>, =, distinct, ite, true, false, xor
 *   Int/Real arithmetic: +, -, *, div, mod, abs
 *   Comparisons: <, <=, >, >=
 *
 * Anything else becomes an uninterpreted {@link Term.App}.
 */
public final class TermFactory {

    private final List<Term> nodes = new ArrayList<>();
    private final Map<Term.Key, Term> intern = new HashMap<>();

    /** Function symbol table (uninterpreted functions). */
    private final Map<String, Sort.FunSig> functions = new HashMap<>();

    /** Sort symbols declared by declare-sort. */
    private final Map<String, Sort> sorts = new HashMap<>();

    public TermFactory() {
        sorts.put("Bool", Sort.BOOL);
        sorts.put("Int", Sort.INT);
        sorts.put("Real", Sort.REAL);
    }

    public List<Term> allTerms() { return List.copyOf(nodes); }

    public Term termById(int id) { return nodes.get(id); }

    public Sort lookupSort(String name) { return sorts.get(name); }

    public void declareSort(String name, int arity) {
        sorts.put(name, new Sort.Uninterp(name, arity));
    }

    /** Replace a sort registration (used when a sort is upgraded e.g. uninterp → datatype). */
    public void replaceSort(String name, Sort sort) {
        sorts.put(name, sort);
    }

    public Sort.FunSig lookupFunction(String name) { return functions.get(name); }

    public void declareFunction(String name, List<Sort> args, Sort result) {
        functions.put(name, new Sort.FunSig(args, result));
    }

    // ---------- atoms ----------

    public Term.Var mkVar(String name, Sort sort) {
        return (Term.Var) intern(new Term.Key.VarK(name, sort), id -> new Term.Var(id, name, sort));
    }

    public Term.BoolConst mkBool(boolean v) {
        return (Term.BoolConst) intern(new Term.Key.BoolK(v), id -> new Term.BoolConst(id, v));
    }

    public Term.IntConst mkInt(long v) { return mkInt(BigInteger.valueOf(v)); }
    public Term.IntConst mkInt(BigInteger v) {
        return (Term.IntConst) intern(new Term.Key.IntK(v), id -> new Term.IntConst(id, v));
    }

    public Term.Quantifier mkQuantifier(Term.Quantifier.Kind k, List<String> names, List<Sort> sorts, Term body) {
        return (Term.Quantifier) intern(new Term.Key.QuantK(k, names, sorts, body.id),
                id -> new Term.Quantifier(id, k, names, sorts, body));
    }

    public Term.BvConst mkBv(BigInteger value, int width) {
        BigInteger mod = BigInteger.ONE.shiftLeft(width);
        BigInteger normalised = value.mod(mod);
        return (Term.BvConst) intern(new Term.Key.BvK(normalised, width),
                id -> new Term.BvConst(id, normalised, width));
    }

    public Term.RatConst mkRat(BigInteger num, BigInteger den) {
        if (den.signum() == 0) throw new IllegalArgumentException("zero denominator");
        if (den.signum() < 0) { num = num.negate(); den = den.negate(); }
        BigInteger g = num.abs().gcd(den);
        if (!g.equals(BigInteger.ONE)) { num = num.divide(g); den = den.divide(g); }
        BigInteger fNum = num, fDen = den;
        return (Term.RatConst) intern(new Term.Key.RatK(num, den),
                id -> new Term.RatConst(id, fNum, fDen));
    }

    // ---------- application (uninterpreted) ----------

    public Term mkApp(String symbol, List<Term> args) {
        Sort.FunSig sig = functions.get(symbol);
        Sort resultSort;
        if (sig == null) {
            // A nullary const declared via declare-const becomes a Var with the right sort.
            // If we see an unknown symbol, treat result as uninterpreted of unknown sort —
            // but the caller should have declared it. We default to Bool for safety.
            resultSort = Sort.BOOL;
        } else {
            if (sig.args().size() != args.size()) {
                throw new IllegalStateException("Arity mismatch for " + symbol +
                        ": expected " + sig.args().size() + ", got " + args.size());
            }
            for (int i = 0; i < args.size(); i++) {
                if (!Sort.equal(sig.args().get(i), args.get(i).sort)) {
                    throw new IllegalStateException("Sort mismatch for " + symbol +
                            " arg " + i + ": expected " + sig.args().get(i) +
                            ", got " + args.get(i).sort);
                }
            }
            resultSort = sig.result();
        }
        return mkAppRaw(symbol, args, resultSort);
    }

    public Term mkAppRaw(String symbol, List<Term> args, Sort resultSort) {
        List<Integer> argIds = new ArrayList<>(args.size());
        for (Term t : args) argIds.add(t.id);
        return intern(new Term.Key.AppK(symbol, argIds, resultSort),
                id -> new Term.App(id, symbol, args, resultSort));
    }

    // ---------- built-in Boolean ops with simplification ----------

    public Term mkNot(Term a) {
        require(a.sort == Sort.BOOL, "not expects Bool");
        if (a instanceof Term.BoolConst b) return mkBool(!b.value);
        if (a instanceof Term.App app && app.symbol.equals("not")) return app.args.get(0);
        return mkAppRaw("not", List.of(a), Sort.BOOL);
    }

    public Term mkAnd(List<Term> args) {
        List<Term> simp = new ArrayList<>();
        for (Term t : args) {
            require(t.sort == Sort.BOOL, "and expects Bool");
            if (t instanceof Term.BoolConst bc) {
                if (!bc.value) return mkBool(false);
                continue; // skip true
            }
            if (t instanceof Term.App app && app.symbol.equals("and")) {
                simp.addAll(app.args);
            } else {
                simp.add(t);
            }
        }
        if (simp.isEmpty()) return mkBool(true);
        if (simp.size() == 1) return simp.get(0);
        return mkAppRaw("and", simp, Sort.BOOL);
    }

    public Term mkOr(List<Term> args) {
        List<Term> simp = new ArrayList<>();
        for (Term t : args) {
            require(t.sort == Sort.BOOL, "or expects Bool");
            if (t instanceof Term.BoolConst bc) {
                if (bc.value) return mkBool(true);
                continue;
            }
            if (t instanceof Term.App app && app.symbol.equals("or")) {
                simp.addAll(app.args);
            } else {
                simp.add(t);
            }
        }
        if (simp.isEmpty()) return mkBool(false);
        if (simp.size() == 1) return simp.get(0);
        return mkAppRaw("or", simp, Sort.BOOL);
    }

    public Term mkImplies(Term a, Term b) {
        return mkOr(List.of(mkNot(a), b));
    }

    public Term mkIff(Term a, Term b) {
        return mkEq(a, b);
    }

    public Term mkEq(Term a, Term b) {
        if (!Sort.equal(a.sort, b.sort)) {
            throw new IllegalStateException("= sort mismatch: " + a.sort + " vs " + b.sort);
        }
        if (a == b) return mkBool(true);
        // Constant folding: any two structurally distinct constants of the same sort are unequal.
        if (a instanceof Term.BoolConst && b instanceof Term.BoolConst) return mkBool(false);
        if (a instanceof Term.IntConst && b instanceof Term.IntConst) return mkBool(false);
        if (a instanceof Term.RatConst && b instanceof Term.RatConst) return mkBool(false);
        if (a instanceof Term.BvConst ba && b instanceof Term.BvConst bb) {
            return mkBool(ba.width == bb.width && ba.value.equals(bb.value));
        }
        return mkAppRaw("=", List.of(a, b), Sort.BOOL);
    }

    public Term mkDistinct(List<Term> args) {
        if (args.size() < 2) return mkBool(true);
        List<Term> conj = new ArrayList<>();
        for (int i = 0; i < args.size(); i++) {
            for (int j = i + 1; j < args.size(); j++) {
                conj.add(mkNot(mkEq(args.get(i), args.get(j))));
            }
        }
        return mkAnd(conj);
    }

    public Term mkIte(Term c, Term t, Term e) {
        require(c.sort == Sort.BOOL, "ite condition must be Bool");
        if (!Sort.equal(t.sort, e.sort)) {
            throw new IllegalStateException("ite branch sort mismatch");
        }
        if (c instanceof Term.BoolConst bc) return bc.value ? t : e;
        if (t == e) return t;
        return mkAppRaw("ite", List.of(c, t, e), t.sort);
    }

    // ---------- arithmetic ----------

    public Term mkAdd(List<Term> args) {
        Sort s = arithResultSort(args);
        // Constant folding for all-int.
        if (args.stream().allMatch(t -> t instanceof Term.IntConst)) {
            BigInteger acc = BigInteger.ZERO;
            for (Term t : args) acc = acc.add(((Term.IntConst) t).value);
            return mkInt(acc);
        }
        if (args.size() == 1) return args.get(0);
        return mkAppRaw("+", args, s);
    }

    public Term mkSub(List<Term> args) {
        Sort s = arithResultSort(args);
        if (args.size() == 1) {
            // Unary minus
            if (args.get(0) instanceof Term.IntConst ic) return mkInt(ic.value.negate());
            return mkAppRaw("-", args, s);
        }
        if (args.stream().allMatch(t -> t instanceof Term.IntConst)) {
            BigInteger acc = ((Term.IntConst) args.get(0)).value;
            for (int i = 1; i < args.size(); i++) acc = acc.subtract(((Term.IntConst) args.get(i)).value);
            return mkInt(acc);
        }
        return mkAppRaw("-", args, s);
    }

    public Term mkMul(List<Term> args) {
        Sort s = arithResultSort(args);
        if (args.stream().allMatch(t -> t instanceof Term.IntConst)) {
            BigInteger acc = BigInteger.ONE;
            for (Term t : args) acc = acc.multiply(((Term.IntConst) t).value);
            return mkInt(acc);
        }
        if (args.size() == 1) return args.get(0);
        return mkAppRaw("*", args, s);
    }

    public Term mkLe(Term a, Term b) {
        return mkAppRaw("<=", List.of(a, b), Sort.BOOL);
    }
    public Term mkLt(Term a, Term b) { return mkAppRaw("<", List.of(a, b), Sort.BOOL); }
    public Term mkGe(Term a, Term b) { return mkAppRaw(">=", List.of(a, b), Sort.BOOL); }
    public Term mkGt(Term a, Term b) { return mkAppRaw(">", List.of(a, b), Sort.BOOL); }

    private Sort arithResultSort(List<Term> args) {
        boolean anyReal = args.stream().anyMatch(t -> t.sort == Sort.REAL);
        return anyReal ? Sort.REAL : Sort.INT;
    }

    // ---------- intern helper ----------

    private Term intern(Term.Key key, java.util.function.IntFunction<Term> mk) {
        Term existing = intern.get(key);
        if (existing != null) return existing;
        int id = nodes.size();
        Term t = mk.apply(id);
        nodes.add(t);
        intern.put(key, t);
        return t;
    }

    private static void require(boolean cond, String msg) {
        if (!cond) throw new IllegalStateException(msg);
    }
}
