package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Bit-blasting for the theory of bit-vectors.
 *
 * Each bit-vector term of width {@code w} is mapped to a list of {@code w} Boolean terms
 * (least-significant bit first). BV operators become Boolean circuits:
 * <ul>
 *   <li>{@code bvand}, {@code bvor}, {@code bvxor}, {@code bvnot} — bitwise.</li>
 *   <li>{@code bvadd}, {@code bvsub}, {@code bvneg} — ripple-carry adder + two's complement.</li>
 *   <li>{@code =}, {@code bvult}, {@code bvule}, {@code bvugt}, {@code bvuge}, {@code bvslt},
 *       {@code bvsle}, {@code bvsgt}, {@code bvsge} — comparators.</li>
 * </ul>
 *
 * Multiplication, shifts, and extract/concat are not yet covered (flagged in PROGRESS.md).
 *
 * The blaster runs after array and ITE preprocessing. It rewrites each top-level Boolean
 * assertion by walking the term tree; each BV-typed subterm produces a bit-list cached by
 * term id, and each BV atom produces a Boolean term composed from those bit-lists.
 */
public final class BvBlaster {

    private final TermFactory tf;
    /** term-id -> bit-list (LSB first). */
    private final Map<Integer, List<Term>> bits = new HashMap<>();
    /** term-id -> rewritten Boolean term (for Bool-sort terms only). */
    private final Map<Integer, Term> boolCache = new HashMap<>();
    private int auxCounter = 0;

    public BvBlaster(TermFactory tf) { this.tf = tf; }

    public Term rewrite(Term t) {
        if (t.sort != Sort.BOOL) {
            throw new IllegalStateException("BvBlaster.rewrite called on non-Bool term: " + t);
        }
        Term cached = boolCache.get(t.id);
        if (cached != null) return cached;
        Term result = rewriteBool(t);
        boolCache.put(t.id, result);
        return result;
    }

    private Term rewriteBool(Term t) {
        if (!(t instanceof Term.App app)) return t;
        switch (app.symbol) {
            case "and": return tf.mkAnd(map(app.args, this::rewrite));
            case "or":  return tf.mkOr(map(app.args, this::rewrite));
            case "not": return tf.mkNot(rewrite(app.args.get(0)));
            case "=>":  return tf.mkImplies(rewrite(app.args.get(0)), rewrite(app.args.get(1)));
            case "ite": return tf.mkIte(rewrite(app.args.get(0)),
                                        rewrite(app.args.get(1)),
                                        rewrite(app.args.get(2)));
            case "=":
                if (app.args.get(0).sort instanceof Sort.BitVec) {
                    List<Term> ab = blastBv(app.args.get(0));
                    List<Term> bb = blastBv(app.args.get(1));
                    return bitsEqual(ab, bb);
                }
                return t; // non-BV equality is for downstream theories
            case "bvult": return cmpUlt(blastBv(app.args.get(0)), blastBv(app.args.get(1)));
            case "bvule": return tf.mkOr(List.of(
                                cmpUlt(blastBv(app.args.get(0)), blastBv(app.args.get(1))),
                                bitsEqual(blastBv(app.args.get(0)), blastBv(app.args.get(1)))));
            case "bvugt": return cmpUlt(blastBv(app.args.get(1)), blastBv(app.args.get(0)));
            case "bvuge": return tf.mkOr(List.of(
                                cmpUlt(blastBv(app.args.get(1)), blastBv(app.args.get(0))),
                                bitsEqual(blastBv(app.args.get(0)), blastBv(app.args.get(1)))));
            case "bvslt": return cmpSlt(blastBv(app.args.get(0)), blastBv(app.args.get(1)));
            case "bvsle": return tf.mkOr(List.of(
                                cmpSlt(blastBv(app.args.get(0)), blastBv(app.args.get(1))),
                                bitsEqual(blastBv(app.args.get(0)), blastBv(app.args.get(1)))));
            case "bvsgt": return cmpSlt(blastBv(app.args.get(1)), blastBv(app.args.get(0)));
            case "bvsge": return tf.mkOr(List.of(
                                cmpSlt(blastBv(app.args.get(1)), blastBv(app.args.get(0))),
                                bitsEqual(blastBv(app.args.get(0)), blastBv(app.args.get(1)))));
            default:    return t;
        }
    }

    private List<Term> blastBv(Term t) {
        if (!(t.sort instanceof Sort.BitVec bv)) {
            throw new IllegalStateException("Not a BV term: " + t);
        }
        List<Term> cached = bits.get(t.id);
        if (cached != null) return cached;
        List<Term> result = computeBits(t, bv.width());
        bits.put(t.id, result);
        return result;
    }

    private List<Term> computeBits(Term t, int width) {
        if (t instanceof Term.BvConst bc) {
            List<Term> out = new ArrayList<>(width);
            for (int i = 0; i < width; i++) out.add(tf.mkBool(bc.value.testBit(i)));
            return out;
        }
        if (t instanceof Term.Var v) {
            // Allocate one fresh Bool var per bit.
            List<Term> out = new ArrayList<>(width);
            for (int i = 0; i < width; i++) {
                String name = v.name + "$" + i;
                tf.declareFunction(name, List.of(), Sort.BOOL);
                out.add(tf.mkVar(name, Sort.BOOL));
            }
            return out;
        }
        if (t instanceof Term.App app) {
            switch (app.symbol) {
                case "bvnot":
                    return mapList(blastBv(app.args.get(0)), tf::mkNot);
                case "bvand":
                    return zip(blastBv(app.args.get(0)), blastBv(app.args.get(1)),
                               (a, b) -> tf.mkAnd(List.of(a, b)));
                case "bvor":
                    return zip(blastBv(app.args.get(0)), blastBv(app.args.get(1)),
                               (a, b) -> tf.mkOr(List.of(a, b)));
                case "bvxor":
                    return zip(blastBv(app.args.get(0)), blastBv(app.args.get(1)),
                               (a, b) -> tf.mkNot(tf.mkEq(a, b)));
                case "bvadd": return rippleAdd(blastBv(app.args.get(0)),
                                                blastBv(app.args.get(1)),
                                                tf.mkBool(false));
                case "bvneg": return rippleAdd(mapList(blastBv(app.args.get(0)), tf::mkNot),
                                                ones(width), tf.mkBool(false));
                case "bvsub": {
                    List<Term> b = blastBv(app.args.get(1));
                    List<Term> negB = rippleAdd(mapList(b, tf::mkNot), ones(width), tf.mkBool(false));
                    return rippleAdd(blastBv(app.args.get(0)), negB, tf.mkBool(false));
                }
                default: break;
            }
        }
        // Fallback: treat as opaque BV variable — allocate fresh bool vars per bit.
        List<Term> out = new ArrayList<>(width);
        for (int i = 0; i < width; i++) {
            String name = "$bv" + (auxCounter++) + "_" + i;
            tf.declareFunction(name, List.of(), Sort.BOOL);
            out.add(tf.mkVar(name, Sort.BOOL));
        }
        return out;
    }

    private List<Term> ones(int w) {
        List<Term> r = new ArrayList<>(w);
        r.add(tf.mkBool(true));
        for (int i = 1; i < w; i++) r.add(tf.mkBool(false));
        return r;
    }

    private List<Term> rippleAdd(List<Term> a, List<Term> b, Term carryIn) {
        int w = a.size();
        List<Term> sum = new ArrayList<>(w);
        Term c = carryIn;
        for (int i = 0; i < w; i++) {
            Term x = a.get(i);
            Term y = b.get(i);
            Term xorXY = tf.mkNot(tf.mkEq(x, y));
            Term sumBit = tf.mkNot(tf.mkEq(xorXY, c));
            Term carryOut = tf.mkOr(List.of(
                tf.mkAnd(List.of(x, y)),
                tf.mkAnd(List.of(x, c)),
                tf.mkAnd(List.of(y, c))
            ));
            sum.add(sumBit);
            c = carryOut;
        }
        return sum;
    }

    private Term bitsEqual(List<Term> a, List<Term> b) {
        int w = Math.min(a.size(), b.size());
        List<Term> conj = new ArrayList<>(w);
        for (int i = 0; i < w; i++) conj.add(tf.mkEq(a.get(i), b.get(i)));
        return tf.mkAnd(conj);
    }

    /** Unsigned less-than: a &lt; b. Recursively a&lt;b iff (a_i=0 ∧ b_i=1) ∨ (a_i=b_i ∧ a_{lower}&lt;b_{lower}). */
    private Term cmpUlt(List<Term> a, List<Term> b) {
        int w = a.size();
        Term result = tf.mkBool(false);
        for (int i = 0; i < w; i++) {
            Term ai = a.get(i), bi = b.get(i);
            Term thisBit = tf.mkAnd(List.of(tf.mkNot(ai), bi));
            Term equalBit = tf.mkEq(ai, bi);
            result = tf.mkOr(List.of(thisBit, tf.mkAnd(List.of(equalBit, result))));
        }
        return result;
    }

    /** Signed less-than: a < b iff (a XOR sign-bit-trick) < (b XOR sign-bit-trick) unsigned, with sign flip. */
    private Term cmpSlt(List<Term> a, List<Term> b) {
        int w = a.size();
        if (w == 0) return tf.mkBool(false);
        // Flip top bit and do unsigned compare.
        List<Term> aFlip = new ArrayList<>(a);
        List<Term> bFlip = new ArrayList<>(b);
        aFlip.set(w - 1, tf.mkNot(a.get(w - 1)));
        bFlip.set(w - 1, tf.mkNot(b.get(w - 1)));
        return cmpUlt(aFlip, bFlip);
    }

    @FunctionalInterface
    private interface Bin<T, R> { R apply(T a, T b); }

    private static <T, R> List<R> zip(List<T> a, List<T> b, Bin<T, R> f) {
        int n = Math.min(a.size(), b.size());
        List<R> out = new ArrayList<>(n);
        for (int i = 0; i < n; i++) out.add(f.apply(a.get(i), b.get(i)));
        return out;
    }

    private static <T> List<T> mapList(List<T> xs, java.util.function.Function<T, T> f) {
        List<T> out = new ArrayList<>(xs.size());
        for (T x : xs) out.add(f.apply(x));
        return out;
    }

    private static <T> List<T> map(List<T> xs, java.util.function.Function<T, T> f) {
        List<T> out = new ArrayList<>(xs.size());
        for (T x : xs) out.add(f.apply(x));
        return out;
    }
}
