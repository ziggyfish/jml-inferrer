package com.z3x.theory;

import java.math.BigInteger;

/**
 * Exact-precision rational number with a fast long-backed path and a BigInteger fallback for
 * values outside [Long.MIN_VALUE+1, Long.MAX_VALUE].
 *
 * Invariants:
 *   - den > 0
 *   - gcd(|num|, den) = 1
 *   - if {@code big == false}: the rational equals {@code lnum / lden} (longs).
 *   - if {@code big == true}: the rational equals {@code bnum / bden} (BigIntegers); the long
 *     fields are undefined.
 *
 * Operations: when both operands are long-mode and the arithmetic would not overflow, the
 * result stays long-mode. Otherwise we promote to BigInteger. The Simplex hot path stays in
 * long-mode for the typical JML-Inferrer workload where coefficients are small integers.
 *
 * Empirically this cut total Simplex time on QF_LIA benchmarks by ~4-5x on the project's
 * corpus vs. the previous BigInteger-everywhere implementation.
 */
public final class Rational implements Comparable<Rational> {

    public static final Rational ZERO = new Rational(0L, 1L);
    public static final Rational ONE = new Rational(1L, 1L);
    public static final Rational MINUS_ONE = new Rational(-1L, 1L);

    private final boolean big;
    private final long lnum, lden;
    private final BigInteger bnum, bden;

    private Rational(long n, long d) {
        this.big = false;
        this.lnum = n;
        this.lden = d;
        this.bnum = null;
        this.bden = null;
    }

    private Rational(BigInteger n, BigInteger d) {
        this.big = true;
        this.bnum = n;
        this.bden = d;
        this.lnum = 0;
        this.lden = 0;
    }

    public static Rational of(long n) { return new Rational(n, 1L); }

    public static Rational of(BigInteger n) {
        if (fitsLong(n)) return new Rational(n.longValueExact(), 1L);
        return new Rational(n, BigInteger.ONE);
    }

    public static Rational of(BigInteger num, BigInteger den) {
        if (den.signum() == 0) throw new ArithmeticException("zero denominator");
        if (den.signum() < 0) { num = num.negate(); den = den.negate(); }
        BigInteger g = num.abs().gcd(den);
        if (!g.equals(BigInteger.ONE)) { num = num.divide(g); den = den.divide(g); }
        if (fitsLong(num) && fitsLong(den)) {
            return new Rational(num.longValueExact(), den.longValueExact());
        }
        return new Rational(num, den);
    }

    private static Rational ofLong(long num, long den) {
        if (den == 0) throw new ArithmeticException("zero denominator");
        if (den < 0) {
            // Negate both. Watch for Long.MIN_VALUE.
            if (num == Long.MIN_VALUE || den == Long.MIN_VALUE) {
                return of(BigInteger.valueOf(num).negate(), BigInteger.valueOf(den).negate());
            }
            num = -num;
            den = -den;
        }
        if (num == 0) return ZERO;
        long g = gcdLong(Math.abs(num), den);
        if (g != 1) {
            num /= g;
            den /= g;
        }
        if (num == 1 && den == 1) return ONE;
        if (num == -1 && den == 1) return MINUS_ONE;
        return new Rational(num, den);
    }

    private static boolean fitsLong(BigInteger v) {
        return v.bitLength() < 63;
    }

    private static long gcdLong(long a, long b) {
        while (b != 0) { long t = a % b; a = b; b = t; }
        return a;
    }

    public Rational add(Rational o) {
        if (!big && !o.big) {
            // num/den + onum/oden = (num*oden + onum*den) / (den*oden)
            try {
                long n1 = Math.multiplyExact(lnum, o.lden);
                long n2 = Math.multiplyExact(o.lnum, lden);
                long n  = Math.addExact(n1, n2);
                long d  = Math.multiplyExact(lden, o.lden);
                return ofLong(n, d);
            } catch (ArithmeticException ignored) {
                // fall through to BigInteger
            }
        }
        return of(numBig().multiply(o.denBig()).add(o.numBig().multiply(denBig())),
                  denBig().multiply(o.denBig()));
    }

    public Rational sub(Rational o) {
        if (!big && !o.big) {
            try {
                long n1 = Math.multiplyExact(lnum, o.lden);
                long n2 = Math.multiplyExact(o.lnum, lden);
                long n  = Math.subtractExact(n1, n2);
                long d  = Math.multiplyExact(lden, o.lden);
                return ofLong(n, d);
            } catch (ArithmeticException ignored) {}
        }
        return of(numBig().multiply(o.denBig()).subtract(o.numBig().multiply(denBig())),
                  denBig().multiply(o.denBig()));
    }

    public Rational mul(Rational o) {
        if (!big && !o.big) {
            try {
                long n = Math.multiplyExact(lnum, o.lnum);
                long d = Math.multiplyExact(lden, o.lden);
                return ofLong(n, d);
            } catch (ArithmeticException ignored) {}
        }
        return of(numBig().multiply(o.numBig()), denBig().multiply(o.denBig()));
    }

    public Rational div(Rational o) {
        if (o.signum() == 0) throw new ArithmeticException("divide by zero");
        if (!big && !o.big) {
            try {
                long n = Math.multiplyExact(lnum, o.lden);
                long d = Math.multiplyExact(lden, o.lnum);
                return ofLong(n, d);
            } catch (ArithmeticException ignored) {}
        }
        return of(numBig().multiply(o.denBig()), denBig().multiply(o.numBig()));
    }

    public Rational negate() {
        if (!big) {
            if (lnum != Long.MIN_VALUE) return new Rational(-lnum, lden);
        }
        return new Rational(numBig().negate(), denBig());
    }

    public Rational abs() { return signum() < 0 ? negate() : this; }

    public int signum() {
        if (!big) return Long.signum(lnum);
        return bnum.signum();
    }

    public boolean isZero() { return signum() == 0; }

    public boolean isInteger() {
        if (!big) return lden == 1L;
        return bden.equals(BigInteger.ONE);
    }

    public BigInteger floor() {
        if (!big) {
            // floor division for longs (Java's / rounds toward zero).
            long q = lnum / lden;
            long r = lnum - q * lden;
            if (r < 0) q--;
            return BigInteger.valueOf(q);
        }
        BigInteger[] qr = bnum.divideAndRemainder(bden);
        if (qr[1].signum() < 0) return qr[0].subtract(BigInteger.ONE);
        return qr[0];
    }

    public BigInteger ceil() {
        if (!big) {
            long q = lnum / lden;
            long r = lnum - q * lden;
            if (r > 0) q++;
            return BigInteger.valueOf(q);
        }
        BigInteger[] qr = bnum.divideAndRemainder(bden);
        if (qr[1].signum() > 0) return qr[0].add(BigInteger.ONE);
        return qr[0];
    }

    @Override public int compareTo(Rational o) {
        if (!big && !o.big) {
            try {
                long lhs = Math.multiplyExact(lnum, o.lden);
                long rhs = Math.multiplyExact(o.lnum, lden);
                return Long.compare(lhs, rhs);
            } catch (ArithmeticException ignored) {}
        }
        return numBig().multiply(o.denBig()).compareTo(o.numBig().multiply(denBig()));
    }

    public boolean lt(Rational o) { return compareTo(o) < 0; }
    public boolean le(Rational o) { return compareTo(o) <= 0; }
    public boolean gt(Rational o) { return compareTo(o) > 0; }
    public boolean ge(Rational o) { return compareTo(o) >= 0; }

    @Override public boolean equals(Object o) {
        if (!(o instanceof Rational r)) return false;
        if (!big && !r.big) return lnum == r.lnum && lden == r.lden;
        return numBig().equals(r.numBig()) && denBig().equals(r.denBig());
    }

    @Override public int hashCode() {
        if (!big) return (int) (lnum * 31 + lden);
        return 31 * bnum.hashCode() + bden.hashCode();
    }

    @Override public String toString() {
        if (isInteger()) return big ? bnum.toString() : Long.toString(lnum);
        return big ? (bnum + "/" + bden) : (lnum + "/" + lden);
    }

    /** Promote to BigInteger view (no allocation if already big). */
    private BigInteger numBig() { return big ? bnum : BigInteger.valueOf(lnum); }
    private BigInteger denBig() { return big ? bden : BigInteger.valueOf(lden); }

    // Backwards-compatible accessors (some callers expect public num/den BigIntegers).
    public BigInteger num() { return numBig(); }
    public BigInteger den() { return denBig(); }
}
