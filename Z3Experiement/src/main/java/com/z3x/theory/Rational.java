package com.z3x.theory;

import java.math.BigInteger;

/**
 * Exact-precision rational number. Stored as numerator/denominator with denominator > 0
 * and gcd(|num|, den) = 1. Immutable.
 */
public final class Rational implements Comparable<Rational> {

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE);
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE);
    public static final Rational MINUS_ONE = new Rational(BigInteger.ONE.negate(), BigInteger.ONE);

    public final BigInteger num;
    public final BigInteger den;

    private Rational(BigInteger num, BigInteger den) {
        this.num = num;
        this.den = den;
    }

    public static Rational of(long n) {
        return new Rational(BigInteger.valueOf(n), BigInteger.ONE);
    }

    public static Rational of(BigInteger n) {
        return new Rational(n, BigInteger.ONE);
    }

    public static Rational of(BigInteger num, BigInteger den) {
        if (den.signum() == 0) throw new ArithmeticException("zero denominator");
        if (den.signum() < 0) { num = num.negate(); den = den.negate(); }
        BigInteger g = num.abs().gcd(den);
        if (!g.equals(BigInteger.ONE)) { num = num.divide(g); den = den.divide(g); }
        return new Rational(num, den);
    }

    public Rational add(Rational o) {
        return of(num.multiply(o.den).add(o.num.multiply(den)), den.multiply(o.den));
    }

    public Rational sub(Rational o) {
        return of(num.multiply(o.den).subtract(o.num.multiply(den)), den.multiply(o.den));
    }

    public Rational mul(Rational o) {
        return of(num.multiply(o.num), den.multiply(o.den));
    }

    public Rational div(Rational o) {
        if (o.signum() == 0) throw new ArithmeticException("divide by zero");
        return of(num.multiply(o.den), den.multiply(o.num));
    }

    public Rational negate() { return new Rational(num.negate(), den); }

    public Rational abs() { return num.signum() < 0 ? negate() : this; }

    public int signum() { return num.signum(); }

    public boolean isZero() { return num.signum() == 0; }

    public boolean isInteger() { return den.equals(BigInteger.ONE); }

    public BigInteger floor() {
        BigInteger[] qr = num.divideAndRemainder(den);
        if (qr[1].signum() < 0) return qr[0].subtract(BigInteger.ONE);
        return qr[0];
    }

    public BigInteger ceil() {
        BigInteger[] qr = num.divideAndRemainder(den);
        if (qr[1].signum() > 0) return qr[0].add(BigInteger.ONE);
        return qr[0];
    }

    @Override public int compareTo(Rational o) {
        return num.multiply(o.den).compareTo(o.num.multiply(den));
    }

    public boolean lt(Rational o) { return compareTo(o) < 0; }
    public boolean le(Rational o) { return compareTo(o) <= 0; }
    public boolean gt(Rational o) { return compareTo(o) > 0; }
    public boolean ge(Rational o) { return compareTo(o) >= 0; }

    @Override public boolean equals(Object o) {
        return o instanceof Rational r && num.equals(r.num) && den.equals(r.den);
    }

    @Override public int hashCode() { return 31 * num.hashCode() + den.hashCode(); }

    @Override public String toString() {
        if (isInteger()) return num.toString();
        return num + "/" + den;
    }
}
