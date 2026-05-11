package com.z3x.term;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;

/**
 * Hash-consed term hierarchy. All construction goes through {@link TermFactory} so that
 * structurally equal terms share an identity (and hence an integer id used downstream
 * by the E-graph and SAT layers).
 *
 * Equality is reference equality once hash-consed. {@link #equals(Object)} and
 * {@link #hashCode()} use the assigned id so terms can also live in plain HashMaps
 * after construction.
 */
public abstract sealed class Term {

    /** Stable id assigned by {@link TermFactory}. */
    public final int id;
    public final Sort sort;

    protected Term(int id, Sort sort) {
        this.id = id;
        this.sort = sort;
    }

    public abstract List<Term> children();

    /** Symbol/operator name for printing. */
    public abstract String head();

    @Override public final int hashCode() { return id; }

    @Override public final boolean equals(Object o) {
        return o instanceof Term t && t.id == id;
    }

    @Override public String toString() {
        if (children().isEmpty()) return head();
        StringBuilder sb = new StringBuilder("(").append(head());
        for (Term c : children()) sb.append(' ').append(c);
        return sb.append(')').toString();
    }

    // ---------- concrete term classes ----------

    /** A free variable (declare-const) or an argument-applied function symbol with zero args. */
    public static final class Var extends Term {
        public final String name;
        public Var(int id, String name, Sort sort) { super(id, sort); this.name = name; }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return name; }
    }

    public static final class BoolConst extends Term {
        public final boolean value;
        public BoolConst(int id, boolean value) { super(id, Sort.BOOL); this.value = value; }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return value ? "true" : "false"; }
    }

    public static final class IntConst extends Term {
        public final BigInteger value;
        public IntConst(int id, BigInteger value) { super(id, Sort.INT); this.value = value; }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return value.toString(); }
    }

    public static final class RatConst extends Term {
        public final BigInteger num, den; // den > 0, gcd(num, |den|) = 1
        public RatConst(int id, BigInteger num, BigInteger den) {
            super(id, Sort.REAL);
            if (den.signum() == 0) throw new IllegalArgumentException("zero denominator");
            this.num = num;
            this.den = den;
        }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return num + "/" + den; }
    }

    /** Application of a named symbol (could be uninterpreted or a built-in). */
    public static final class BvConst extends Term {
        public final BigInteger value;
        public final int width;
        public BvConst(int id, BigInteger value, int width) {
            super(id, new Sort.BitVec(width));
            this.value = value;
            this.width = width;
        }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return "(_ bv" + value + " " + width + ")"; }
    }

    /** Universal or existential quantifier. */
    public static final class Quantifier extends Term {
        public enum Kind { FORALL, EXISTS }
        public final Kind kind;
        public final List<String> boundNames;
        public final List<Sort> boundSorts;
        public final Term body;
        public Quantifier(int id, Kind kind, List<String> names, List<Sort> sorts, Term body) {
            super(id, Sort.BOOL);
            this.kind = kind;
            this.boundNames = List.copyOf(names);
            this.boundSorts = List.copyOf(sorts);
            this.body = body;
        }
        @Override public List<Term> children() { return List.of(body); }
        @Override public String head() { return kind == Kind.FORALL ? "forall" : "exists"; }
        @Override public String toString() {
            StringBuilder sb = new StringBuilder("(").append(head()).append(" (");
            for (int i = 0; i < boundNames.size(); i++) {
                if (i > 0) sb.append(' ');
                sb.append('(').append(boundNames.get(i)).append(' ').append(boundSorts.get(i)).append(')');
            }
            return sb.append(") ").append(body).append(')').toString();
        }
    }

    /** IEEE-754 floating-point literal. Stored as packed bits (sign:1, exp:eb, sig:sb-1). */
    public static final class FpConst extends Term {
        public final boolean sign;
        public final java.math.BigInteger exp; // unsigned exponent bits
        public final java.math.BigInteger sig; // unsigned significand bits (without hidden 1)
        public final int eb, sb;
        /** Tag for special values. */
        public enum Kind { NORMAL, PLUS_ZERO, MINUS_ZERO, PLUS_INF, MINUS_INF, NAN }
        public final Kind kind;
        public FpConst(int id, boolean sign, java.math.BigInteger exp, java.math.BigInteger sig, int eb, int sb, Kind kind) {
            super(id, new Sort.FloatingPoint(eb, sb));
            this.sign = sign; this.exp = exp; this.sig = sig; this.eb = eb; this.sb = sb; this.kind = kind;
        }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() {
            return switch (kind) {
                case PLUS_ZERO  -> "(_ +zero "  + eb + " " + sb + ")";
                case MINUS_ZERO -> "(_ -zero "  + eb + " " + sb + ")";
                case PLUS_INF   -> "(_ +oo "    + eb + " " + sb + ")";
                case MINUS_INF  -> "(_ -oo "    + eb + " " + sb + ")";
                case NAN        -> "(_ NaN "    + eb + " " + sb + ")";
                default         -> "(fp " + (sign ? "#b1" : "#b0") + " #b" + exp.toString(2) + " #b" + sig.toString(2) + ")";
            };
        }
    }

    /** Rounding mode constant: RNE, RNA, RTP, RTN, RTZ. */
    public static final class RmConst extends Term {
        public enum Mode { RNE, RNA, RTP, RTN, RTZ }
        public final Mode mode;
        public RmConst(int id, Mode mode) { super(id, Sort.ROUNDING_MODE); this.mode = mode; }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return mode.name(); }
    }

    public static final class StrConst extends Term {
        public final String value;
        public StrConst(int id, String value) { super(id, Sort.STRING); this.value = value; }
        @Override public List<Term> children() { return List.of(); }
        @Override public String head() { return "\"" + value.replace("\"", "\\\"") + "\""; }
    }

    public static final class App extends Term {
        public final String symbol;
        public final List<Term> args;
        public App(int id, String symbol, List<Term> args, Sort sort) {
            super(id, sort);
            this.symbol = symbol;
            this.args = List.copyOf(args);
        }
        @Override public List<Term> children() { return args; }
        @Override public String head() { return symbol; }
    }

    // ---------- structural keys for hash-consing ----------

    /** Internal key used by {@link TermFactory} to look up existing nodes. */
    public sealed interface Key {
        record VarK(String name, Sort sort) implements Key {}
        record BoolK(boolean v) implements Key {}
        record IntK(BigInteger v) implements Key {}
        record RatK(BigInteger n, BigInteger d) implements Key {}
        record AppK(String symbol, List<Integer> argIds, Sort sort) implements Key {
            public AppK { argIds = List.copyOf(argIds); }
        }
        record BvK(BigInteger v, int w) implements Key {}
        record QuantK(Quantifier.Kind k, List<String> names, List<Sort> sorts, int bodyId) implements Key {
            public QuantK { names = List.copyOf(names); sorts = List.copyOf(sorts); }
        }
        record StrK(String value) implements Key {}
        record FpK(boolean sign, java.math.BigInteger exp, java.math.BigInteger sig, int eb, int sb, FpConst.Kind kind) implements Key {}
        record RmK(RmConst.Mode mode) implements Key {}
    }

    public static int hash(Key k) { return Objects.hashCode(k); }
}
