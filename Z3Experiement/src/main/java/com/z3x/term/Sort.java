package com.z3x.term;

import java.util.List;
import java.util.Objects;

/** Type / sort. Built-in: Bool, Int, Real. Plus uninterpreted (user-declared) sorts. */
public sealed interface Sort {

    String name();

    Sort BOOL = new Builtin("Bool");
    Sort INT  = new Builtin("Int");
    Sort REAL = new Builtin("Real");
    Sort STRING = new Builtin("String");

    record Builtin(String name) implements Sort {
        @Override public String toString() { return name; }
    }

    record Uninterp(String name, int arity) implements Sort {
        @Override public String toString() { return name; }
    }

    record BitVec(int width) implements Sort {
        @Override public String name() { return "(_ BitVec " + width + ")"; }
        @Override public String toString() { return name(); }
    }

    /** IEEE-754 binary floating-point sort, parameterized by exponent and significand widths. */
    record FloatingPoint(int eb, int sb) implements Sort {
        @Override public String name() { return "(_ FloatingPoint " + eb + " " + sb + ")"; }
        @Override public String toString() { return name(); }
    }

    /** SMT-LIB rounding mode (RNE, RNA, RTP, RTN, RTZ). */
    Sort ROUNDING_MODE = new Builtin("RoundingMode");

    record Array(Sort domain, Sort range) implements Sort {
        @Override public String name() { return "(Array " + domain + " " + range + ")"; }
        @Override public String toString() { return name(); }
    }

    /** SMT-LIB Sequences theory: parameterized by the element sort. */
    record Seq(Sort element) implements Sort {
        @Override public String name() { return "(Seq " + element + ")"; }
        @Override public String toString() { return name(); }
    }

    /** SMT-LIB Regular Expressions theory. (RegLan in SMT-LIB.) */
    Sort REGEX = new Builtin("RegLan");

    /** Algebraic datatype sort. Identity = name (so a placeholder during declaration is
     *  interchangeable with the final-ctors version). */
    final class Datatype implements Sort {
        private final String name;
        private List<Constructor> constructors;
        public Datatype(String name, List<Constructor> constructors) {
            this.name = name;
            this.constructors = constructors;
        }
        @Override public String name() { return name; }
        public List<Constructor> constructors() { return constructors; }
        public void setConstructors(List<Constructor> c) { this.constructors = c; }
        @Override public boolean equals(Object o) { return o instanceof Datatype d && d.name.equals(name); }
        @Override public int hashCode() { return name.hashCode(); }
        @Override public String toString() { return name; }
    }

    record Constructor(String name, List<Selector> selectors) {}
    record Selector(String name, Sort sort) {}

    static Sort fromAtomName(String s) {
        return switch (s) {
            case "Bool"         -> BOOL;
            case "Int"          -> INT;
            case "Real"         -> REAL;
            case "String"       -> STRING;
            case "RegLan"       -> REGEX;
            case "RoundingMode" -> ROUNDING_MODE;
            // Aliases for FP common widths.
            case "Float16"      -> new FloatingPoint(5, 11);
            case "Float32"      -> new FloatingPoint(8, 24);
            case "Float64"      -> new FloatingPoint(11, 53);
            case "Float128"     -> new FloatingPoint(15, 113);
            default             -> null;
        };
    }

    static boolean equal(Sort a, Sort b) { return Objects.equals(a, b); }

    /** Function signature: arg sorts + result sort. */
    record FunSig(List<Sort> args, Sort result) {}
}
