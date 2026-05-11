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

    record Array(Sort domain, Sort range) implements Sort {
        @Override public String name() { return "(Array " + domain + " " + range + ")"; }
        @Override public String toString() { return name(); }
    }

    /** Algebraic datatype sort. */
    record Datatype(String name, List<Constructor> constructors) implements Sort {
        @Override public String toString() { return name; }
    }

    record Constructor(String name, List<Selector> selectors) {}
    record Selector(String name, Sort sort) {}

    static Sort fromAtomName(String s) {
        return switch (s) {
            case "Bool"   -> BOOL;
            case "Int"    -> INT;
            case "Real"   -> REAL;
            case "String" -> STRING;
            default       -> null;
        };
    }

    static boolean equal(Sort a, Sort b) { return Objects.equals(a, b); }

    /** Function signature: arg sorts + result sort. */
    record FunSig(List<Sort> args, Sort result) {}
}
