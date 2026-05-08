package com.z3x.parser;

import java.util.List;

/** Parsed S-expression: an atom (text + token kind) or a list of S-expressions. */
public sealed interface SExpr {

    record Atom(Token token) implements SExpr {
        public String text() { return token.text(); }
        public Token.Kind kind() { return token.kind(); }
        @Override public String toString() { return token.text(); }
    }

    record SList(List<SExpr> items, int line, int col) implements SExpr {
        @Override public String toString() {
            StringBuilder sb = new StringBuilder("(");
            for (int i = 0; i < items.size(); i++) {
                if (i > 0) sb.append(' ');
                sb.append(items.get(i));
            }
            return sb.append(')').toString();
        }
    }

    default boolean isAtom() { return this instanceof Atom; }
    default boolean isList() { return this instanceof SList; }

    default String atomText() {
        if (this instanceof Atom a) return a.text();
        throw new IllegalStateException("Expected atom, got list: " + this);
    }

    default List<SExpr> listItems() {
        if (this instanceof SList l) return l.items();
        throw new IllegalStateException("Expected list, got atom: " + this);
    }
}
