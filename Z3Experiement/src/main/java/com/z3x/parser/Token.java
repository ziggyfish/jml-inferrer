package com.z3x.parser;

public record Token(Kind kind, String text, int line, int col) {
    public enum Kind { LPAREN, RPAREN, SYMBOL, NUMERAL, DECIMAL, STRING, KEYWORD, EOF }

    @Override
    public String toString() {
        return kind + "(" + text + ")@" + line + ":" + col;
    }
}
