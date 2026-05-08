package com.z3x.parser;

import java.util.ArrayList;
import java.util.List;

/** SMT-LIB2 lexer. Handles parens, symbols (incl. |quoted|), numerals, decimals, keywords, strings, ; comments. */
public final class Lexer {
    private final String src;
    private int pos;
    private int line = 1;
    private int col = 1;

    public Lexer(String src) { this.src = src; }

    public List<Token> tokenize() {
        List<Token> out = new ArrayList<>();
        while (true) {
            skipTrivia();
            if (pos >= src.length()) {
                out.add(new Token(Token.Kind.EOF, "", line, col));
                return out;
            }
            int startLine = line, startCol = col;
            char c = src.charAt(pos);
            if (c == '(') { advance(); out.add(new Token(Token.Kind.LPAREN, "(", startLine, startCol)); continue; }
            if (c == ')') { advance(); out.add(new Token(Token.Kind.RPAREN, ")", startLine, startCol)); continue; }
            if (c == '"') { out.add(string(startLine, startCol)); continue; }
            if (c == '|') { out.add(quotedSymbol(startLine, startCol)); continue; }
            if (c == ':') { out.add(keyword(startLine, startCol)); continue; }
            if (Character.isDigit(c)) { out.add(number(startLine, startCol)); continue; }
            if (c == '-' && pos + 1 < src.length() && Character.isDigit(src.charAt(pos + 1))) {
                out.add(number(startLine, startCol)); continue;
            }
            if (isSymbolStart(c)) { out.add(symbol(startLine, startCol)); continue; }
            throw new ParseException("Unexpected character '" + c + "'", startLine, startCol);
        }
    }

    private void skipTrivia() {
        while (pos < src.length()) {
            char c = src.charAt(pos);
            if (c == ' ' || c == '\t' || c == '\r') { advance(); }
            else if (c == '\n') { advance(); }
            else if (c == ';') { while (pos < src.length() && src.charAt(pos) != '\n') advance(); }
            else break;
        }
    }

    private Token string(int sl, int sc) {
        advance(); // opening "
        StringBuilder sb = new StringBuilder();
        while (pos < src.length()) {
            char c = src.charAt(pos);
            if (c == '"') {
                if (pos + 1 < src.length() && src.charAt(pos + 1) == '"') { sb.append('"'); advance(); advance(); }
                else { advance(); return new Token(Token.Kind.STRING, sb.toString(), sl, sc); }
            } else { sb.append(c); advance(); }
        }
        throw new ParseException("Unterminated string", sl, sc);
    }

    private Token quotedSymbol(int sl, int sc) {
        advance(); // opening |
        StringBuilder sb = new StringBuilder();
        while (pos < src.length() && src.charAt(pos) != '|') { sb.append(src.charAt(pos)); advance(); }
        if (pos >= src.length()) throw new ParseException("Unterminated |symbol|", sl, sc);
        advance(); // closing |
        return new Token(Token.Kind.SYMBOL, sb.toString(), sl, sc);
    }

    private Token keyword(int sl, int sc) {
        advance(); // :
        StringBuilder sb = new StringBuilder();
        while (pos < src.length() && isSymbolPart(src.charAt(pos))) { sb.append(src.charAt(pos)); advance(); }
        return new Token(Token.Kind.KEYWORD, sb.toString(), sl, sc);
    }

    private Token number(int sl, int sc) {
        StringBuilder sb = new StringBuilder();
        if (src.charAt(pos) == '-') { sb.append('-'); advance(); }
        while (pos < src.length() && Character.isDigit(src.charAt(pos))) { sb.append(src.charAt(pos)); advance(); }
        if (pos < src.length() && src.charAt(pos) == '.') {
            sb.append('.'); advance();
            while (pos < src.length() && Character.isDigit(src.charAt(pos))) { sb.append(src.charAt(pos)); advance(); }
            return new Token(Token.Kind.DECIMAL, sb.toString(), sl, sc);
        }
        return new Token(Token.Kind.NUMERAL, sb.toString(), sl, sc);
    }

    private Token symbol(int sl, int sc) {
        StringBuilder sb = new StringBuilder();
        while (pos < src.length() && isSymbolPart(src.charAt(pos))) { sb.append(src.charAt(pos)); advance(); }
        return new Token(Token.Kind.SYMBOL, sb.toString(), sl, sc);
    }

    private static boolean isSymbolStart(char c) {
        if (Character.isLetter(c)) return true;
        return "~!@$%^&*_+-=<>.?/#".indexOf(c) >= 0;
    }

    private static boolean isSymbolPart(char c) {
        if (Character.isLetterOrDigit(c)) return true;
        return "~!@$%^&*_+-=<>.?/#".indexOf(c) >= 0;
    }

    private void advance() {
        if (pos < src.length() && src.charAt(pos) == '\n') { line++; col = 1; }
        else { col++; }
        pos++;
    }

    public static final class ParseException extends RuntimeException {
        public final int line, col;
        public ParseException(String msg, int line, int col) {
            super(msg + " at " + line + ":" + col);
            this.line = line; this.col = col;
        }
    }
}
