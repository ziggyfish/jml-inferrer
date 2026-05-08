package com.z3x.parser;

import java.util.ArrayList;
import java.util.List;

/** Parses an SMT-LIB2 source into a sequence of top-level S-expression commands. */
public final class Parser {
    private final List<Token> tokens;
    private int pos;

    public Parser(List<Token> tokens) { this.tokens = tokens; }

    public static List<SExpr> parseAll(String src) {
        List<Token> toks = new Lexer(src).tokenize();
        return new Parser(toks).parseProgram();
    }

    public List<SExpr> parseProgram() {
        List<SExpr> commands = new ArrayList<>();
        while (peek().kind() != Token.Kind.EOF) commands.add(parseExpr());
        return commands;
    }

    public SExpr parseExpr() {
        Token t = peek();
        if (t.kind() == Token.Kind.LPAREN) {
            int line = t.line(), col = t.col();
            advance();
            List<SExpr> items = new ArrayList<>();
            while (peek().kind() != Token.Kind.RPAREN) {
                if (peek().kind() == Token.Kind.EOF) {
                    throw new Lexer.ParseException("Unterminated list", line, col);
                }
                items.add(parseExpr());
            }
            advance(); // consume )
            return new SExpr.SList(items, line, col);
        }
        if (t.kind() == Token.Kind.RPAREN) {
            throw new Lexer.ParseException("Unexpected )", t.line(), t.col());
        }
        advance();
        return new SExpr.Atom(t);
    }

    private Token peek() { return tokens.get(pos); }
    private void advance() { pos++; }
}
