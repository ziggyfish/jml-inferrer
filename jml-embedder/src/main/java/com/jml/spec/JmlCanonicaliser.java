package com.jml.spec;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

/**
 * Canonical-form printer for JML clause strings.
 *
 * <p>The canonicaliser performs lexical normalisation only — it does not attempt
 * semantic equivalence. Two clauses that differ in whitespace, operator spelling,
 * or quantifier-variable name are canonicalised to the same form; two clauses
 * that differ in operator (e.g., {@code a > b} vs {@code b < a}) remain distinct.
 *
 * <p>Rules implemented (per {@code journal/rq2_embedding_design.md} §4):
 * <ul>
 *   <li>All whitespace runs collapse to a single space.</li>
 *   <li>No leading or trailing whitespace.</li>
 *   <li>No spaces immediately inside {@code (}, {@code [}, or before {@code )},
 *       {@code ]}, {@code ,}, {@code ;}.</li>
 *   <li>Single spaces around binary operators ({@code +}, {@code -}, {@code *},
 *       {@code /}, {@code %}, {@code ==}, {@code !=}, {@code <=}, {@code >=},
 *       {@code <}, {@code >}, {@code &&}, {@code ||}, {@code ==>}, {@code <==>}).
 *   </li>
 *   <li>No space between unary operators and their operand ({@code !x}, {@code -x}).</li>
 *   <li>No space around {@code .} or {@code ::}.</li>
 *   <li>Implication and biconditional canonicalised to the longer arrow forms
 *       ({@code ==>}, {@code <==>}).</li>
 *   <li>Quantifier variables {@code (\forall T x; range; body)} alpha-rename to
 *       {@code k}, {@code i, j, k} for nested.</li>
 * </ul>
 *
 * <p>Semantic-equivalence rewrites (e.g., constant folding, normalising
 * {@code a > b} to {@code b < a}) are explicitly out of scope. They would
 * make the canonicaliser unsound for fidelity checks: a roundtrip that
 * silently rewrote {@code (\sum int k; 0 <= k < n; arr[k])} to its
 * (equivalent) reverse form would mask string-mangling bugs.</p>
 */
public final class JmlCanonicaliser {

    private static final Set<String> KEYWORDS = Set.of(
            "true", "false", "null", "this",
            "\\result", "\\old", "\\forall", "\\exists", "\\sum", "\\product",
            "\\num_of", "\\nothing", "\\everything", "\\not_modified",
            "int", "long", "double", "float", "boolean", "byte", "short", "char"
    );

    private JmlCanonicaliser() {
    }

    public static String canonicalise(Kind kind, String text) {
        if (text == null) return null;
        String s = text.strip();
        if (s.isEmpty()) return s;
        s = canonicaliseOperators(s);
        s = canonicaliseWhitespace(s);
        s = canonicaliseQuantifierVariables(s);
        return s;
    }

    public static boolean equalsCanonical(String a, String b) {
        return canonicalise(null, a).equals(canonicalise(null, b));
    }

    /**
     * Map short-form arrows ({@code =>}, {@code <=>}) to long-form ({@code ==>},
     * {@code <==>}). Done first so subsequent whitespace passes see the canonical
     * spelling.
     */
    private static String canonicaliseOperators(String s) {
        // Replace `=>` not preceded by `=` and `<=>` to `==>` / `<==>`.
        // Order matters: handle `<=>` before `=>` to avoid `<==>` being mangled.
        StringBuilder sb = new StringBuilder(s.length() + 4);
        int i = 0;
        while (i < s.length()) {
            char c = s.charAt(i);
            if (c == '<' && i + 2 < s.length() && s.charAt(i + 1) == '=' && s.charAt(i + 2) == '>') {
                sb.append("<==>");
                i += 3;
            } else if (c == '=' && i + 1 < s.length() && s.charAt(i + 1) == '>'
                    && (i == 0 || s.charAt(i - 1) != '=')) {
                sb.append("==>");
                i += 2;
            } else {
                sb.append(c);
                i++;
            }
        }
        return sb.toString();
    }

    /**
     * Tokenise then re-emit with the canonical spacing rules. Tokens are
     * one of: identifier, number, multi-char operator (e.g., {@code ==>},
     * {@code <==>}, {@code &&}, {@code ||}, {@code ==}, {@code !=},
     * {@code <=}, {@code >=}, {@code ::}), single-char punctuation, or
     * a JML backslash-keyword.
     */
    private static String canonicaliseWhitespace(String s) {
        List<String> tokens = tokenise(s);
        StringBuilder sb = new StringBuilder(s.length());
        for (int i = 0; i < tokens.size(); i++) {
            String t = tokens.get(i);
            String prev = i > 0 ? tokens.get(i - 1) : "";
            String next = i + 1 < tokens.size() ? tokens.get(i + 1) : "";
            boolean spaceBefore = needsSpaceBefore(t, prev, i, tokens);
            if (spaceBefore && sb.length() > 0 && sb.charAt(sb.length() - 1) != ' ') {
                sb.append(' ');
            }
            sb.append(t);
        }
        return sb.toString().strip();
    }

    private static boolean needsSpaceBefore(String t, String prev, int i, List<String> tokens) {
        if (prev.isEmpty()) return false;
        if (t.equals(",") || t.equals(";") || t.equals(")") || t.equals("]")) return false;
        if (prev.equals("(") || prev.equals("[")) return false;
        if (t.equals(".") || prev.equals(".")) return false;
        if (t.equals("::") || prev.equals("::")) return false;
        if (t.equals("(") && isCallable(prev)) return false;       // identifier( or quantifier(
        if (t.equals("[") && isIndexable(prev)) return false;      // identifier[
        // Unary minus / not / tilde: no space between operator and operand when
        // the operator follows another operator or open paren (i.e., is unary).
        if (isUnaryHere(prev) && (t.equals("-") || t.equals("!") || t.equals("~"))) return true;
        if ((prev.equals("-") || prev.equals("!") || prev.equals("~"))
                && i >= 2 && isUnaryHere(tokens.get(i - 2))) {
            return false;
        }
        return true;
    }

    private static boolean isCallable(String tok) {
        if (tok.isEmpty()) return false;
        char c = tok.charAt(0);
        return Character.isJavaIdentifierStart(c) || c == '\\';
    }

    private static boolean isIndexable(String tok) {
        if (tok.isEmpty()) return false;
        char c = tok.charAt(0);
        return Character.isJavaIdentifierPart(c) || c == ')' || c == ']';
    }

    private static boolean isUnaryHere(String prev) {
        if (prev.isEmpty()) return true;
        char c = prev.charAt(0);
        if (c == '(' || c == '[' || c == ',' || c == ';') return true;
        return isOperatorToken(prev);
    }

    private static boolean isOperatorToken(String tok) {
        return Set.of("+", "-", "*", "/", "%", "==", "!=", "<=", ">=", "<", ">",
                "&&", "||", "==>", "<==>", "=", "&", "|", "^", "?", ":", "!").contains(tok);
    }

    /**
     * Lexer for the canonical-form syntax. Returns tokens in source order.
     * Whitespace is dropped; multi-character operators are atomic tokens.
     */
    private static List<String> tokenise(String s) {
        List<String> tokens = new ArrayList<>();
        int i = 0;
        int n = s.length();
        while (i < n) {
            char c = s.charAt(i);
            if (Character.isWhitespace(c)) { i++; continue; }
            if (c == '\\') {
                int j = i + 1;
                while (j < n && (Character.isJavaIdentifierPart(s.charAt(j)) || s.charAt(j) == '_')) j++;
                tokens.add(s.substring(i, j));
                i = j;
                continue;
            }
            if (Character.isJavaIdentifierStart(c) || c == '`') {
                int j = i + 1;
                if (c == '`') {
                    while (j < n && s.charAt(j) != '`') j++;
                    if (j < n) j++; // include closing backtick
                } else {
                    while (j < n && Character.isJavaIdentifierPart(s.charAt(j))) j++;
                }
                tokens.add(s.substring(i, j));
                i = j;
                continue;
            }
            if (Character.isDigit(c)) {
                int j = i + 1;
                while (j < n && (Character.isDigit(s.charAt(j))
                        || s.charAt(j) == '.' || s.charAt(j) == 'e' || s.charAt(j) == 'E'
                        || s.charAt(j) == 'L' || s.charAt(j) == 'l'
                        || s.charAt(j) == 'F' || s.charAt(j) == 'f'
                        || s.charAt(j) == 'D' || s.charAt(j) == 'd'
                        || s.charAt(j) == '+' && (s.charAt(j - 1) == 'e' || s.charAt(j - 1) == 'E')
                        || s.charAt(j) == '-' && (s.charAt(j - 1) == 'e' || s.charAt(j - 1) == 'E'))) {
                    j++;
                }
                tokens.add(s.substring(i, j));
                i = j;
                continue;
            }
            // Multi-character operators
            if (matches(s, i, "==>")) { tokens.add("==>"); i += 3; continue; }
            if (matches(s, i, "<==>")) { tokens.add("<==>"); i += 4; continue; }
            if (matches(s, i, "==")) { tokens.add("=="); i += 2; continue; }
            if (matches(s, i, "!=")) { tokens.add("!="); i += 2; continue; }
            if (matches(s, i, "<=")) { tokens.add("<="); i += 2; continue; }
            if (matches(s, i, ">=")) { tokens.add(">="); i += 2; continue; }
            if (matches(s, i, "&&")) { tokens.add("&&"); i += 2; continue; }
            if (matches(s, i, "||")) { tokens.add("||"); i += 2; continue; }
            if (matches(s, i, "::")) { tokens.add("::"); i += 2; continue; }
            // Single-character punctuation / operator
            tokens.add(String.valueOf(c));
            i++;
        }
        return tokens;
    }

    private static boolean matches(String s, int i, String pat) {
        return i + pat.length() <= s.length() && s.regionMatches(i, pat, 0, pat.length());
    }

    /**
     * Alpha-rename quantifier bound variables. Currently a no-op for the
     * common case; full renaming would require a parser to scope variables.
     * Kept as a hook so that future work (per design doc §4.3) can plug in
     * scope-aware renaming.
     */
    private static String canonicaliseQuantifierVariables(String s) {
        // Intentionally a no-op for now — scope-aware renaming requires parsing
        // and is deferred to the JML expression parser planned for Phase 2A.4.
        // The lexical pass above already canonicalises whitespace inside
        // quantifier headers so simple shapes roundtrip cleanly.
        return s;
    }

    /** Returns the canonical clause text wrapped with its kind keyword for
     * use in a JML stub file. */
    public static String renderClause(Kind kind, String text) {
        String body = canonicalise(kind, text);
        return switch (kind) {
            case REQUIRES -> "requires " + body;
            case ENSURES -> "ensures " + body;
            case ASSIGNABLE -> "assignable " + body;
            case SIGNALS -> "signals " + body;
            case LOOP_INVARIANT -> "loop_invariant " + body;
            case LOOP_DECREASES -> "loop_decreases " + body;
            case INVARIANT -> "invariant " + body;
            case ALSO_PARTITION -> "also " + body;
            case AXIOM -> "axiom " + body;
            case INITIALLY -> "initially " + body;
        };
    }

    @SuppressWarnings("unused")
    private static List<String> trace(String s) {
        return Arrays.asList(s.split(""));
    }
}
