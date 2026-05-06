package com.jml.spec;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class JmlCanonicaliserTest {

    @Test
    @DisplayName("Whitespace runs collapse to single space")
    void whitespaceCollapse() {
        assertEquals("a + b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a   +    b"));
        assertEquals("a + b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a\t+\nb"));
    }

    @Test
    @DisplayName("Leading and trailing whitespace stripped")
    void leadingTrailingStripped() {
        assertEquals("p != null", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "  p != null  "));
    }

    @Test
    @DisplayName("No spaces inside parens, before commas")
    void parensAndCommas() {
        assertEquals("f(a, b)", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "f( a , b )"));
        assertEquals("arr[i]", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "arr[ i ]"));
    }

    @Test
    @DisplayName("Single space around binary operators")
    void binaryOperators() {
        assertEquals("a == b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a==b"));
        assertEquals("a + b * c", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a+b*c"));
        assertEquals("a && b || c", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a&&b||c"));
    }

    @Test
    @DisplayName("No space around dot")
    void dotAccess() {
        assertEquals("this.field", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "this . field"));
        assertEquals("a.b.c", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a . b . c"));
    }

    @Test
    @DisplayName("Implication arrows canonicalised to long form")
    void arrowsCanonicalised() {
        assertEquals("a ==> b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a => b"));
        assertEquals("a <==> b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a <=> b"));
    }

    @Test
    @DisplayName("Implication already in long form preserved")
    void longArrowPreserved() {
        assertEquals("a ==> b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a==>b"));
        assertEquals("a <==> b", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "a<==>b"));
    }

    @Test
    @DisplayName("JML keywords with backslash recognised as identifiers")
    void jmlKeywords() {
        assertEquals("\\result == p", JmlCanonicaliser.canonicalise(Kind.ENSURES, "\\result==p"));
        assertEquals("\\old(this.field)", JmlCanonicaliser.canonicalise(Kind.ENSURES, "\\old( this . field )"));
    }

    @Test
    @DisplayName("Method call has no space before paren")
    void methodCallNoSpace() {
        assertEquals("arr.length", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "arr.length"));
        assertEquals("f(x)", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "f( x )"));
    }

    @Test
    @DisplayName("Quantifier shape preserved with canonical spacing")
    void quantifier() {
        assertEquals("(\\forall int k; 0 <= k && k < n; arr[k] != null)",
                JmlCanonicaliser.canonicalise(Kind.REQUIRES,
                        "(\\forall  int  k;  0<=k&&k<n;  arr[k]!=null)"));
    }

    @Test
    @DisplayName("Sum quantifier with body preserves spacing")
    void sumQuantifier() {
        assertEquals("(\\sum int k; 0 <= k && k < n; arr[k])",
                JmlCanonicaliser.canonicalise(Kind.ENSURES,
                        "(\\sum int k;0<=k&&k<n;arr[k])"));
    }

    @Test
    @DisplayName("Idempotent: canonicalise twice gives same result")
    void idempotent() {
        String s = "(\\forall int k; 0 <= k && k < this.size; this.data[k] != null)";
        String once = JmlCanonicaliser.canonicalise(Kind.REQUIRES, s);
        String twice = JmlCanonicaliser.canonicalise(Kind.REQUIRES, once);
        assertEquals(once, twice);
    }

    @Test
    @DisplayName("equalsCanonical reports two whitespace-different strings as equal")
    void equalsCanonicalCompares() {
        assertTrue(JmlCanonicaliser.equalsCanonical("a == b", "a==b"));
        assertTrue(JmlCanonicaliser.equalsCanonical("a => b", "a ==> b"));
        assertFalse(JmlCanonicaliser.equalsCanonical("a > b", "b < a"),
                "semantic equivalence is NOT the canonicaliser's job");
    }

    @Test
    @DisplayName("renderClause prepends the kind keyword")
    void renderClauseAddsKeyword() {
        assertEquals("requires p != null",
                JmlCanonicaliser.renderClause(Kind.REQUIRES, "p!=null"));
        assertEquals("ensures \\result == p + 1",
                JmlCanonicaliser.renderClause(Kind.ENSURES, "\\result==p+1"));
        assertEquals("assignable \\nothing",
                JmlCanonicaliser.renderClause(Kind.ASSIGNABLE, "\\nothing"));
    }

    @Test
    @DisplayName("Null and empty input handled gracefully")
    void nullAndEmpty() {
        assertNull(JmlCanonicaliser.canonicalise(Kind.REQUIRES, null));
        assertEquals("", JmlCanonicaliser.canonicalise(Kind.REQUIRES, ""));
        assertEquals("", JmlCanonicaliser.canonicalise(Kind.REQUIRES, "   "));
    }

    @Test
    @DisplayName("Negative integer literal preserves no-space-after-minus when unary")
    void unaryMinusLiteral() {
        // Inside a comparison: `i >= -1` — the - is unary on 1, a >= is binary
        String result = JmlCanonicaliser.canonicalise(Kind.REQUIRES, "i  >=  -1");
        assertEquals("i >= -1", result);
    }
}
