/*
 * This file is part of the OpenJML project.
 * Adapted from the OpenJML-SeniorDesign quantifier project under GPLv2.
 * Original author: Sachin Shah.
 */
package org.jmlspecs.openjml.esc;

import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;

/**
 * Extracts the numeric bounds of a JML quantifier range expression.
 *
 * <p>A JML quantifier has the shape
 * {@code (\sum int k; <range>; <value>)}. To translate the quantifier to an
 * SMTLIB {@code define-fun-rec} we need to recover the low and high endpoints
 * of {@code <range>} -- for example, from {@code 0 <= k && k < arr.length} we
 * need {@code lo = 0} and {@code hi = arr.length}.</p>
 *
 * <p>The extractor handles compound conjunctions ({@code &&} / {@code &}) and
 * the four relational operators ({@code <}, {@code <=}, {@code >},
 * {@code >=}). Disjunctive and non-binary ranges aren't supported -- those
 * typically indicate infinite or unioned ranges the SMT encoding can't express
 * as a single recursive function.</p>
 */
public class JmlBoundsExtractor {

    protected static class Bounds {
        public JCExpression lo;
        public JCExpression hi;

        public Bounds(JCExpression lo, JCExpression hi) {
            this.lo = lo;
            this.hi = hi;
        }
    }

    /**
     * Returns true if the expression is a long/int literal equal to Integer.MIN_VALUE,
     * Integer.MAX_VALUE, Long.MIN_VALUE, or Long.MAX_VALUE. OpenJML auto-appends
     * these as redundant type-safety bounds to quantifier ranges; for sum/product/
     * num_of encoding we must filter them out so they don't collide with the real
     * user-supplied bounds.
     */
    private static boolean isIntegralTypeExtreme(JCExpression expr) {
        if (expr instanceof JCParens) {
            expr = ((JCParens) expr).getExpression();
        }
        if (!(expr instanceof JCLiteral)) return false;
        Object v = ((JCLiteral) expr).value;
        long val;
        if (v instanceof Integer) val = ((Integer) v).longValue();
        else if (v instanceof Long) val = (Long) v;
        else return false;
        return val == Integer.MIN_VALUE || val == Integer.MAX_VALUE
                || val == Long.MIN_VALUE || val == Long.MAX_VALUE;
    }

    /**
     * Extracts low and high from a single comparison (e.g. {@code X <= Y}).
     * For {@code <=} or {@code <}, lhs is the low and rhs is the high.
     * For {@code >=} or {@code >}, the order is reversed.
     *
     * Returns null for comparisons that are just the auto-appended type
     * boundary assertions (e.g. {@code k >= -2147483648L}) so the caller
     * merge logic ignores them.
     */
    public static Bounds extractSingleBound(JCBinary expr) {
        JCTree.Tag tag = expr.getTag();

        if (tag == JCTree.Tag.LE || tag == JCTree.Tag.LT) {
            if (isIntegralTypeExtreme(expr.lhs) || isIntegralTypeExtreme(expr.rhs)) {
                return null;
            }
            return new Bounds(expr.lhs, expr.rhs);
        }
        if (tag == JCTree.Tag.GE || tag == JCTree.Tag.GT) {
            if (isIntegralTypeExtreme(expr.lhs) || isIntegralTypeExtreme(expr.rhs)) {
                return null;
            }
            return new Bounds(expr.rhs, expr.lhs);
        }
        return null;
    }

    /** True if {@code expr} is a name occurring in the quantifier's declaration list. */
    public static boolean inDecls(List<JCVariableDecl> decls, JCExpression expr) {
        if (!(expr instanceof JCIdent)) {
            if ((expr instanceof JCParens))
                expr = ((JCParens) expr).getExpression();

            String exprStr = " " + expr.toString() + " ";
            for (JCVariableDecl decl : decls) {
                if (exprStr.contains(" " + decl.getName() + " ")) return true;
            }
            return false;
        }

        JCIdent ident = (JCIdent) expr;

        for (JCVariableDecl decl : decls) {
            if (decl.getName().equals(ident.name)) return true;
        }
        return false;
    }

    private static boolean isConjunctiveOperator(JCTree.Tag tag) {
        return tag == JCTree.Tag.AND || tag == JCTree.Tag.BITAND
                || tag == JCTree.Tag.OR || tag == JCTree.Tag.BITOR;
    }

    /**
     * Recursively extracts bounds from a range expression. At the root,
     * requires a conjunctive combiner ({@code &&} or {@code &}) because a
     * single comparison alone yields an unbounded half-open range (e.g. just
     * {@code k < n}) which the SMT encoding can't represent as a finite
     * recursive definition.
     *
     * @param decls the quantifier-bound variable declarations (e.g. {@code int k})
     * @param range the range expression to extract bounds from
     * @param isRoot true for the initial call -- enforces the conjunctive-combiner rule
     * @param smtTranslator the caller, used for reporting not-yet-implemented diagnostics
     */
    public static Bounds extract(List<JCVariableDecl> decls, JCExpression range,
                                  boolean isRoot, SMTTranslator smtTranslator) {
        if ((range instanceof JCParens)) {
            range = ((JCParens) range).getExpression();
        }

        if (!(range instanceof JCBinary)) {
            smtTranslator.notImplWarn(range, "The range expression is not binary.");
            return null;
        }

        JCBinary expr = (JCBinary) range;
        if (isRoot && !isConjunctiveOperator(expr.getTag())) {
            smtTranslator.notImplWarn(range,
                    "Range expressions without && or || are not supported because those " +
                    "expressions often result in infinite ranges.");
            return null;
        }

        if (isConjunctiveOperator(expr.getTag())) {
            TreeMaker treeMaker = TreeMaker.instance(smtTranslator.context);
            Bounds left = extract(decls, expr.lhs, false, smtTranslator);
            Bounds right = extract(decls, expr.rhs, false, smtTranslator);

            if (left == null) return right;
            if (right == null) return left;

            JCExpression lo;
            if (left.lo == null) {
                lo = right.lo;
            } else if (!inDecls(decls, left.lo) && inDecls(decls, right.lo)) {
                lo = left.lo;
            } else if (inDecls(decls, left.lo) && !inDecls(decls, right.lo)) {
                lo = right.lo;
            } else if (!inDecls(decls, left.lo) && !inDecls(decls, right.lo)) {
                lo = treeMaker.Conditional(treeMaker.Binary(JCTree.Tag.LT, left.lo, right.lo), left.lo, right.lo);
            } else {
                lo = null;
            }

            JCExpression hi;
            if (left.hi == null) {
                hi = right.hi;
            } else if (!inDecls(decls, left.hi) && inDecls(decls, right.hi)) {
                hi = left.hi;
            } else if (inDecls(decls, left.hi) && !inDecls(decls, right.hi)) {
                hi = right.hi;
            } else if (!inDecls(decls, left.hi) && !inDecls(decls, right.hi)) {
                hi = treeMaker.Conditional(treeMaker.Binary(JCTree.Tag.GT, left.hi, right.hi), left.hi, right.hi);
            } else {
                hi = null;
            }

            return new Bounds(lo, hi);
        }

        if (expr.getTag() == JCTree.Tag.LT ||
            expr.getTag() == JCTree.Tag.LE ||
            expr.getTag() == JCTree.Tag.GT ||
            expr.getTag() == JCTree.Tag.GE) {

            return extractSingleBound(expr);
        }

        return null;
    }
}
