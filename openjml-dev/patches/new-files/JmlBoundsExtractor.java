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
 * SMTLIB function we need to recover the low and high endpoints of
 * {@code <range>} -- for example, from {@code 0 <= k && k < arr.length} we
 * need {@code lo = 0, hi = arr.length} with hi exclusive; from
 * {@code 1 <= k && k <= n} we need {@code lo = 1, hi = n+1} (so the high end
 * is uniformly exclusive in the SMT encoding).</p>
 *
 * <p>The extractor handles compound conjunctions ({@code &&} / {@code &}) and
 * the four relational operators ({@code <}, {@code <=}, {@code >},
 * {@code >=}). Disjunctive and non-binary ranges aren't supported -- those
 * typically indicate infinite or unioned ranges the SMT encoding can't express
 * as a single function.</p>
 */
public class JmlBoundsExtractor {

    protected static class Bounds {
        public JCExpression lo;
        public JCExpression hi;
        /** When true, the user wrote {@code k <= hi} (inclusive). The SMT
         *  encoding uses an exclusive upper bound, so the caller must add 1
         *  when emitting the call site. We keep the raw user-supplied
         *  expression here rather than synthesising a {@code hi + 1} JCExpression
         *  because OpenJML's TreeMaker requires a Context to do so cleanly. */
        public boolean hiInclusive;
        /** When true, the user wrote {@code lo > k} or similar yielding an
         *  exclusive lower bound; SMT encoding's lower bound is inclusive, so
         *  add 1. The cases of {@code lo < k} can occur in normal-form
         *  ranges -- e.g. {@code 0 < k && k < n} for a sum starting at 1. */
        public boolean loExclusive;

        public Bounds(JCExpression lo, JCExpression hi) {
            this.lo = lo;
            this.hi = hi;
            this.hiInclusive = false;
            this.loExclusive = false;
        }

        public Bounds(JCExpression lo, JCExpression hi, boolean loExclusive, boolean hiInclusive) {
            this.lo = lo;
            this.hi = hi;
            this.hiInclusive = hiInclusive;
            this.loExclusive = loExclusive;
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
     * Extracts low and high from a single comparison. Marks inclusive/exclusive
     * for the high bound and exclusive for the low bound when applicable.
     *
     * Returns null for comparisons that are just the auto-appended type
     * boundary assertions (e.g. {@code k >= -2147483648L}) so the caller
     * merge logic ignores them.
     *
     * Examples:
     *   k <  hi  ->  Bounds(?, hi, false, false)   // hi exclusive (SMT default)
     *   k <= hi  ->  Bounds(?, hi, false, true )   // hi inclusive (caller adds +1)
     *   lo <= k  ->  Bounds(lo, ?, false, false)
     *   lo <  k  ->  Bounds(lo, ?, true,  false)   // lo exclusive (caller adds +1)
     *   hi >  k  ->  Bounds(?, hi, false, false)   // same as k < hi
     *   hi >= k  ->  Bounds(?, hi, false, true )   // same as k <= hi
     */
    public static Bounds extractSingleBound(JCBinary expr) {
        JCTree.Tag tag = expr.getTag();

        if (tag == JCTree.Tag.LE || tag == JCTree.Tag.LT) {
            if (isIntegralTypeExtreme(expr.lhs) || isIntegralTypeExtreme(expr.rhs)) {
                return null;
            }
            // lhs <= rhs   means lhs is the lo-bound, rhs is the hi-bound.
            // The hi side is inclusive iff <= ; the lo side is exclusive iff <
            // (i.e. when lhs IS the bound being applied as a strict inequality).
            // For lhs <  rhs : if lhs is the variable, lo = lhs is exclusive;
            //                  if rhs is the variable, hi = rhs is exclusive.
            // We don't know which side is the variable here -- the caller
            // disambiguates via inDecls(). So we mark the bound flags
            // syntactically: hi side is inclusive iff <= ; lo side is exclusive
            // iff < . The caller selects the right flag based on which side
            // is the bound variable.
            boolean inclusive = (tag == JCTree.Tag.LE);
            // hi (rhs) is inclusive iff op is <=
            // lo (lhs) is exclusive iff op is <  (since k < lo means lo is excluded
            //                                     -- but we'd need lhs to BE the
            //                                     variable for that interpretation;
            //                                     it's not the case here. Instead
            //                                     "lhs < rhs" with lhs=lo means
            //                                     "lo < k", i.e. lo is exclusive
            //                                     for the variable's range.)
            return new Bounds(expr.lhs, expr.rhs, !inclusive, inclusive);
        }
        if (tag == JCTree.Tag.GE || tag == JCTree.Tag.GT) {
            if (isIntegralTypeExtreme(expr.lhs) || isIntegralTypeExtreme(expr.rhs)) {
                return null;
            }
            // lhs >= rhs   <==>   rhs <= lhs    (lo=rhs, hi=lhs, hi inclusive)
            // lhs >  rhs   <==>   rhs <  lhs    (lo=rhs, hi=lhs, hi exclusive)
            boolean inclusive = (tag == JCTree.Tag.GE);
            return new Bounds(expr.rhs, expr.lhs, !inclusive, inclusive);
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
     * function call.
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
            boolean loExclusive = false;
            if (left.lo == null) {
                lo = right.lo;
                loExclusive = right.loExclusive;
            } else if (!inDecls(decls, left.lo) && inDecls(decls, right.lo)) {
                // left.lo is a real bound (not the variable), right.lo IS the variable
                lo = left.lo;
                loExclusive = left.loExclusive;
            } else if (inDecls(decls, left.lo) && !inDecls(decls, right.lo)) {
                lo = right.lo;
                loExclusive = right.loExclusive;
            } else if (!inDecls(decls, left.lo) && !inDecls(decls, right.lo)) {
                lo = treeMaker.Conditional(treeMaker.Binary(JCTree.Tag.LT, left.lo, right.lo), left.lo, right.lo);
                // For both-bounds, use the wider (less restrictive) flag:
                // adding +1 to one side and not the other could over- or
                // under-count. Keep loExclusive false; users who write multiple
                // overlapping lo bounds get the disjunction semantics.
            } else {
                lo = null;
            }

            JCExpression hi;
            boolean hiInclusive = false;
            if (left.hi == null) {
                hi = right.hi;
                hiInclusive = right.hiInclusive;
            } else if (!inDecls(decls, left.hi) && inDecls(decls, right.hi)) {
                hi = left.hi;
                hiInclusive = left.hiInclusive;
            } else if (inDecls(decls, left.hi) && !inDecls(decls, right.hi)) {
                hi = right.hi;
                hiInclusive = right.hiInclusive;
            } else if (!inDecls(decls, left.hi) && !inDecls(decls, right.hi)) {
                hi = treeMaker.Conditional(treeMaker.Binary(JCTree.Tag.GT, left.hi, right.hi), left.hi, right.hi);
            } else {
                hi = null;
            }

            return new Bounds(lo, hi, loExclusive, hiInclusive);
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
