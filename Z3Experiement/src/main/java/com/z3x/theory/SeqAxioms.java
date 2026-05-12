package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Eager axioms for the SMT-LIB Sequences theory. Mirrors {@link StringAxioms} for the basic
 * shape — length non-negativity, concat-length addition, contains/prefixof/suffixof bound
 * implications, at/extract length axioms — but operates over (Seq T) for any element sort T.
 *
 * Word-equation reasoning (non-trivial concat cancellation) and full sequence congruence
 * remain deferred — the axioms here cover the bounded-length JML-style use cases.
 */
public final class SeqAxioms {

    private final TermFactory tf;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seen = new HashSet<>();

    public SeqAxioms(TermFactory tf) { this.tf = tf; }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) { walk(t); }

    private void walk(Term t) {
        if (!seen.add(t.id)) return;
        for (Term c : t.children()) walk(c);
        if (t instanceof Term.App app) handleApp(app);
        // Universal: every (Seq T) term has non-negative length.
        if (t.sort instanceof Sort.Seq) {
            Term lenT = tf.mkAppRaw("seq.len", List.of(t), Sort.INT);
            axioms.add(tf.mkGe(lenT, tf.mkInt(0)));
        }
    }

    private void handleApp(Term.App app) {
        switch (app.symbol) {
            case "seq.len":
                axioms.add(tf.mkGe((Term) app, tf.mkInt(0)));
                break;
            case "seq.++":
                if (app.args.size() >= 2) {
                    Term lenAB = tf.mkAppRaw("seq.len", List.of((Term) app), Sort.INT);
                    List<Term> partLens = new ArrayList<>();
                    for (Term a : app.args) {
                        Term la = tf.mkAppRaw("seq.len", List.of(a), Sort.INT);
                        partLens.add(la);
                        axioms.add(tf.mkGe(la, tf.mkInt(0)));
                    }
                    axioms.add(tf.mkEq(lenAB, tf.mkAdd(partLens)));
                    axioms.add(tf.mkGe(lenAB, tf.mkInt(0)));
                }
                break;
            case "seq.unit":
                if (app.args.size() == 1) {
                    Term lenU = tf.mkAppRaw("seq.len", List.of((Term) app), Sort.INT);
                    axioms.add(tf.mkEq(lenU, tf.mkInt(1)));
                }
                break;
            case "seq.at":
                if (app.args.size() == 2) {
                    Term s = app.args.get(0);
                    Term idx = app.args.get(1);
                    Term lenS = tf.mkAppRaw("seq.len", List.of(s), Sort.INT);
                    Term lenAt = tf.mkAppRaw("seq.len", List.of((Term) app), Sort.INT);
                    Term inBounds = tf.mkAnd(List.of(tf.mkGe(idx, tf.mkInt(0)), tf.mkLt(idx, lenS)));
                    axioms.add(tf.mkEq(lenAt, tf.mkIte(inBounds, tf.mkInt(1), tf.mkInt(0))));
                }
                break;
            case "seq.extract":
                if (app.args.size() == 3) {
                    Term s = app.args.get(0);
                    Term start = app.args.get(1);
                    Term l = app.args.get(2);
                    Term lenS = tf.mkAppRaw("seq.len", List.of(s), Sort.INT);
                    Term lenSub = tf.mkAppRaw("seq.len", List.of((Term) app), Sort.INT);
                    Term validStart = tf.mkAnd(List.of(tf.mkGe(start, tf.mkInt(0)), tf.mkLe(start, lenS)));
                    Term remaining = tf.mkSub(List.of(lenS, start));
                    Term capped = tf.mkIte(tf.mkLt(l, remaining), l, remaining);
                    Term nonNeg = tf.mkIte(tf.mkLt(capped, tf.mkInt(0)), tf.mkInt(0), capped);
                    axioms.add(tf.mkEq(lenSub, tf.mkIte(validStart, nonNeg, tf.mkInt(0))));
                    axioms.add(tf.mkGe(lenSub, tf.mkInt(0)));
                }
                break;
            case "seq.contains":
            case "seq.prefixof":
            case "seq.suffixof":
                if (app.args.size() == 2) {
                    Term outer = app.symbol.equals("seq.contains") ? app.args.get(0) : app.args.get(1);
                    Term inner = app.symbol.equals("seq.contains") ? app.args.get(1) : app.args.get(0);
                    Term lenOuter = tf.mkAppRaw("seq.len", List.of(outer), Sort.INT);
                    Term lenInner = tf.mkAppRaw("seq.len", List.of(inner), Sort.INT);
                    axioms.add(tf.mkImplies((Term) app, tf.mkLe(lenInner, lenOuter)));
                }
                break;
            case "seq.indexof":
                if (app.args.size() == 3) {
                    Term s = app.args.get(0);
                    Term lenS = tf.mkAppRaw("seq.len", List.of(s), Sort.INT);
                    axioms.add(tf.mkOr(List.of(
                            tf.mkEq((Term) app, tf.mkInt(-1)),
                            tf.mkAnd(List.of(tf.mkGe((Term) app, tf.mkInt(0)), tf.mkLt((Term) app, lenS))))));
                }
                break;
            default: break;
        }
    }
}
