package com.z3x.solver;

import com.z3x.parser.Parser;
import com.z3x.parser.SExpr;
import com.z3x.sat.Cdcl;
import com.z3x.sat.TheoryHook;
import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermBuilder;
import com.z3x.term.TermFactory;
import com.z3x.theory.ArrayExtensionality;
import com.z3x.theory.ArrayPreprocessor;
import com.z3x.theory.BvBlaster;
import com.z3x.theory.EufTheory;
import com.z3x.theory.IteEliminator;
import com.z3x.theory.LiaTheory;
import com.z3x.theory.MultiTheory;
import com.z3x.theory.Quantifiers;

import java.util.ArrayList;
import java.util.List;

/**
 * SMT-LIB2 command driver. Reads a script, executes commands, and returns the sequence of
 * {@code check-sat} answers in order. Single-context for now (push/pop are accepted but
 * implemented as full re-solves since incremental is not yet wired up).
 */
public final class Solver {

    public enum Verdict { SAT, UNSAT, UNKNOWN }

    private final TermFactory tf = new TermFactory();
    private final TermBuilder tb = new TermBuilder(tf);
    private final List<List<Term>> assertionStack = new ArrayList<>();
    private String logic = "";
    /** Last seen (set-info :status ...) value, or empty if none. */
    private String declaredStatus = "";

    public String declaredStatus() { return declaredStatus; }

    public Solver() { assertionStack.add(new ArrayList<>()); }

    public List<Verdict> run(String src) {
        List<SExpr> commands = Parser.parseAll(src);
        List<Verdict> verdicts = new ArrayList<>();
        for (SExpr c : commands) {
            Verdict v = exec(c);
            if (v != null) verdicts.add(v);
        }
        return verdicts;
    }

    private Verdict exec(SExpr cmd) {
        if (!(cmd instanceof SExpr.SList l) || l.items().isEmpty()) return null;
        SExpr head = l.items().get(0);
        if (!(head instanceof SExpr.Atom op)) return null;
        switch (op.text()) {
            case "set-logic" -> { logic = ((SExpr.Atom) l.items().get(1)).text(); }
            case "set-info" -> {
                if (l.items().size() >= 3 && l.items().get(1) instanceof SExpr.Atom kw
                        && kw.text().equals("status") && l.items().get(2) instanceof SExpr.Atom v) {
                    declaredStatus = v.text();
                }
            }
            case "set-option" -> {}
            case "declare-sort" -> {
                String name = ((SExpr.Atom) l.items().get(1)).text();
                int arity = Integer.parseInt(((SExpr.Atom) l.items().get(2)).text());
                tf.declareSort(name, arity);
            }
            case "declare-const" -> {
                String name = ((SExpr.Atom) l.items().get(1)).text();
                Sort s = tb.resolveSort(l.items().get(2));
                tf.declareFunction(name, List.of(), s);
            }
            case "declare-fun" -> {
                String name = ((SExpr.Atom) l.items().get(1)).text();
                List<Sort> args = new ArrayList<>();
                for (SExpr a : ((SExpr.SList) l.items().get(2)).items()) args.add(tb.resolveSort(a));
                Sort res = tb.resolveSort(l.items().get(3));
                tf.declareFunction(name, args, res);
            }
            case "assert" -> {
                Term t = tb.build(l.items().get(1));
                assertionStack.get(assertionStack.size() - 1).add(t);
            }
            case "push" -> {
                int n = l.items().size() > 1 ? Integer.parseInt(((SExpr.Atom) l.items().get(1)).text()) : 1;
                for (int i = 0; i < n; i++) assertionStack.add(new ArrayList<>());
            }
            case "pop" -> {
                int n = l.items().size() > 1 ? Integer.parseInt(((SExpr.Atom) l.items().get(1)).text()) : 1;
                for (int i = 0; i < n; i++) assertionStack.remove(assertionStack.size() - 1);
                if (assertionStack.isEmpty()) assertionStack.add(new ArrayList<>());
            }
            case "check-sat" -> { return checkSat(); }
            case "exit" -> {}
            default -> {}
        }
        return null;
    }

    private Verdict checkSat() {
        List<Term> all = new ArrayList<>();
        for (List<Term> frame : assertionStack) all.addAll(frame);
        Quantifiers q = new Quantifiers(tf);
        ArrayExtensionality ext = new ArrayExtensionality(tf);
        ArrayPreprocessor arr = new ArrayPreprocessor(tf);
        IteEliminator ite = new IteEliminator(tf);
        BvBlaster bv = new BvBlaster(tf);
        Cnf cnf = new Cnf();
        // Extensionality first so the introduced selects flow through array preprocessing
        // and the introduced forall flows through quantifier handling.
        List<Term> extended = new ArrayList<>(all.size());
        for (Term t : all) extended.add(ext.rewrite(t));
        List<Term> qRewritten = q.rewriteAll(extended);
        qRewritten.addAll(q.sideAssertions());
        List<Term> rewritten = new ArrayList<>();
        for (Term t : qRewritten) rewritten.add(bv.rewrite(ite.rewrite(arr.rewrite(t))));
        for (Term t : ite.sideAssertions()) rewritten.add(bv.rewrite(ite.rewrite(arr.rewrite(t))));
        for (Term t : rewritten) cnf.assertTerm(t);
        TheoryHook theory;
        boolean wantEuf = logicNeedsEuf();
        boolean wantLia = logicNeedsLia();
        if (wantEuf && wantLia) {
            theory = new MultiTheory(List.of(new EufTheory(tf, cnf), new LiaTheory(tf, cnf)));
        } else if (wantEuf) {
            theory = new EufTheory(tf, cnf);
        } else if (wantLia) {
            theory = new LiaTheory(tf, cnf);
        } else {
            theory = TheoryHook.NONE;
        }
        for (int v = 1; v <= cnf.numVars(); v++) {
            if (cnf.isTheoryAtom(v)) theory.registerAtom(v);
        }
        Cdcl sat = new Cdcl(cnf, theory);
        Cdcl.Result r = sat.solve();
        return r == Cdcl.Result.SAT ? Verdict.SAT : Verdict.UNSAT;
    }

    private boolean logicNeedsEuf() {
        if (logic.isEmpty()) return true;
        return logic.contains("UF") || logic.equals("ALL") || logic.equals("QF_UF") || logic.equals("QF_AUFLIA");
    }

    private boolean logicNeedsLia() {
        if (logic.isEmpty()) return true;
        return logic.contains("LIA") || logic.contains("LRA") || logic.contains("IDL") || logic.contains("RDL")
                || logic.contains("LIRA") || logic.equals("ALL") || logic.contains("AUF");
    }
}
