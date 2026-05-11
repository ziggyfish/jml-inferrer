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
import com.z3x.theory.DatatypeAxioms;
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
    private final List<List<String>> assertionNameStack = new ArrayList<>();
    private String logic = "";
    /** Last seen (set-info :status ...) value, or empty if none. */
    private String declaredStatus = "";
    /** Last unsat core (names of assertions involved in the proof). */
    private List<String> lastUnsatCore = new ArrayList<>();
    /** Last produced model, mapping declared symbol name to value term. */
    private java.util.Map<String, Term> lastModel = new java.util.LinkedHashMap<>();
    private boolean produceUnsatCores = false;
    private boolean produceModels = false;

    public String declaredStatus() { return declaredStatus; }
    public List<String> lastUnsatCore() { return List.copyOf(lastUnsatCore); }
    public java.util.Map<String, Term> lastModel() { return java.util.Map.copyOf(lastModel); }

    public Solver() {
        assertionStack.add(new ArrayList<>());
        assertionNameStack.add(new ArrayList<>());
    }

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
            case "set-option" -> {
                if (l.items().size() >= 3 && l.items().get(1) instanceof SExpr.Atom kw) {
                    String key = kw.text();
                    String val = l.items().get(2) instanceof SExpr.Atom a ? a.text() : "";
                    if ((key.equals(":produce-unsat-cores") || key.equals("produce-unsat-cores")) && val.equals("true")) produceUnsatCores = true;
                    if ((key.equals(":produce-models") || key.equals("produce-models")) && val.equals("true")) produceModels = true;
                }
            }
            case "get-unsat-core" -> {
                StringBuilder sb = new StringBuilder("(");
                for (int i = 0; i < lastUnsatCore.size(); i++) {
                    if (i > 0) sb.append(' ');
                    sb.append(lastUnsatCore.get(i));
                }
                sb.append(')');
                System.out.println(sb);
            }
            case "get-model" -> {
                StringBuilder sb = new StringBuilder("(model");
                for (var e : lastModel.entrySet()) {
                    sb.append("\n  (define-fun ").append(e.getKey()).append(" () ");
                    sb.append(e.getValue().sort).append(' ').append(e.getValue()).append(')');
                }
                sb.append(')');
                System.out.println(sb);
            }
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
            case "declare-datatypes" -> handleDeclareDatatypes(l);
            case "declare-datatype" -> handleDeclareDatatype(l);
            case "declare-fun" -> {
                String name = ((SExpr.Atom) l.items().get(1)).text();
                List<Sort> args = new ArrayList<>();
                for (SExpr a : ((SExpr.SList) l.items().get(2)).items()) args.add(tb.resolveSort(a));
                Sort res = tb.resolveSort(l.items().get(3));
                tf.declareFunction(name, args, res);
            }
            case "assert" -> {
                SExpr arg = l.items().get(1);
                String name = null;
                // Strip top-level (! body :named X) for unsat-core tracking.
                if (arg instanceof SExpr.SList al && al.items().size() >= 4
                        && al.items().get(0) instanceof SExpr.Atom h && h.text().equals("!")) {
                    for (int i = 2; i + 1 < al.items().size(); i += 2) {
                        if (al.items().get(i) instanceof SExpr.Atom kw && kw.text().equals("named")
                                && al.items().get(i + 1) instanceof SExpr.Atom nm) {
                            name = nm.text();
                        }
                    }
                    arg = al.items().get(1);
                }
                Term t = tb.build(arg);
                assertionStack.get(assertionStack.size() - 1).add(t);
                assertionNameStack.get(assertionNameStack.size() - 1).add(name);
            }
            case "push" -> {
                int n = l.items().size() > 1 ? Integer.parseInt(((SExpr.Atom) l.items().get(1)).text()) : 1;
                for (int i = 0; i < n; i++) {
                    assertionStack.add(new ArrayList<>());
                    assertionNameStack.add(new ArrayList<>());
                }
            }
            case "pop" -> {
                int n = l.items().size() > 1 ? Integer.parseInt(((SExpr.Atom) l.items().get(1)).text()) : 1;
                for (int i = 0; i < n; i++) {
                    assertionStack.remove(assertionStack.size() - 1);
                    assertionNameStack.remove(assertionNameStack.size() - 1);
                }
                if (assertionStack.isEmpty()) {
                    assertionStack.add(new ArrayList<>());
                    assertionNameStack.add(new ArrayList<>());
                }
            }
            case "check-sat" -> { return checkSat(); }
            case "exit" -> {}
            default -> {}
        }
        return null;
    }

    /** Toggle to dump preprocessing artefacts. Set via {@code -Dz3x.debug=true}. */
    private static final boolean DEBUG = Boolean.getBoolean("z3x.debug");

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
        // Datatype axiom expansion: ground instantiation per constructor occurrence.
        if (!datatypes.isEmpty()) {
            DatatypeAxioms dax = new DatatypeAxioms(tf, datatypes.values());
            for (Term t : extended) dax.collectFrom(t);
            extended.addAll(dax.axioms());
        }
        List<Term> qRewritten = q.rewriteAll(extended);
        qRewritten.addAll(q.sideAssertions());
        List<Term> rewritten = new ArrayList<>();
        for (Term t : qRewritten) rewritten.add(bv.rewrite(ite.rewrite(arr.rewrite(t))));
        for (Term t : ite.sideAssertions()) rewritten.add(bv.rewrite(ite.rewrite(arr.rewrite(t))));
        if (DEBUG) {
            System.err.println("=== assertions (post-preprocess) ===");
            for (Term t : rewritten) System.err.println("  " + t);
        }
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
        if (r == Cdcl.Result.UNSAT && produceUnsatCores) {
            // Sound (coarse) unsat core: every named assertion currently active. A finer-grained
            // implementation would walk the resolution proof and pick only the named asserts
            // whose top-level CNF vars appear; that's a follow-up.
            lastUnsatCore.clear();
            for (List<String> frame : assertionNameStack) {
                for (String n : frame) if (n != null) lastUnsatCore.add(n);
            }
        }
        if (r == Cdcl.Result.SAT && produceModels) {
            lastModel.clear();
            // Extract value assignments for declared int/bool constants. Theory-specific value
            // reconstruction (LIA's Simplex values, EUF's class representatives) is a follow-up.
            for (int v = 1; v <= cnf.numVars(); v++) {
                Term t = cnf.termForVar(v);
                if (t instanceof Term.Var var) {
                    int val = sat.valueOf(v);
                    lastModel.put(var.name, val == 1 ? tf.mkBool(true) : val == -1 ? tf.mkBool(false) : t);
                }
            }
        }
        return r == Cdcl.Result.SAT ? Verdict.SAT : Verdict.UNSAT;
    }

    /** Registered datatype sorts, indexed by name. */
    private final java.util.Map<String, Sort.Datatype> datatypes = new java.util.HashMap<>();

    /** Tracks all known datatype sorts so the preprocessor can emit axioms. */
    public java.util.Collection<Sort.Datatype> datatypes() { return datatypes.values(); }

    private void handleDeclareDatatypes(SExpr.SList l) {
        // (declare-datatypes ((Name 0) ...) ( (((C1 (sel1 sort) ...) (C2 ...))) ... ))
        SExpr.SList names = (SExpr.SList) l.items().get(1);
        SExpr.SList bodies = (SExpr.SList) l.items().get(2);
        // First declare all names as sorts (allows mutual recursion).
        for (SExpr nd : names.items()) {
            SExpr.SList ndl = (SExpr.SList) nd;
            String dname = ((SExpr.Atom) ndl.items().get(0)).text();
            tf.declareSort(dname, 0);
        }
        for (int i = 0; i < names.items().size(); i++) {
            SExpr.SList ndl = (SExpr.SList) names.items().get(i);
            String dname = ((SExpr.Atom) ndl.items().get(0)).text();
            SExpr.SList ctorList = (SExpr.SList) bodies.items().get(i);
            registerDatatype(dname, ctorList);
        }
    }

    private void handleDeclareDatatype(SExpr.SList l) {
        // (declare-datatype Name ((C1 (sel1 sort) ...) (C2 ...) ...))
        String dname = ((SExpr.Atom) l.items().get(1)).text();
        tf.declareSort(dname, 0);
        SExpr.SList ctorList = (SExpr.SList) l.items().get(2);
        registerDatatype(dname, ctorList);
    }

    private void registerDatatype(String dname, SExpr.SList ctorList) {
        // First pass: parse the structure without registering any functions yet, so we can
        // build the final Sort.Datatype instance before any function signatures reference it.
        List<Sort.Constructor> ctors = new ArrayList<>();
        List<List<Sort>> ctorArgSorts = new ArrayList<>();
        for (SExpr c : ctorList.items()) {
            SExpr.SList cl = (SExpr.SList) c;
            String cname = ((SExpr.Atom) cl.items().get(0)).text();
            List<Sort.Selector> sels = new ArrayList<>();
            List<Sort> argSorts = new ArrayList<>();
            for (int i = 1; i < cl.items().size(); i++) {
                SExpr.SList sl = (SExpr.SList) cl.items().get(i);
                String sname = ((SExpr.Atom) sl.items().get(0)).text();
                Sort ssort = tb.resolveSort(sl.items().get(1));
                sels.add(new Sort.Selector(sname, ssort));
                argSorts.add(ssort);
            }
            ctors.add(new Sort.Constructor(cname, sels));
            ctorArgSorts.add(argSorts);
        }
        Sort.Datatype dtSort = new Sort.Datatype(dname, ctors);
        tf.replaceSort(dname, dtSort);
        datatypes.put(dname, dtSort);
        // Second pass: now register constructors, selectors, testers with the final dtSort.
        for (int ci = 0; ci < ctors.size(); ci++) {
            Sort.Constructor c = ctors.get(ci);
            List<Sort> argSorts = ctorArgSorts.get(ci);
            tf.declareFunction(c.name(), argSorts, dtSort);
            tf.declareFunction("is-" + c.name(), List.of((Sort) dtSort), Sort.BOOL);
            for (Sort.Selector sel : c.selectors()) {
                tf.declareFunction(sel.name(), List.of((Sort) dtSort), sel.sort());
            }
        }
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
