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
import com.z3x.theory.ConstantPropagator;
import com.z3x.theory.FpAxioms;
import com.z3x.theory.NlaAxioms;
import com.z3x.theory.RecursiveExpander;
import com.z3x.theory.StringAxioms;
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
    /** declared (declare-const NAME SORT) tracked here so get-model can dump their values. */
    private final java.util.Map<String, Term> declaredConstants = new java.util.LinkedHashMap<>();
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
                declaredConstants.put(name, tf.mkVar(name, s));
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
            case "define-fun" -> handleDefineFun(l, false);
            case "define-fun-rec" -> handleDefineFun(l, true);
            case "define-funs-rec" -> handleDefineFunsRec(l);
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
    private static final boolean PROF = Boolean.getBoolean("z3x.prof");
    /** Phase timings in nanoseconds (for profiling). */
    public long lastTimePreNs, lastTimeCnfNs, lastTimeSatNs;

    private Verdict checkSat() {
        long tStart = PROF ? System.nanoTime() : 0;
        List<Term> all = new ArrayList<>();
        for (List<Term> frame : assertionStack) all.addAll(frame);
        // Cheap feature-scan: avoid preprocessing passes whose feature isn't present.
        FeatureFlags ff = scanFeatures(all);
        Cnf cnf = new Cnf();
        List<Term> extended;
        if (ff.hasArrays) {
            ArrayExtensionality ext = new ArrayExtensionality(tf);
            extended = new ArrayList<>(all.size());
            for (Term t : all) extended.add(ext.rewrite(t));
        } else {
            extended = all;
        }
        if (!datatypes.isEmpty()) {
            DatatypeAxioms dax = new DatatypeAxioms(tf, datatypes.values());
            for (Term t : extended) dax.collectFrom(t);
            if (!dax.axioms().isEmpty()) {
                if (extended == all) extended = new ArrayList<>(all);
                extended.addAll(dax.axioms());
            }
        }
        // Recursive function definitions + constant propagation: iterate to fixpoint so that
        // each round of propagation can ground more arguments to recursive calls, which then
        // expand to expose more constants. Standard \sum/\product/\num_of from OpenJML's fork.
        if (!funDefs.isEmpty()) {
            if (extended == all) extended = new ArrayList<>(all);
            RecursiveExpander rex = new RecursiveExpander(tf, funDefs);
            for (int round = 0; round < 8; round++) {
                int axiomsBefore = rex.axioms().size();
                for (Term t : extended) rex.collectFrom(t);
                for (int idx = axiomsBefore; idx < rex.axioms().size(); idx++) {
                    extended.add(rex.axioms().get(idx));
                }
                ConstantPropagator cp = new ConstantPropagator(tf);
                cp.collectEqualities(extended);
                if (!cp.hasSubstitutions() && rex.axioms().size() == axiomsBefore) break;
                if (cp.hasSubstitutions()) {
                    List<Term> propagated = new ArrayList<>(extended.size());
                    boolean anyChange = false;
                    for (Term t : extended) {
                        Term r = cp.apply(t);
                        if (r != t) anyChange = true;
                        propagated.add(r);
                    }
                    if (anyChange) extended = propagated;
                    else if (rex.axioms().size() == axiomsBefore) break;
                }
            }
        }
        if (ff.hasStrings) {
            StringAxioms sax = new StringAxioms(tf);
            for (Term t : extended) sax.collectFrom(t);
            if (!sax.axioms().isEmpty()) {
                if (extended == all) extended = new ArrayList<>(all);
                extended.addAll(sax.axioms());
            }
        }
        if (ff.hasMul) {
            NlaAxioms nax = new NlaAxioms(tf);
            for (Term t : extended) nax.collectFrom(t);
            if (!nax.axioms().isEmpty()) {
                if (extended == all) extended = new ArrayList<>(all);
                extended.addAll(nax.axioms());
            }
        }
        if (ff.hasFp) {
            FpAxioms fpx = new FpAxioms(tf);
            for (Term t : extended) fpx.collectFrom(t);
            if (!fpx.axioms().isEmpty()) {
                if (extended == all) extended = new ArrayList<>(all);
                extended.addAll(fpx.axioms());
            }
        }
        List<Term> qRewritten;
        Quantifiers q = null;
        // Array extensionality may have just introduced foralls; if hasArrays force quantifier pass.
        if (ff.hasQuantifiers || ff.hasArrays) {
            q = new Quantifiers(tf);
            qRewritten = q.rewriteAll(extended);
            qRewritten.addAll(q.sideAssertions());
        } else {
            qRewritten = extended;
        }
        // ArrayPreprocessor introduces (ite ...) terms over the range sort; BvBlaster's div/rem
        // also introduce them. Force ITE elim on whenever either preprocessor will run.
        boolean needIte = ff.hasIte || ff.hasArrays || ff.hasBv;
        IteEliminator ite = needIte ? new IteEliminator(tf) : null;
        ArrayPreprocessor arr = ff.hasArrays ? new ArrayPreprocessor(tf) : null;
        BvBlaster bv = ff.hasBv ? new BvBlaster(tf) : null;
        List<Term> rewritten;
        if (ite == null && arr == null && bv == null) {
            rewritten = qRewritten;
        } else {
            rewritten = new ArrayList<>(qRewritten.size());
            for (Term t : qRewritten) rewritten.add(applyPipeline(t, arr, ite, bv));
            if (ite != null) for (Term t : ite.sideAssertions()) rewritten.add(applyPipeline(t, arr, ite, bv));
        }
        if (DEBUG) {
            System.err.println("=== assertions (post-preprocess) ===");
            for (Term t : rewritten) System.err.println("  " + t);
        }
        long tPre = PROF ? System.nanoTime() : 0;
        for (Term t : rewritten) cnf.assertTerm(t);
        long tCnf = PROF ? System.nanoTime() : 0;
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
        long tSat = PROF ? System.nanoTime() : 0;
        if (PROF) {
            lastTimePreNs = tPre - tStart;
            lastTimeCnfNs = tCnf - tPre;
            lastTimeSatNs = tSat - tCnf;
        }
        if (r == Cdcl.Result.UNSAT && produceUnsatCores) {
            // Tighter sound unsat core: collect SAT vars that appear in any clause whose
            // ancestors reach the level-0 empty clause (i.e., trail or conflict). For each named
            // assertion, include it iff one of its top-level SAT atoms is touched.
            // This is still over-approximating but much tighter than "every named assertion".
            java.util.Set<Integer> touchedVars = new java.util.HashSet<>();
            // Walk the SAT trail: every assigned var was "touched" if it has a non-trivial reason.
            for (int v = 1; v <= cnf.numVars(); v++) if (sat.valueOf(v) != 0) touchedVars.add(v);
            lastUnsatCore.clear();
            int idx = 0;
            for (int frameIdx = 0; frameIdx < assertionStack.size(); frameIdx++) {
                List<Term> frame = assertionStack.get(frameIdx);
                List<String> names = assertionNameStack.get(frameIdx);
                for (int aIdx = 0; aIdx < frame.size(); aIdx++) {
                    String n = names.get(aIdx);
                    if (n == null) { idx++; continue; }
                    // If any SAT var introduced by this assertion is touched, include it.
                    java.util.Set<Integer> assertionVars = new java.util.HashSet<>();
                    collectVarIds(frame.get(aIdx), assertionVars, cnf);
                    boolean intersect = false;
                    for (int av : assertionVars) if (touchedVars.contains(av)) { intersect = true; break; }
                    if (intersect) lastUnsatCore.add(n);
                    idx++;
                }
            }
            // Safety fallback: if the core is empty (shouldn't happen but be defensive), add all.
            if (lastUnsatCore.isEmpty()) {
                for (List<String> frame : assertionNameStack)
                    for (String n : frame) if (n != null) lastUnsatCore.add(n);
            }
        }
        if (r == Cdcl.Result.SAT && produceModels) {
            lastModel.clear();
            // Boolean variables: pull from SAT assignment.
            for (int v = 1; v <= cnf.numVars(); v++) {
                Term t = cnf.termForVar(v);
                if (t instanceof Term.Var var && var.sort == Sort.BOOL) {
                    int val = sat.valueOf(v);
                    if (val != 0) lastModel.put(var.name, tf.mkBool(val == 1));
                }
            }
            // LIA values: ask the theory for the Simplex assignment of declared Int/Real constants.
            LiaTheory liaT = findTheory(theory, LiaTheory.class);
            EufTheory eufT = findTheory(theory, EufTheory.class);
            for (var entry : declaredConstants.entrySet()) {
                Term t = entry.getValue();
                if (lastModel.containsKey(entry.getKey())) continue;
                if (t.sort == Sort.INT || t.sort == Sort.REAL) {
                    if (liaT != null) {
                        com.z3x.theory.Rational val = liaT.modelValue(t);
                        if (val != null) {
                            if (val.isInteger()) lastModel.put(entry.getKey(), tf.mkInt(val.num()));
                            else lastModel.put(entry.getKey(), tf.mkRat(val.num(), val.den()));
                            continue;
                        }
                    }
                }
                if (eufT != null) {
                    Term canon = eufT.canonicalOf(t);
                    if (canon != t) lastModel.put(entry.getKey(), canon);
                    else lastModel.put(entry.getKey(), t);
                } else {
                    lastModel.put(entry.getKey(), t);
                }
            }
        }
        return r == Cdcl.Result.SAT ? Verdict.SAT : Verdict.UNSAT;
    }

    private static final class FeatureFlags {
        boolean hasArrays, hasBv, hasIte, hasQuantifiers, hasStrings, hasMul, hasFp;
    }

    private FeatureFlags scanFeatures(List<Term> assertions) {
        FeatureFlags ff = new FeatureFlags();
        java.util.IdentityHashMap<Term, Boolean> seen = new java.util.IdentityHashMap<>();
        for (Term t : assertions) scanRec(t, ff, seen);
        return ff;
    }

    private void scanRec(Term t, FeatureFlags ff, java.util.IdentityHashMap<Term, Boolean> seen) {
        if (seen.put(t, Boolean.TRUE) != null) return;
        if (t instanceof Term.Quantifier) { ff.hasQuantifiers = true; }
        if (t instanceof Term.App app) {
            switch (app.symbol) {
                case "select", "store" -> ff.hasArrays = true;
                case "ite" -> { if (app.sort != Sort.BOOL) ff.hasIte = true; }
                case "*" -> {
                    // Non-linear multiplication = both operands non-constant.
                    if (app.args.size() == 2 && !(app.args.get(0) instanceof Term.IntConst)
                            && !(app.args.get(1) instanceof Term.IntConst)
                            && !(app.args.get(0) instanceof Term.RatConst)
                            && !(app.args.get(1) instanceof Term.RatConst)) {
                        ff.hasMul = true;
                    }
                }
                case "bvadd","bvsub","bvneg","bvnot","bvand","bvor","bvxor","bvmul",
                     "bvshl","bvlshr","bvashr","bvudiv","bvurem","bvsdiv","bvsrem","bvsmod",
                     "bvult","bvule","bvugt","bvuge","bvslt","bvsle","bvsgt","bvsge" -> ff.hasBv = true;
                case "str.++", "str.len", "str.at", "str.substr", "str.contains",
                     "str.prefixof", "str.suffixof", "str.indexof" -> ff.hasStrings = true;
                default -> {}
            }
            if (t.sort instanceof Sort.Array) ff.hasArrays = true;
            if (t.sort instanceof Sort.BitVec) ff.hasBv = true;
        }
        if (t instanceof Term.StrConst) ff.hasStrings = true;
        if (t instanceof Term.BvConst) ff.hasBv = true;
        if (t instanceof Term.FpConst) ff.hasFp = true;
        if (t.sort instanceof Sort.FloatingPoint) ff.hasFp = true;
        for (Term c : t.children()) scanRec(c, ff, seen);
    }

    private Term applyPipeline(Term t, ArrayPreprocessor arr, IteEliminator ite, BvBlaster bv) {
        Term cur = t;
        if (arr != null) cur = arr.rewrite(cur);
        if (ite != null) cur = ite.rewrite(cur);
        if (bv != null) cur = bv.rewrite(cur);
        return cur;
    }

    /** Registered (possibly-recursive) function definitions, indexed by name.
     *  {@code define-fun} entries are also stored here for uniform handling — they get
     *  unfolded the same way but their unfolding is guaranteed to terminate at depth 1. */
    public record FunDef(String name, List<String> paramNames, List<Sort> paramSorts,
                         Sort returnSort, Term body, boolean recursive) {}
    private final java.util.Map<String, FunDef> funDefs = new java.util.LinkedHashMap<>();
    public java.util.Map<String, FunDef> functionDefinitions() { return funDefs; }

    private void handleDefineFun(SExpr.SList l, boolean rec) {
        // (define-fun NAME ((p1 T1) ...) ReturnSort body)
        String name = ((SExpr.Atom) l.items().get(1)).text();
        SExpr.SList params = (SExpr.SList) l.items().get(2);
        List<String> paramNames = new ArrayList<>();
        List<Sort> paramSorts = new ArrayList<>();
        for (SExpr p : params.items()) {
            SExpr.SList pl = (SExpr.SList) p;
            String pn = ((SExpr.Atom) pl.items().get(0)).text();
            Sort ps = tb.resolveSort(pl.items().get(1));
            paramNames.add(pn);
            paramSorts.add(ps);
        }
        Sort retSort = tb.resolveSort(l.items().get(3));
        // The function may reference itself in body — pre-declare it.
        tf.declareFunction(name, paramSorts, retSort);
        // Declare each param as a placeholder function so body can be built.
        // We then read the body and store it; the placeholders stay in tf but never resolve.
        for (int i = 0; i < paramNames.size(); i++) {
            tf.declareFunction(paramNames.get(i), List.of(), paramSorts.get(i));
        }
        Term body = tb.build(l.items().get(4));
        funDefs.put(name, new FunDef(name, paramNames, paramSorts, retSort, body, rec));
    }

    private void handleDefineFunsRec(SExpr.SList l) {
        // (define-funs-rec ((name1 (params1) ret1) ...) (body1 body2 ...))
        SExpr.SList sigs = (SExpr.SList) l.items().get(1);
        SExpr.SList bodies = (SExpr.SList) l.items().get(2);
        // Pre-declare every function so bodies can mention each other.
        List<String> names = new ArrayList<>();
        List<List<String>> allParamNames = new ArrayList<>();
        List<List<Sort>> allParamSorts = new ArrayList<>();
        List<Sort> allRetSorts = new ArrayList<>();
        for (SExpr sig : sigs.items()) {
            SExpr.SList sl = (SExpr.SList) sig;
            String name = ((SExpr.Atom) sl.items().get(0)).text();
            SExpr.SList ps = (SExpr.SList) sl.items().get(1);
            List<String> pn = new ArrayList<>();
            List<Sort> psorts = new ArrayList<>();
            for (SExpr p : ps.items()) {
                SExpr.SList pl = (SExpr.SList) p;
                pn.add(((SExpr.Atom) pl.items().get(0)).text());
                psorts.add(tb.resolveSort(pl.items().get(1)));
            }
            Sort ret = tb.resolveSort(sl.items().get(2));
            tf.declareFunction(name, psorts, ret);
            names.add(name);
            allParamNames.add(pn);
            allParamSorts.add(psorts);
            allRetSorts.add(ret);
        }
        // Now build each body in turn.
        for (int i = 0; i < names.size(); i++) {
            for (int j = 0; j < allParamNames.get(i).size(); j++) {
                tf.declareFunction(allParamNames.get(i).get(j), List.of(), allParamSorts.get(i).get(j));
            }
            Term body = tb.build(bodies.items().get(i));
            funDefs.put(names.get(i), new FunDef(names.get(i), allParamNames.get(i),
                    allParamSorts.get(i), allRetSorts.get(i), body, true));
        }
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
        // Install the datatype sort with empty ctors first, so recursive references in selector
        // sorts (e.g. (tail List)) resolve to this same Datatype instance. Then fill in ctors.
        Sort.Datatype dtSort = new Sort.Datatype(dname, new ArrayList<>());
        tf.replaceSort(dname, dtSort);
        datatypes.put(dname, dtSort);
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
        dtSort.setConstructors(ctors);
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

    /** Walk a term and collect the CNF var ids of any atom it contains. */
    private void collectVarIds(Term t, java.util.Set<Integer> out, Cnf cnf) {
        Integer v = cnf.varForTerm(t);
        if (v != null) out.add(v);
        for (Term c : t.children()) collectVarIds(c, out, cnf);
    }

    @SuppressWarnings("unchecked")
    private <T extends TheoryHook> T findTheory(TheoryHook root, Class<T> cls) {
        if (cls.isInstance(root)) return (T) root;
        if (root instanceof com.z3x.theory.MultiTheory mt) {
            for (var sub : mt.theories()) if (cls.isInstance(sub)) return (T) sub;
        }
        return null;
    }

    private boolean logicNeedsEuf() {
        if (logic.isEmpty()) return true;
        return logic.contains("UF") || logic.equals("ALL") || logic.equals("QF_UF") || logic.equals("QF_AUFLIA");
    }

    private boolean logicNeedsLia() {
        if (logic.isEmpty()) return true;
        return logic.contains("LIA") || logic.contains("LRA") || logic.contains("IDL") || logic.contains("RDL")
                || logic.contains("LIRA") || logic.equals("ALL") || logic.contains("AUF")
                || logic.contains("S");  // String theory needs LIA for length reasoning.
    }
}
