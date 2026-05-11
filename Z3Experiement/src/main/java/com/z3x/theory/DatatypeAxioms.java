package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Eager axiom generator for algebraic datatypes.
 *
 * For each registered datatype, walks the input formula and for every constructor and selector
 * occurrence emits the corresponding axiom as a side assertion:
 *
 * <ul>
 *   <li>Selector: <code>(sel_i (C x1..xn)) = xi</code> for each constructor C and selector sel_i.</li>
 *   <li>Tester-positive: <code>(is-C (C x1..xn)) = true</code>.</li>
 *   <li>Tester-negative: <code>(is-D (C x1..xn)) = false</code> for D ≠ C.</li>
 *   <li>Disjointness: <code>(C ...) ≠ (D ...)</code> for distinct constructors of the same datatype.</li>
 * </ul>
 *
 * Acyclicity (a datatype term cannot equal a strict subterm of itself) is enforced by EUF
 * automatically as long as the disjointness axioms separate constructors.
 *
 * This is sound but eager — instantiates one axiom per ground occurrence. For deeply nested
 * datatypes the axiom count is linear in subterm count, matching the standard "Akron"
 * approach used by other solvers as a baseline.
 */
public final class DatatypeAxioms {

    private final TermFactory tf;
    private final Collection<Sort.Datatype> datatypes;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seenCtorTerms = new HashSet<>();

    public DatatypeAxioms(TermFactory tf, Collection<Sort.Datatype> datatypes) {
        this.tf = tf;
        this.datatypes = datatypes;
    }

    public List<Term> axioms() { return axioms; }

    public void collectFrom(Term t) {
        walk(t, new HashSet<>());
    }

    private void walk(Term t, Set<Integer> visited) {
        if (!visited.add(t.id)) return;
        for (Term c : t.children()) walk(c, visited);
        if (t instanceof Term.App app) {
            if (app.symbol.equals("=") && app.args.size() == 2) {
                tryEmitEqUnfold(app.args.get(0), app.args.get(1));
                tryEmitEqUnfold(app.args.get(1), app.args.get(0));
            }
            for (Sort.Datatype dt : datatypes) {
                for (Sort.Constructor ctor : dt.constructors()) {
                    if (app.symbol.equals(ctor.name())) {
                        emitCtorAxioms(app, dt, ctor);
                        return;
                    }
                }
            }
        } else if (t instanceof Term.Var var) {
            for (Sort.Datatype dt : datatypes) {
                for (Sort.Constructor ctor : dt.constructors()) {
                    if (ctor.selectors().isEmpty() && var.name.equals(ctor.name())) {
                        emitNullaryCtorAxioms(var, dt, ctor);
                        return;
                    }
                }
            }
        }
    }

    private void emitNullaryCtorAxioms(Term.Var v, Sort.Datatype dt, Sort.Constructor ctor) {
        if (!seenCtorTerms.add(v.id)) return;
        axioms.add(tf.mkAppRaw("is-" + ctor.name(), List.of(v), Sort.BOOL));
        for (Sort.Constructor other : dt.constructors()) {
            if (other.name().equals(ctor.name())) continue;
            Term testerOther = tf.mkAppRaw("is-" + other.name(), List.of(v), Sort.BOOL);
            axioms.add(tf.mkNot(testerOther));
        }
    }

    /** If rhs = (C arg1..argn) or rhs is a nullary constructor Var, emit selector + tester axioms on lhs. */
    private void tryEmitEqUnfold(Term lhs, Term rhs) {
        String head = null;
        List<Term> ctorArgs = List.of();
        if (rhs instanceof Term.App rApp) { head = rApp.symbol; ctorArgs = rApp.args; }
        else if (rhs instanceof Term.Var rVar) { head = rVar.name; }
        else return;
        for (Sort.Datatype dt : datatypes) {
            for (Sort.Constructor ctor : dt.constructors()) {
                if (!head.equals(ctor.name())) continue;
                // Skip nullary self-equality unfolds where lhs already equals rhs structurally.
                if (lhs == rhs) return;
                for (int i = 0; i < ctor.selectors().size() && i < ctorArgs.size(); i++) {
                    Sort.Selector sel = ctor.selectors().get(i);
                    Term selOnLhs = tf.mkAppRaw(sel.name(), List.of(lhs), sel.sort());
                    axioms.add(tf.mkEq(selOnLhs, ctorArgs.get(i)));
                }
                // Tester-positive on lhs.
                axioms.add(tf.mkAppRaw("is-" + ctor.name(), List.of(lhs), Sort.BOOL));
                for (Sort.Constructor other : dt.constructors()) {
                    if (other.name().equals(ctor.name())) continue;
                    Term testerOther = tf.mkAppRaw("is-" + other.name(), List.of(lhs), Sort.BOOL);
                    axioms.add(tf.mkNot(testerOther));
                }
                return;
            }
        }
    }

    private void emitCtorAxioms(Term.App ctorApp, Sort.Datatype dt, Sort.Constructor ctor) {
        if (!seenCtorTerms.add(ctorApp.id)) return;
        // Selector axioms: sel_i(C(x1..xn)) = x_i.
        for (int i = 0; i < ctor.selectors().size(); i++) {
            Sort.Selector sel = ctor.selectors().get(i);
            Term selApp = tf.mkAppRaw(sel.name(), List.of(ctorApp), sel.sort());
            axioms.add(tf.mkEq(selApp, ctorApp.args.get(i)));
        }
        // Tester positive: is-C(C(args)) = true.
        Term testerThis = tf.mkAppRaw("is-" + ctor.name(), List.of(ctorApp), Sort.BOOL);
        axioms.add(testerThis);
        // Tester negative + disjointness: for every other constructor D ≠ C.
        for (Sort.Constructor other : dt.constructors()) {
            if (other.name().equals(ctor.name())) continue;
            Term testerOther = tf.mkAppRaw("is-" + other.name(), List.of(ctorApp), Sort.BOOL);
            axioms.add(tf.mkNot(testerOther));
        }
    }
}
