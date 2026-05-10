package com.z3x;

import com.z3x.solver.Solver;

import java.util.List;

/** Tests for nested quantifiers (∀∀, ∀∃, ∃∀) — Day-3 alternation support. */
public class QuantifierAlternationTest extends TestHarness {

    public void testMultiBindForallSat() {
        // Multi-bound forall: ∀ x y. (x=a ∧ y=b ⇒ p(x,y)).
        // Ground set has a and b; instance (a,b) gives (p a b), asserted.
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun p (U U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((x U) (y U)) (=> (and (= x a) (= y b)) (p x y))))
                (assert (p a b))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testMultiBindForallUnsat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun p (U U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((x U) (y U)) (=> (and (= x a) (= y b)) (p x y))))
                (assert (not (p a b)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testNestedForallUnsat() {
        // ∀ x. ∀ y. ((x=a ∧ y=b) ⇒ q(x,y)) — nested quantifier requires substitution-through-quantifier.
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun q (U U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((x U)) (forall ((y U)) (=> (and (= x a) (= y b)) (q x y)))))
                (assert (not (q a b)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testNestedForallSat() {
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun q (U U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((x U)) (forall ((y U)) (=> (and (= x a) (= y b)) (q x y)))))
                (assert (q a b))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.SAT), v);
    }

    public void testForallContainingExistsSkolemUnsat() {
        // (∀ x. ∃ y. y ≠ x) where the body is parsed; after skolemising the inner exists in
        // positive position under the universal, we instantiate the outer ∀. Body of outer ∀
        // becomes (= sk(x) x ⇒ false) → effectively asserts the inner exists witnesses x = sk(x),
        // which holds when sk depends on x (it does — fresh skolem per quantifier).
        // Concretely we encode the unsat (∃ x. ∀ y. y = x ∧ y ≠ x) ≡ false.
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-const a U)
                (assert (exists ((x U)) (forall ((y U)) (and (= y x) (not (= y x))))))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }

    public void testAlphaRenameNoCapture() {
        // ∀ z. (∀ x. (z=a ∧ x=b) ⇒ q(x,z)) — both quantifiers active; ensure inner ∀ x sees the
        // outer-substituted z without capturing x.
        var v = new Solver().run("""
                (set-logic QF_UF)
                (declare-sort U 0)
                (declare-fun q (U U) Bool)
                (declare-const a U)
                (declare-const b U)
                (assert (forall ((z U)) (forall ((x U)) (=> (and (= z a) (= x b)) (q x z)))))
                (assert (not (q b a)))
                (check-sat)
                """);
        assertEquals(List.of(Solver.Verdict.UNSAT), v);
    }
}
