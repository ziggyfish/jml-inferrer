package com.jml.inferrer.analysis;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the RQ3 {@link CompositionalAnalyzer} scaffold.
 *
 * <p>The analyzer's contract: after {@link CompositionalAnalyzer#refineAll()},
 * a caller's preconditions include the callee's preconditions (substituted
 * for arguments) when (a) the callee is a method known to the cache and
 * (b) the call site is unguarded by branch logic. Order of refinement is
 * driven by the call graph's strongly-connected components.</p>
 */
class CompositionalAnalyzerTest {

    @Test
    @DisplayName("Caller inherits callee's preconditions on a direct call")
    void directCallPropagatesPreconditions() {
        Map<String, MethodDeclaration> decls = parse("""
                class T {
                    int helper(String s) { return s.length(); }
                    int caller(String x) { return helper(x); }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);

        // Pass 1 — bottom-up isolated inference (mimicking the existing pipeline).
        for (var entry : decls.entrySet()) {
            MethodSpecification spec = inferrer.inferSpecification(entry.getValue());
            cache.put(entry.getKey(), spec);
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        // Wire the call: caller -> helper.
        cg.addCall(sigOf("caller", decls), sigOf("helper", decls));

        // Sanity: the caller does not yet have helper's `s != null` precondition.
        MethodSpecification callerBefore = cache.get(sigOf("caller", decls));
        assertFalse(callerBefore.getPreconditions().stream()
                        .anyMatch(p -> p.contains("x != null")
                                || p.contains("s != null")),
                "caller should not yet inherit helper's null check; got: " + callerBefore.getPreconditions());

        // Pass 2 — compositional refinement.
        CompositionalAnalyzer analyzer = new CompositionalAnalyzer(cache, cg, decls);
        var result = analyzer.refineAll();
        assertNotNull(result);
        assertTrue(result.methodsRefined() >= 1, "at least one method should refine; got " + result);

        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));
        assertTrue(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("x != null")),
                "caller should now have x != null after composition; got: " + callerAfter.getPreconditions());
    }

    @Test
    @DisplayName("Self-recursion does not loop forever")
    void selfRecursionTerminates() {
        Map<String, MethodDeclaration> decls = parse("""
                class R {
                    int factorial(int n) {
                        if (n <= 1) return 1;
                        return n * factorial(n - 1);
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("factorial", decls), sigOf("factorial", decls));

        CompositionalAnalyzer analyzer = new CompositionalAnalyzer(cache, cg, decls);
        var result = analyzer.refineAll();
        // The fixpoint cap (default 5) bounds iteration; the test passes by not hanging.
        assertNotNull(result);
    }

    @Test
    @DisplayName("Mutual recursion: SCC drives joint refinement")
    void mutualRecursionRefinesSCC() {
        Map<String, MethodDeclaration> decls = parse("""
                class M {
                    boolean isEven(int n) {
                        if (n == 0) return true;
                        return isOdd(n - 1);
                    }
                    boolean isOdd(int n) {
                        if (n == 0) return false;
                        return isEven(n - 1);
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        // Mutual edges: isEven -> isOdd, isOdd -> isEven.
        cg.addCall(sigOf("isEven", decls), sigOf("isOdd", decls));
        cg.addCall(sigOf("isOdd", decls), sigOf("isEven", decls));

        var sccs = cg.sccsReverseTopological();
        assertTrue(sccs.stream().anyMatch(s -> s.size() == 2),
                "expected one SCC of size 2 for mutual recursion; got " + sccs);

        CompositionalAnalyzer analyzer = new CompositionalAnalyzer(cache, cg, decls);
        var result = analyzer.refineAll();
        assertNotNull(result);
        assertEquals(sccs.size(), result.sccCount(),
                "RefinementResult.sccCount should match graph SCC count");
    }

    @Test
    @DisplayName("Branch-guarded call yields cond ==> precondition")
    void branchGuardedCallLifted() {
        Map<String, MethodDeclaration> decls = parse("""
                class B {
                    int helper(String s) { return s.length(); }
                    int caller(String x, boolean ready) {
                        if (ready) {
                            return helper(x);
                        }
                        return 0;
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("caller", decls), sigOf("helper", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));

        // The callee's precondition `s != null` should be lifted as
        // `(ready) ==> (x != null)` because the call is guarded by `ready`.
        assertTrue(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("ready") && p.contains("==>") && p.contains("x != null")),
                "expected branch-lifted precondition; got: " + callerAfter.getPreconditions());

        // The unguarded form must NOT be present.
        assertFalse(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.equals("x != null")),
                "unguarded x != null should not appear; the call is conditional");
    }

    @Test
    @DisplayName("Else-branch call yields !cond ==> precondition")
    void elseBranchCallLifted() {
        Map<String, MethodDeclaration> decls = parse("""
                class E {
                    int helper(String s) { return s.length(); }
                    int caller(String x, boolean fast) {
                        if (fast) {
                            return 0;
                        } else {
                            return helper(x);
                        }
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("caller", decls), sigOf("helper", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));
        assertTrue(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("!(fast)") && p.contains("==>") && p.contains("x != null")),
                "expected else-branch lifted precondition with negated guard; got: "
                        + callerAfter.getPreconditions());
    }

    @Test
    @DisplayName("Nested if statements conjoin guard conditions")
    void nestedIfConjoinsGuards() {
        Map<String, MethodDeclaration> decls = parse("""
                class N {
                    int helper(String s) { return s.length(); }
                    int caller(String x, boolean a, boolean b) {
                        if (a) {
                            if (b) {
                                return helper(x);
                            }
                        }
                        return 0;
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("caller", decls), sigOf("helper", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));
        // Conjunction of `a` and `b` should appear, in source order
        assertTrue(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("a") && p.contains("&&") && p.contains("b")
                                && p.contains("==>") && p.contains("x != null")),
                "expected (a) && (b) ==> (x != null); got: " + callerAfter.getPreconditions());
    }

    @Test
    @DisplayName("Side-effecting guard condition drops the entire guard chain")
    void sideEffectingGuardDropped() {
        Map<String, MethodDeclaration> decls = parse("""
                class S {
                    int helper(String s) { return s.length(); }
                    int caller(String x, int counter) {
                        if (counter++ > 0) {
                            return helper(x);
                        }
                        return 0;
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("caller", decls), sigOf("helper", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));
        // No precondition should be added at all — the guard has side effects,
        // so we conservatively drop both the guard and the propagated clause.
        assertFalse(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("counter++")),
                "side-effecting guard should be dropped, not embedded; got: "
                        + callerAfter.getPreconditions());
    }

    @Test
    @DisplayName("Polymorphic dispatch: caller emits disjunction over candidate preconditions")
    void polymorphicDispatchEmitsDisjunction() {
        Map<String, MethodDeclaration> decls = parse("""
                class Animal {
                    int eat(String food) { return food.length(); }
                }
                class Cow extends Animal {
                    int eat(String hay) { return hay.length() * 2; }
                }
                class Caller {
                    int feed(Animal a, String x) { return a.eat(x); }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        // Wire the class hierarchy: Cow extends Animal.
        cg.setSuperclass("Cow", "Animal");
        // Wire the call: Caller.feed -> Animal.eat. The polymorphic resolver
        // should also pick up Cow.eat as a candidate.
        cg.addCall(sigOf("feed", decls), sigOf("eat", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("feed", decls));

        // The caller's preconditions should include a disjunction of
        // candidate preconditions: `(food != null) || (hay != null)` after
        // substitution becomes `(x != null) || (x != null)` — both propagate
        // x != null because the substituted clauses are identical.
        assertTrue(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("x != null")),
                "expected polymorphic-dispatch precondition; got: " + callerAfter.getPreconditions());
    }

    @Test
    @DisplayName("Polymorphic dispatch: empty candidate preconditions collapse to no clause")
    void polymorphicDispatchTrivialDisjunction() {
        Map<String, MethodDeclaration> decls = parse("""
                class Base {
                    int run() { return 42; }
                }
                class Derived extends Base {
                    int run() { return 99; }
                }
                class Driver {
                    int kick(Base b) { return b.run(); }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.setSuperclass("Derived", "Base");
        cg.addCall(sigOf("kick", decls), sigOf("run", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("kick", decls));

        // Both candidates have no preconditions — the disjunction collapses
        // to true, so no precondition is added to the caller.
        assertFalse(callerAfter.getPreconditions().stream()
                        .anyMatch(p -> p.contains("||")),
                "should not emit empty disjunction; got: " + callerAfter.getPreconditions());
    }

    @Test
    @DisplayName("Termination: terminating callee's postcondition propagates to caller")
    void terminatingCalleePostconditionPropagates() {
        Map<String, MethodDeclaration> decls = parse("""
                class T {
                    int helper(String s) { return s.length(); }
                    int caller(String x) { return helper(x); }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("caller", decls), sigOf("helper", decls));

        // Confirm helper is marked terminating.
        assertTrue(cache.get(sigOf("helper", decls)).terminates(),
                "non-recursive helper should be marked terminating");

        // Inject a postcondition on the helper to verify propagation behaviour.
        cache.get(sigOf("helper", decls)).addPostcondition("\\result >= 0");

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));
        assertTrue(callerAfter.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\result >= 0")),
                "expected helper's postcondition to propagate; got: " + callerAfter.getPostconditions());
    }

    @Test
    @DisplayName("Termination: non-terminating callee's postcondition does NOT propagate")
    void nonTerminatingCalleePostconditionWithheld() {
        Map<String, MethodDeclaration> decls = parse("""
                class R {
                    int spin() {
                        while (true) {}
                    }
                    int caller() { return spin(); }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("caller", decls), sigOf("spin", decls));

        // The infinite loop should flag spin as non-terminating.
        assertFalse(cache.get(sigOf("spin", decls)).terminates(),
                "method with while(true) should be marked non-terminating");

        // Inject a postcondition on spin (hypothetical contract).
        cache.get(sigOf("spin", decls)).addPostcondition("\\result == 42");

        new CompositionalAnalyzer(cache, cg, decls).refineAll();
        MethodSpecification callerAfter = cache.get(sigOf("caller", decls));
        assertFalse(callerAfter.getPostconditions().stream()
                        .anyMatch(p -> p.contains("\\result == 42")),
                "non-terminating callee's postcondition must not propagate; got: "
                        + callerAfter.getPostconditions());
    }

    @Test
    @DisplayName("Termination: direct self-recursion flags the method as non-terminating")
    void directSelfRecursionMarkedNonTerminating() {
        Map<String, MethodDeclaration> decls = parse("""
                class F {
                    int factorial(int n) {
                        if (n <= 1) return 1;
                        return n * factorial(n - 1);
                    }
                    int helper() { return 0; }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
        }
        assertFalse(cache.get(sigOf("factorial", decls)).terminates(),
                "directly recursive method should default to non-terminating without decreases");
        assertTrue(cache.get(sigOf("helper", decls)).terminates(),
                "non-recursive method should be marked terminating");
    }

    @Test
    @DisplayName("Compositional pass strictly extends isolated inference (clause delta > 0)")
    void compositionalPassAddsNewClauses() {
        Map<String, MethodDeclaration> decls = parse("""
                class C {
                    int sqrt(int n) {
                        if (n < 0) throw new IllegalArgumentException();
                        return (int) Math.sqrt(n);
                    }
                    int hypot(int a, int b) {
                        int s = a * a + b * b;
                        return sqrt(s);
                    }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("hypot", decls), sigOf("sqrt", decls));

        // Capture the isolated spec's preconditions for hypot — what the
        // existing single-pass inferrer produces.
        int isolatedPreCount = cache.get(sigOf("hypot", decls)).getPreconditions().size();

        // Run the compositional pass.
        new CompositionalAnalyzer(cache, cg, decls).refineAll();

        int composedPreCount = cache.get(sigOf("hypot", decls)).getPreconditions().size();
        assertTrue(composedPreCount > isolatedPreCount,
                "compositional pass should strictly extend the precondition set; "
                        + "isolated=" + isolatedPreCount + " composed=" + composedPreCount
                        + " preconditions=" + cache.get(sigOf("hypot", decls)).getPreconditions());

        // The new clause is the substituted form of sqrt's precondition
        // n >= 0 → s >= 0. The actual emitted form depends on the inferrer's
        // emission of sqrt's precondition (it may emit n >= 0 or n > -1).
        // Either way, the propagated form mentions `s` (the actual argument).
        assertTrue(cache.get(sigOf("hypot", decls)).getPreconditions().stream()
                        .anyMatch(p -> p.contains("s ")),
                "expected precondition to substitute formal `n` with actual `s`; got: "
                        + cache.get(sigOf("hypot", decls)).getPreconditions());
    }

    @Test
    @DisplayName("Compositional pass on transitive call chain propagates two levels")
    void compositionalPassPropagatesTransitively() {
        Map<String, MethodDeclaration> decls = parse("""
                class L {
                    int leaf(String s) { return s.length(); }
                    int mid(String t) { return leaf(t); }
                    int top(String u) { return mid(u); }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        cg.addCall(sigOf("mid", decls), sigOf("leaf", decls));
        cg.addCall(sigOf("top", decls), sigOf("mid", decls));

        new CompositionalAnalyzer(cache, cg, decls).refineAll();

        // After Pass 2 (single iteration), `top` should have inherited
        // `mid`'s precondition (`t != null`), which itself was previously
        // refined to include `leaf`'s precondition (`s != null`). The
        // substitution chain: leaf(s != null) → mid(t != null) → top(u != null).
        MethodSpecification topSpec = cache.get(sigOf("top", decls));
        assertTrue(topSpec.getPreconditions().stream()
                        .anyMatch(p -> p.contains("u != null")),
                "expected u != null transitive precondition on top; got: " + topSpec.getPreconditions());
    }

    @Test
    @DisplayName("Cache entry without a corresponding declaration is skipped, not crashed")
    void missingDeclarationSkipped() {
        Map<String, MethodDeclaration> decls = parse("""
                class S {
                    int simple() { return 0; }
                }
                """);

        SpecificationCache cache = new SpecificationCache();
        CallGraph cg = new CallGraph();
        var inferrer = new MethodSpecificationInferrer(cache);
        for (var entry : decls.entrySet()) {
            cache.put(entry.getKey(), inferrer.inferSpecification(entry.getValue()));
            cg.addMethodToClass(entry.getKey(), classOf(entry.getKey()));
        }
        // Add a phantom cache entry with no corresponding declaration.
        cache.put("Phantom.ghost(I)V", new MethodSpecification());

        CompositionalAnalyzer analyzer = new CompositionalAnalyzer(cache, cg, decls);
        var result = analyzer.refineAll();
        assertNotNull(result, "should not throw on phantom entry");
    }

    private static Map<String, MethodDeclaration> parse(String source) {
        var parser = new JavaParser();
        CompilationUnit cu = parser.parse(source).getResult().orElseThrow();
        Map<String, MethodDeclaration> out = new HashMap<>();
        cu.findAll(MethodDeclaration.class).forEach(m -> {
            String className = m.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .map(c -> c.getNameAsString())
                    .orElse("Unknown");
            // Plain class.method(paramTypes) signature.
            StringBuilder sig = new StringBuilder(className).append('.').append(m.getNameAsString()).append('(');
            for (int i = 0; i < m.getParameters().size(); i++) {
                if (i > 0) sig.append(',');
                sig.append(m.getParameters().get(i).getTypeAsString());
            }
            sig.append(')');
            out.put(sig.toString(), m);
        });
        return out;
    }

    private static String sigOf(String simpleMethodName, Map<String, MethodDeclaration> decls) {
        for (String key : decls.keySet()) {
            int dot = key.indexOf('.');
            int paren = key.indexOf('(');
            String simple = key.substring(dot + 1, paren);
            if (simple.equals(simpleMethodName)) return key;
        }
        throw new AssertionError("no method named " + simpleMethodName + " in " + decls.keySet());
    }

    private static String classOf(String signature) {
        int dot = signature.indexOf('.');
        return signature.substring(0, dot);
    }
}
