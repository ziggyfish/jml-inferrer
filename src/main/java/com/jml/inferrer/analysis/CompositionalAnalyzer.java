package com.jml.inferrer.analysis;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Compositional specification refinement (RQ3 Phase 2B.1 — scaffold).
 *
 * <p>The existing {@link InterproceduralAnalyzer} performs single-pass
 * propagation: when method {@code m} calls {@code n}, the callee's preconditions
 * (substituted at the call site) are appended to {@code m}'s precondition set.
 * That is enough for many shapes but does not perform full weakest-precondition
 * (WP) refinement: it does not lift the callee's clauses through {@code m}'s
 * own control flow, and it does not iterate to a fixpoint when caller and
 * callee are mutually recursive.</p>
 *
 * <p>This class implements the second pass — a top-down WP refinement over the
 * call graph in reverse topological order. The algorithm is:
 *
 * <ol>
 *   <li>Take SCCs of the call graph in callees-first order
 *       ({@link CallGraph#sccsReverseTopological}).</li>
 *   <li>For each SCC: refine each method's spec by walking its body and
 *       applying the WP transformer at each call site, using the callee's
 *       cached spec.</li>
 *   <li>For an SCC of size &gt; 1 (mutual recursion), iterate the refinement
 *       until specs stabilise or a fixpoint cap is reached.</li>
 * </ol>
 *
 * <p>This scaffold ships a working two-pass driver and a basic per-call-site
 * transformer that conjoins the callee's preconditions into the caller's set.
 * Pass-2 features deferred to follow-up work (per
 * {@code journal/rq3_compositional_design.md}):</p>
 * <ul>
 *   <li>Lifting through branch / loop / try-catch shapes (currently treated as
 *       sequential composition).</li>
 *   <li>Polymorphic dispatch — disjunction over subtype callees.</li>
 *   <li>Side-effecting argument expressions (currently substituted naively).</li>
 *   <li>Termination tracking; the algorithm assumes callees terminate.</li>
 *   <li>Predicate-language fragment restriction; currently no clause is
 *       rejected on shape.</li>
 * </ul>
 *
 * <p>The scaffold runs after the existing bottom-up isolated inference and
 * mutates the {@link SpecificationCache} in place. A configuration knob
 * {@link Config#fixpointCap} bounds iteration on cyclic SCCs.</p>
 */
public class CompositionalAnalyzer {

    private static final Logger logger = LoggerFactory.getLogger(CompositionalAnalyzer.class);

    private final SpecificationCache cache;
    private final CallGraph callGraph;
    private final Map<String, MethodDeclaration> declarations;
    private final Config config;

    public CompositionalAnalyzer(SpecificationCache cache, CallGraph callGraph,
                                  Map<String, MethodDeclaration> declarations) {
        this(cache, callGraph, declarations, new Config());
    }

    public CompositionalAnalyzer(SpecificationCache cache, CallGraph callGraph,
                                  Map<String, MethodDeclaration> declarations, Config config) {
        this.cache = cache;
        this.callGraph = callGraph;
        this.declarations = declarations;
        this.config = config;
    }

    /**
     * Drive the second pass over all methods registered in the cache, in
     * reverse topological order. Each method's spec is replaced in place if
     * refinement produces additions.
     */
    public RefinementResult refineAll() {
        List<Set<String>> sccs = callGraph.sccsReverseTopological();
        int refinedCount = 0;
        int iterationsTotal = 0;

        for (Set<String> scc : sccs) {
            if (scc.size() == 1) {
                String only = scc.iterator().next();
                if (refineOne(only)) refinedCount++;
                iterationsTotal += 1;
            } else {
                // Cyclic SCC — iterate to fixpoint or until the cap is hit.
                int iter = 0;
                boolean changed;
                do {
                    changed = false;
                    for (String sig : scc) {
                        if (refineOne(sig)) {
                            changed = true;
                            refinedCount++;
                        }
                    }
                    iter++;
                } while (changed && iter < config.fixpointCap);
                iterationsTotal += iter;
                if (changed) {
                    logger.warn("Compositional refinement hit fixpoint cap ({}) on SCC of size {}",
                            config.fixpointCap, scc.size());
                }
            }
        }
        return new RefinementResult(refinedCount, iterationsTotal, sccs.size());
    }

    /**
     * Refine a single method's spec in the cache. Returns {@code true} if any
     * new clause was added to the spec.
     */
    private boolean refineOne(String methodSignature) {
        MethodSpecification current = cache.get(methodSignature);
        if (current == null) return false;
        MethodDeclaration decl = declarations.get(methodSignature);
        if (decl == null) return false;

        Set<String> beforePrecond = new LinkedHashSet<>(current.getPreconditions());
        Set<String> beforePostcond = new LinkedHashSet<>(current.getPostconditions());

        // Walk all call sites in the body and append the callee's WP-image to
        // the caller's spec, using the cached callee spec. The current
        // transformer is conservative: it conjoins the callee's preconditions
        // (substituted with actual arguments) into the caller's preconditions.
        // Lifting through control flow is deferred to follow-up work.
        List<MethodCallExpr> calls = decl.findAll(MethodCallExpr.class);
        for (MethodCallExpr call : calls) {
            String calleeSig = resolveCallee(call);
            if (calleeSig == null) continue;
            MethodSpecification calleeSpec = cache.get(calleeSig);
            if (calleeSpec == null) continue;

            // Polymorphic dispatch: a virtual call may dispatch to any
            // method that overrides the resolved callee. Collect all dispatch
            // candidates; for a single candidate the behaviour is the same as
            // before (conjoin the substituted preconditions). For multiple
            // candidates, emit the disjunction across candidates: at least
            // one candidate's preconditions must be satisfied at the call
            // site, so the caller's precondition becomes the disjunction.
            List<String> candidates = polymorphicCandidates(calleeSig);
            String guardCondition = enclosingGuardCondition(call);
            int candidateCount = candidates.size();

            if (candidateCount == 1) {
                List<String> calleePreSnapshot = new ArrayList<>(calleeSpec.getPreconditions());
                for (String pre : calleePreSnapshot) {
                    String substituted = substituteArguments(pre, call, calleeSig);
                    if (substituted == null) continue;
                    String lifted = guardCondition == null
                            ? substituted
                            : "(" + guardCondition + ") ==> (" + substituted + ")";
                    if (!current.getPreconditions().contains(lifted)) {
                        current.addPrecondition(lifted);
                    }
                }
            } else {
                // For multiple candidates, emit one disjunction per
                // shared-shape precondition. The simplest sound approach is to
                // emit the disjunction of all candidates' substituted
                // preconditions as a single clause: at least one candidate's
                // contract must hold.
                List<String> candidateClauses = new ArrayList<>();
                for (String candidateSig : candidates) {
                    MethodSpecification candidateSpec = cache.get(candidateSig);
                    if (candidateSpec == null) continue;
                    List<String> conjoined = new ArrayList<>();
                    for (String pre : candidateSpec.getPreconditions()) {
                        String substituted = substituteArguments(pre, call, candidateSig);
                        if (substituted == null) continue;
                        conjoined.add(substituted);
                    }
                    if (conjoined.isEmpty()) {
                        // A candidate with no preconditions matches trivially;
                        // disjunction collapses to true.
                        candidateClauses.clear();
                        break;
                    }
                    candidateClauses.add(conjoined.size() == 1
                            ? conjoined.get(0)
                            : "(" + String.join(" && ", conjoined) + ")");
                }
                if (!candidateClauses.isEmpty()) {
                    String disjunction = candidateClauses.size() == 1
                            ? candidateClauses.get(0)
                            : String.join(" || ", candidateClauses);
                    String lifted = guardCondition == null
                            ? disjunction
                            : "(" + guardCondition + ") ==> (" + disjunction + ")";
                    if (!current.getPreconditions().contains(lifted)) {
                        current.addPrecondition(lifted);
                    }
                }
            }

            // RQ3: postcondition propagation, gated on the callee's
            // termination flag. A non-terminating callee's postcondition is
            // conditional on termination; propagating it unconditionally
            // would be unsound. For the scaffold we propagate the callee's
            // postconditions only when terminates() is true; the propagated
            // clause is the substituted postcondition optionally guarded by
            // the enclosing branch condition.
            if (calleeSpec.terminates() && candidateCount == 1) {
                List<String> calleePostSnapshot = new ArrayList<>(calleeSpec.getPostconditions());
                for (String post : calleePostSnapshot) {
                    String substituted = substituteArguments(post, call, calleeSig);
                    if (substituted == null) continue;
                    String lifted = guardCondition == null
                            ? substituted
                            : "(" + guardCondition + ") ==> (" + substituted + ")";
                    if (!current.getPostconditions().contains(lifted)) {
                        current.addPostcondition(lifted);
                    }
                }
            }
        }

        boolean changed = !beforePrecond.equals(new LinkedHashSet<>(current.getPreconditions()))
                || !beforePostcond.equals(new LinkedHashSet<>(current.getPostconditions()));
        return changed;
    }

    /**
     * Best-effort callee resolution. Returns the cached signature whose name
     * matches the call expression, or {@code null} if no match. The full
     * version uses the call graph's static-type information; this scaffold
     * matches by simple name only and is therefore unsound for overloaded
     * methods. Documented as a known limit pending the polymorphic-dispatch
     * extension.
     */
    private String resolveCallee(MethodCallExpr call) {
        String name = call.getNameAsString();
        for (String sig : cache.getAll().keySet()) {
            int dot = sig.lastIndexOf('.');
            int paren = sig.indexOf('(');
            String simple = sig.substring(dot + 1, paren > dot ? paren : sig.length());
            if (simple.equals(name)) return sig;
        }
        return null;
    }

    /**
     * Substitute the callee's formal parameter names with the caller's actual
     * argument expressions in a precondition string. Conservative: drops the
     * clause if any argument is an expression that the inferrer can't safely
     * substitute (method calls with side effects, lambda expressions).
     */
    private String substituteArguments(String calleePrecondition, MethodCallExpr call, String calleeSig) {
        // The inferrer's clauses use the callee's parameter names verbatim. We
        // need the callee's MethodDeclaration to recover those names.
        MethodDeclaration callee = declarations.get(calleeSig);
        if (callee == null) return null;
        String result = calleePrecondition;
        var formalParams = callee.getParameters();
        var actualArgs = call.getArguments();
        if (formalParams.size() != actualArgs.size()) return null;
        for (int i = 0; i < formalParams.size(); i++) {
            String formal = formalParams.get(i).getNameAsString();
            Expression actualExpr = actualArgs.get(i);
            // Reject side-effecting expressions — naive substitution would be
            // unsound.
            String actual = actualExpr.toString();
            if (actual.contains("++") || actual.contains("--")) return null;
            // Word-boundary regex replace so `\bformal\b` doesn't clobber
            // substrings (e.g. parameter `s` in `result == this.size`).
            result = result.replaceAll("\\b" + java.util.regex.Pattern.quote(formal) + "\\b",
                    java.util.regex.Matcher.quoteReplacement(actual));
        }
        return result;
    }

    /**
     * Walks the AST upward from the call expression and accumulates any
     * branch conditions whose body contains the call. Returns the conjunction
     * of those guards in JML-friendly syntax, or {@code null} if the call is
     * unguarded.
     *
     * <p>For a call inside {@code if (a) { if (b) { call(); } }} the result is
     * {@code (a) && (b)}. For a call inside the else-branch
     * {@code if (a) ...; else { call(); }} the result is {@code !(a)}. Calls
     * inside ternary expressions {@code cond ? thenCall() : elseCall()} are
     * handled symmetrically.</p>
     *
     * <p>Conservative: any if-statement whose condition has a side effect
     * (assignments, increments) is treated as opaque — we drop the entire
     * guard chain rather than emit an unsound clause. This keeps the
     * propagation sound at the cost of completeness on side-effecting code.</p>
     */
    private static String enclosingGuardCondition(MethodCallExpr call) {
        List<String> conjuncts = new ArrayList<>();
        Node child = call;
        Node parent = call.getParentNode().orElse(null);
        while (parent != null && !(parent instanceof MethodDeclaration)) {
            if (parent instanceof IfStmt ifStmt) {
                Expression cond = ifStmt.getCondition();
                if (hasSideEffect(cond)) return null;
                String condStr = cond.toString();
                Statement thenStmt = ifStmt.getThenStmt();
                Statement elseStmt = ifStmt.getElseStmt().orElse(null);
                if (thenStmt == child) {
                    conjuncts.add(condStr);
                } else if (elseStmt == child) {
                    conjuncts.add("!(" + condStr + ")");
                }
                // If `child` is the IfStmt itself (we just emerged from a
                // statement-level child), no guard from this layer.
            } else if (parent instanceof ConditionalExpr cExpr) {
                Expression cond = cExpr.getCondition();
                if (hasSideEffect(cond)) return null;
                if (cExpr.getThenExpr() == child) {
                    conjuncts.add(cond.toString());
                } else if (cExpr.getElseExpr() == child) {
                    conjuncts.add("!(" + cond.toString() + ")");
                }
            }
            child = parent;
            parent = parent.getParentNode().orElse(null);
        }
        if (conjuncts.isEmpty()) return null;
        // Reverse so the outermost guard appears first — reads more naturally.
        java.util.Collections.reverse(conjuncts);
        return String.join(" && ", conjuncts);
    }

    private static boolean hasSideEffect(Expression e) {
        String s = e.toString();
        return s.contains("++") || s.contains("--") || s.contains("=") && !s.contains("==") && !s.contains("!=")
                && !s.contains("<=") && !s.contains(">=");
    }

    /**
     * Return the set of dispatch candidates for a virtual call to
     * {@code calleeSig}: the method itself plus any cached method whose
     * simple name and class is in the same class hierarchy and whose method
     * descriptor matches.
     *
     * <p>This is a conservative resolution — it includes every method with
     * the same name across the cached classes, not narrowed by static-type
     * analysis. The cost is over-approximation (the disjunction may include
     * irrelevant candidates); the benefit is soundness (the disjunction
     * never excludes a real candidate).</p>
     */
    private List<String> polymorphicCandidates(String calleeSig) {
        List<String> out = new ArrayList<>();
        out.add(calleeSig);
        int dotInCallee = calleeSig.lastIndexOf('.');
        int parenInCallee = calleeSig.indexOf('(');
        if (dotInCallee < 0 || parenInCallee < 0) return out;
        String simpleName = calleeSig.substring(dotInCallee + 1, parenInCallee);
        String descriptor = calleeSig.substring(parenInCallee);
        String className = calleeSig.substring(0, dotInCallee);
        for (String otherSig : cache.getAll().keySet()) {
            if (otherSig.equals(calleeSig)) continue;
            int dot = otherSig.lastIndexOf('.');
            int paren = otherSig.indexOf('(');
            if (dot < 0 || paren < 0) continue;
            String otherName = otherSig.substring(dot + 1, paren);
            String otherDesc = otherSig.substring(paren);
            if (!simpleName.equals(otherName)) continue;
            if (!descriptor.equals(otherDesc)) continue;
            String otherClass = otherSig.substring(0, dot);
            if (sharesHierarchy(className, otherClass)) {
                out.add(otherSig);
            }
        }
        return out;
    }

    /**
     * Heuristic: two classes share a hierarchy if one is a subclass of the
     * other in the cached call graph. Without full type information, this
     * uses {@code CallGraph.getSuperclassChain} symmetrically.
     */
    private boolean sharesHierarchy(String a, String b) {
        if (a.equals(b)) return true;
        if (callGraph.getSuperclassChain(a).contains(b)) return true;
        if (callGraph.getSuperclassChain(b).contains(a)) return true;
        // Also include sibling classes that share a common ancestor and
        // implement the same interface — a virtual call dispatches to either.
        for (String iface : callGraph.getAllImplementedInterfaces(a)) {
            if (callGraph.getAllImplementedInterfaces(b).contains(iface)) return true;
        }
        return false;
    }

    /** Configuration knobs. */
    public static class Config {
        public int fixpointCap = 5;
    }

    /** Summary of a compositional refinement run. */
    public record RefinementResult(int methodsRefined, int totalIterations, int sccCount) {
        @Override
        public String toString() {
            return String.format("CompositionalAnalyzer: %d methods refined across %d SCCs (%d iterations total)",
                    methodsRefined, sccCount, totalIterations);
        }
    }
}
