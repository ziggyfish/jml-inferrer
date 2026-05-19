package com.jml.inferrer.analysis;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.model.MethodSpecification;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Article 3 RQ3 measurement experiment: does compositional specification
 * refinement strictly extend the isolated-inference precondition set on
 * real code?
 *
 * <p>The experiment:
 * <ol>
 *   <li>Parse every source file in Apache Commons Lang 3.14.0 (the same
 *       corpus used by Articles 1 and 2).</li>
 *   <li>Build a call graph over all parsed methods
 *       ({@link CallGraphBuilder}).</li>
 *   <li>Run {@link MethodSpecificationInferrer} on every method to produce
 *       the isolated-inference baseline; snapshot the per-method
 *       precondition and postcondition counts.</li>
 *   <li>Run {@link CompositionalAnalyzer#refineAll()} on the populated
 *       {@link SpecificationCache}.</li>
 *   <li>Snapshot the per-method counts again and diff against the
 *       baseline. Categorise the newly-added clauses by syntactic shape.</li>
 * </ol>
 *
 * <p>Disabled when the Commons Lang sources jar is missing from the local
 * Maven cache. Results are written to
 * {@code journal/rq3_composition_measurement.txt} for inclusion in
 * Article 3's empirical section.</p>
 */
class CompositionalAnalyzerCommonsLangExperimentTest {

    private static final Path COMMONS_LANG_SOURCES = m2(
            "org/apache/commons/commons-lang3/3.14.0", "commons-lang3-3.14.0-sources.jar");
    private static final Path COMMONS_IO_SOURCES = m2(
            "commons-io/commons-io/2.13.0", "commons-io-2.13.0-sources.jar");
    private static final Path COMMONS_MATH_SOURCES = m2(
            "org/apache/commons/commons-math3/3.6.1", "commons-math3-3.6.1-sources.jar");
    private static final Path JOOL_SOURCES = m2(
            "org/jooq/jool/0.9.14", "jool-0.9.14-sources.jar");
    private static final Path VAVR_SOURCES = m2(
            "io/vavr/vavr/0.10.4", "vavr-0.10.4-sources.jar");
    private static final Path GUAVA_SOURCES = m2(
            "com/google/guava/guava/33.3.0-jre", "guava-33.3.0-jre-sources.jar");

    private static Path m2(String repoSub, String file) {
        return Paths.get(System.getProperty("user.home"), ".m2", "repository")
                .resolve(repoSub).resolve(file);
    }

    static boolean inputsAvailable() {
        return Files.exists(COMMONS_LANG_SOURCES);
    }

    static boolean commonsIoAvailable() {
        return Files.exists(COMMONS_IO_SOURCES);
    }

    static boolean commonsMathAvailable() {
        return Files.exists(COMMONS_MATH_SOURCES);
    }

    static boolean joolAvailable() {
        return Files.exists(JOOL_SOURCES);
    }

    static boolean vavrAvailable() {
        return Files.exists(VAVR_SOURCES);
    }

    static boolean guavaAvailable() {
        return Files.exists(GUAVA_SOURCES);
    }

    @Test
    @EnabledIf("inputsAvailable")
    void measureCompositionalExtensionOnCommonsLang() throws IOException {
        runOn("commons-lang3-3.14.0", COMMONS_LANG_SOURCES);
    }

    @Test
    @EnabledIf("commonsIoAvailable")
    void measureCompositionalExtensionOnCommonsIo() throws IOException {
        runOn("commons-io-2.13.0", COMMONS_IO_SOURCES);
    }

    @Test
    @EnabledIf("commonsMathAvailable")
    void measureCompositionalExtensionOnCommonsMath() throws IOException {
        runOn("commons-math3-3.6.1", COMMONS_MATH_SOURCES);
    }

    @Test
    @EnabledIf("joolAvailable")
    void measureCompositionalExtensionOnJool() throws IOException {
        runOn("jool-0.9.14", JOOL_SOURCES);
    }

    @Test
    @EnabledIf("vavrAvailable")
    void measureCompositionalExtensionOnVavr() throws IOException {
        runOn("vavr-0.10.4", VAVR_SOURCES);
    }

    // Guava is excluded from the present experiment: its source-jar size
    // pushes the JavaParser-driven harness into a deep recursion that
    // overflows the default JVM stack. Resolving requires either raising
    // -Xss for the test JVM or restructuring the call-graph builder to be
    // iterative; both are deferred. The breadth claim for the present
    // article rests on the Commons Lang + Commons IO measurements only.
    // @Test @EnabledIf("guavaAvailable")
    // void measureCompositionalExtensionOnGuava() throws IOException {
    //     runOn("guava-33.3.0-jre", GUAVA_SOURCES);
    // }

    private void runOn(String label, Path sourcesJar) throws IOException {
        // Pass 0: parse every source file in the jar.
        List<CompilationUnit> compilationUnits = new ArrayList<>();
        Map<String, MethodDeclaration> declarations = new HashMap<>();
        JavaParser parser = new JavaParser();

        try (JarFile jar = new JarFile(sourcesJar.toFile())) {
            Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!entry.getName().endsWith(".java")) continue;
                if (entry.getName().startsWith("META-INF/")) continue;
                String source;
                try (InputStream in = jar.getInputStream(entry)) {
                    source = new String(in.readAllBytes());
                }
                CompilationUnit cu;
                try {
                    cu = parser.parse(source).getResult().orElse(null);
                } catch (RuntimeException ex) { continue; }
                if (cu == null) continue;
                compilationUnits.add(cu);
                String pkg = cu.getPackageDeclaration()
                        .map(d -> d.getNameAsString()).orElse("");
                for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                    String fqcn = pkg.isEmpty() ? clazz.getNameAsString()
                            : pkg + "." + clazz.getNameAsString();
                    for (MethodDeclaration method : clazz.getMethods()) {
                        String sig = signatureOf(fqcn, method);
                        declarations.put(sig, method);
                    }
                }
            }
        }
        assertFalse(compilationUnits.isEmpty(), "expected to parse at least one source file");

        // Pass 1: build the call graph.
        CallGraph callGraph = new CallGraphBuilder().buildFromCompilationUnits(compilationUnits);

        // Pass 2: run isolated inference and populate the cache.
        SpecificationCache cache = new SpecificationCache();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer(cache, callGraph);

        Map<String, int[]> baselineCounts = new HashMap<>();  // sig -> [pre, post]
        Map<String, MethodSpecification> baselineSpecs = new HashMap<>();
        int totalInferred = 0;
        for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
            try {
                MethodSpecification spec = inferrer.inferSpecification(e.getValue());
                cache.put(e.getKey(), spec);
                baselineCounts.put(e.getKey(),
                        new int[]{spec.getPreconditions().size(), spec.getPostconditions().size()});
                baselineSpecs.put(e.getKey(), snapshot(spec));
                totalInferred++;
            } catch (Exception ex) {
                // Skip methods the inferrer can't process; not part of the experiment.
            }
        }

        // Debug: print 5 sample (sig, calls-in-body, isolated-pre-count) tuples
        // so we can see whether the isolated inference is already propagating.
        int debugged = 0;
        for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
            if (debugged >= 8) break;
            int calls = e.getValue().findAll(com.github.javaparser.ast.expr.MethodCallExpr.class).size();
            if (calls < 2) continue;
            MethodSpecification s = cache.get(e.getKey());
            if (s == null) continue;
            System.out.printf("  sample: %s -> calls=%d isolatedPre=%d isolatedPost=%d%n",
                    e.getKey(), calls, s.getPreconditions().size(), s.getPostconditions().size());
            for (String p : s.getPreconditions()) System.out.println("    pre: " + p);
            debugged++;
        }

        // Diagnostic: how many call sites in the corpus, how many resolve to a
        // cached callee, how many substitutions would succeed (matching arity),
        // and how many of those substituted clauses are already in the caller's
        // isolated spec. Reveals whether composition adds nothing because
        // (a) call resolution fails, (b) arity rejects, or (c) the isolated
        // pass already derives the same clause.
        int callSites = 0, calleeFound = 0, calleeHasSpec = 0;
        int arityMatch = 0, substituted = 0, alreadyPresent = 0, wouldAdd = 0;
        for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
            MethodSpecification callerSpec = cache.get(e.getKey());
            if (callerSpec == null) continue;
            for (var call : e.getValue().findAll(com.github.javaparser.ast.expr.MethodCallExpr.class)) {
                callSites++;
                String name = call.getNameAsString();
                String calleeSig = null;
                for (String sig : cache.getAll().keySet()) {
                    int dot = sig.lastIndexOf('.');
                    int paren = sig.indexOf('(');
                    String simple = sig.substring(dot + 1, paren > dot ? paren : sig.length());
                    if (simple.equals(name)) { calleeSig = sig; break; }
                }
                if (calleeSig == null) continue;
                calleeFound++;
                MethodSpecification calleeSpec = cache.get(calleeSig);
                if (calleeSpec == null) continue;
                calleeHasSpec++;
                MethodDeclaration calleeDecl = declarations.get(calleeSig);
                if (calleeDecl == null) continue;
                if (calleeDecl.getParameters().size() != call.getArguments().size()) continue;
                arityMatch++;
                for (String pre : calleeSpec.getPreconditions()) {
                    substituted++;
                    if (callerSpec.getPreconditions().contains(pre)) {
                        alreadyPresent++;
                    } else {
                        wouldAdd++;
                    }
                }
            }
        }
        System.out.printf("  diag: callSites=%d calleeFound=%d calleeHasSpec=%d arityMatch=%d "
                + "substituted=%d alreadyPresent=%d wouldAdd=%d%n",
                callSites, calleeFound, calleeHasSpec, arityMatch,
                substituted, alreadyPresent, wouldAdd);

        // Pass 3: run compositional refinement.
        long t0 = System.nanoTime();
        CompositionalAnalyzer.RefinementResult result =
                new CompositionalAnalyzer(cache, callGraph, declarations).refineAll();
        long refineNanos = System.nanoTime() - t0;

        // Pass 4: diff per method.
        int methodsRefined = 0;
        int methodsWithNewPre = 0;
        int methodsWithNewPost = 0;
        int totalNewPreClauses = 0;
        int totalNewPostClauses = 0;
        int maxNewPreOnOne = 0;
        ShapeCounts shapes = new ShapeCounts();

        for (Map.Entry<String, int[]> e : baselineCounts.entrySet()) {
            MethodSpecification after = cache.get(e.getKey());
            if (after == null) continue;
            MethodSpecification before = baselineSpecs.get(e.getKey());
            int newPre = after.getPreconditions().size() - e.getValue()[0];
            int newPost = after.getPostconditions().size() - e.getValue()[1];
            if (newPre > 0 || newPost > 0) methodsRefined++;
            if (newPre > 0) {
                methodsWithNewPre++;
                totalNewPreClauses += newPre;
                if (newPre > maxNewPreOnOne) maxNewPreOnOne = newPre;
                // Identify clauses added in `after` but not in `before`.
                Set<String> beforeSet = new LinkedHashSet<>(before.getPreconditions());
                for (String clause : after.getPreconditions()) {
                    if (!beforeSet.contains(clause)) shapes.add(clause);
                }
            }
            if (newPost > 0) {
                methodsWithNewPost++;
                totalNewPostClauses += newPost;
            }
        }

        // Write the metric line for the article.
        Path metrics = Paths.get("journal", "rq3_composition_measurement.txt");
        Files.createDirectories(metrics.getParent());
        StringBuilder report = new StringBuilder();
        report.append(String.format(
                "%s (compositional refinement)%n"
                + "  sourceFiles=%d methodsInferred=%d methodsInCache=%d%n"
                + "  refineWallTimeMs=%.2f%n"
                + "  sccsVisited=%d refinementsApplied=%d iterationsTotal=%d%n"
                + "  methodsRefined=%d (%.2f%% of cache)%n"
                + "  methodsWithNewPrecondition=%d totalNewPreconditionClauses=%d%n"
                + "    avgNewPrePerRefinedMethod=%.2f maxNewPreOnOneMethod=%d%n"
                + "  methodsWithNewPostcondition=%d totalNewPostconditionClauses=%d%n"
                + "  shapeCategories of newly-added preconditions:%n"
                + "    nullCheck=%d  (%s)%n"
                + "    rangeOrBound=%d  (%s)%n"
                + "    branchConditional=%d  (==>)%n"
                + "    disjunctive=%d  (||)%n"
                + "    other=%d%n%n",
                label,
                compilationUnits.size(), totalInferred, cache.size(),
                refineNanos / 1_000_000.0,
                result.sccCount(), result.methodsRefined(), result.totalIterations(),
                methodsRefined,
                100.0 * methodsRefined / Math.max(1, cache.size()),
                methodsWithNewPre, totalNewPreClauses,
                methodsRefined == 0 ? 0.0 : (double) totalNewPreClauses / methodsWithNewPre,
                maxNewPreOnOne,
                methodsWithNewPost, totalNewPostClauses,
                shapes.nullCheck, "!= null / == null",
                shapes.rangeOrBound, "<, <=, >, >=",
                shapes.branchConditional,
                shapes.disjunctive,
                shapes.other));
        Files.writeString(metrics, report.toString(),
                java.nio.file.StandardOpenOption.CREATE,
                java.nio.file.StandardOpenOption.APPEND);
        System.out.println(report);

        assertTrue(totalInferred > 0, "at least one method should be inferred");
        assertTrue(result.sccCount() > 0, "refineAll should visit at least one SCC");
    }

    /**
     * Match {@link CallGraphBuilder#buildMethodSignature}'s format so the
     * compositional analyser, which iterates the call graph in reverse
     * topological order, can look up our cache entries: simple class name
     * (not FQCN), generics stripped from parameter types.
     */
    private static String signatureOf(String fqcn, MethodDeclaration method) {
        String simpleClass = fqcn.contains(".") ? fqcn.substring(fqcn.lastIndexOf('.') + 1) : fqcn;
        StringBuilder sig = new StringBuilder();
        sig.append(simpleClass).append('.').append(method.getNameAsString()).append('(');
        boolean first = true;
        for (var p : method.getParameters()) {
            if (!first) sig.append(',');
            String typeName = p.getType().asString();
            if (typeName.contains("<")) typeName = typeName.substring(0, typeName.indexOf('<'));
            sig.append(typeName);
            first = false;
        }
        sig.append(')');
        return sig.toString();
    }

    private static MethodSpecification snapshot(MethodSpecification original) {
        MethodSpecification copy = new MethodSpecification();
        for (String s : original.getPreconditions())     copy.addPrecondition(s);
        for (String s : original.getPostconditions())    copy.addPostcondition(s);
        for (String s : original.getAssignableClauses()) copy.addAssignableClause(s);
        for (String s : original.getLoopInvariants())    copy.addLoopInvariant(s);
        return copy;
    }

    private static final class ShapeCounts {
        int nullCheck = 0;
        int rangeOrBound = 0;
        int branchConditional = 0;
        int disjunctive = 0;
        int other = 0;

        void add(String clause) {
            // Order matters: branch-conditional (==>) and disjunctive (||) take
            // precedence over content-only categories so they're counted by
            // their structural shape, not their content.
            if (clause.contains("==>")) { branchConditional++; return; }
            if (clause.contains("||")) { disjunctive++; return; }
            if (clause.contains("!= null") || clause.contains("== null")) { nullCheck++; return; }
            if (clause.contains("<=") || clause.contains(">=")
                    || clause.matches(".*[^=<>]<[^=].*") || clause.matches(".*[^=<>]>[^=].*")) {
                rangeOrBound++; return;
            }
            other++;
        }
    }
}
