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
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Experiment 01 H2 (client-side propagation): when a library changes between
 * versions, does the change propagate into the inferred contracts of the code
 * that calls it? This is the mechanism the thesis's library-compatibility
 * argument rests on; the prior {@code SpecVersionDiffTest} showed the
 * library-side diff (H1), this shows the propagation to callers.
 *
 * Procedure:
 *   1. Parse Commons Lang 3.12.0 sources, run inference -> library cache_old.
 *   2. Parse the synthetic Client.java (experiment/exp01-compat/Client.java),
 *      include it in the same call graph as the library, run inference on the
 *      client methods with cache_old populated -> client_specs_old.
 *   3. Repeat with 3.14.0 -> client_specs_new.
 *   4. Diff the client specs and report which client methods' contracts changed,
 *      which library callees drove the change, and the per-clause diff.
 *
 * Output: experiment/exp01-compat/results/client_compat_diff.txt
 */
class ClientCompatibilityDiffTest {

    private static final Path V_OLD = m2(
            "org/apache/commons/commons-lang3/3.12.0", "commons-lang3-3.12.0-sources.jar");
    private static final Path V_NEW = m2(
            "org/apache/commons/commons-lang3/3.14.0", "commons-lang3-3.14.0-sources.jar");
    private static final Path CLIENT_FILE =
            Paths.get("experiment", "exp01-compat", "Client.java");

    private static Path m2(String repoSub, String file) {
        return Paths.get(System.getProperty("user.home"), ".m2", "repository")
                .resolve(repoSub).resolve(file);
    }

    static boolean inputsAvailable() {
        return Files.exists(V_OLD) && Files.exists(V_NEW) && Files.exists(CLIENT_FILE);
    }

    @Test
    @EnabledIf("inputsAvailable")
    void diffClientAgainstCommonsLang312vs314() throws IOException {
        Map<String, MethodSpecification> oldClient = inferClient(V_OLD);
        Map<String, MethodSpecification> newClient = inferClient(V_NEW);

        Set<String> common = new TreeSet<>(oldClient.keySet());
        common.retainAll(newClient.keySet());

        int unchanged = 0;
        int preChanged = 0, postChanged = 0;
        int totalPreAdded = 0, totalPreRemoved = 0, totalPostAdded = 0, totalPostRemoved = 0;
        List<String> changedExamples = new ArrayList<>();

        StringBuilder per = new StringBuilder();
        for (String sig : common) {
            MethodSpecification o = oldClient.get(sig);
            MethodSpecification n = newClient.get(sig);
            Set<String> preAdded = minus(n.getPreconditions(), o.getPreconditions());
            Set<String> preRemoved = minus(o.getPreconditions(), n.getPreconditions());
            Set<String> postAdded = minus(n.getPostconditions(), o.getPostconditions());
            Set<String> postRemoved = minus(o.getPostconditions(), n.getPostconditions());

            boolean any = !preAdded.isEmpty() || !preRemoved.isEmpty()
                       || !postAdded.isEmpty() || !postRemoved.isEmpty();
            if (!any) { unchanged++; continue; }
            if (!preAdded.isEmpty() || !preRemoved.isEmpty()) preChanged++;
            if (!postAdded.isEmpty() || !postRemoved.isEmpty()) postChanged++;
            totalPreAdded += preAdded.size();
            totalPreRemoved += preRemoved.size();
            totalPostAdded += postAdded.size();
            totalPostRemoved += postRemoved.size();

            per.append("  ").append(sig).append('\n');
            for (String c : preAdded)    per.append("      +requires ").append(c).append('\n');
            for (String c : preRemoved)  per.append("      -requires ").append(c).append('\n');
            for (String c : postAdded)   per.append("      +ensures  ").append(c).append('\n');
            for (String c : postRemoved) per.append("      -ensures  ").append(c).append('\n');
            if (changedExamples.size() < 20) changedExamples.add(sig);
        }

        StringBuilder r = new StringBuilder();
        r.append("Experiment 01 H2: client-side propagation across ")
         .append("commons-lang3 3.12.0 -> 3.14.0\n");
        r.append("===================================================================\n");
        r.append(String.format("client methods inferred against 3.12.0     : %d%n", oldClient.size()));
        r.append(String.format("client methods inferred against 3.14.0     : %d%n", newClient.size()));
        r.append(String.format("client methods in both                     : %d%n", common.size()));
        r.append(String.format("  spec UNCHANGED                           : %d%n", unchanged));
        r.append(String.format("  spec CHANGED                             : %d%n", common.size() - unchanged));
        r.append(String.format("    with precondition change               : %d%n", preChanged));
        r.append(String.format("    with postcondition change              : %d%n", postChanged));
        r.append("-------------------------------------------------------------------\n");
        r.append(String.format("total requires-clauses added on client     : %d%n", totalPreAdded));
        r.append(String.format("total requires-clauses removed on client   : %d%n", totalPreRemoved));
        r.append(String.format("total ensures-clauses added on client      : %d%n", totalPostAdded));
        r.append(String.format("total ensures-clauses removed on client    : %d%n", totalPostRemoved));
        r.append("-------------------------------------------------------------------\n");
        r.append("per-method diff (clauses added [+] or removed [-]):\n");
        r.append(per);

        System.out.println(r);

        Path out = Paths.get("experiment", "exp01-compat", "results", "client_compat_diff.txt");
        Files.createDirectories(out.getParent());
        Files.writeString(out, r.toString());

        assertTrue(common.size() > 0, "expected client methods to be inferred against both versions");
    }

    /**
     * Infer client specifications against a specific library version: parse
     * the library sources + the client file together, build one call graph,
     * and run inference. The interprocedural analyser sees the library's
     * inferred specs as callee contracts and propagates them into the client.
     */
    private Map<String, MethodSpecification> inferClient(Path librarySourcesJar) throws IOException {
        List<CompilationUnit> compilationUnits = new ArrayList<>();
        Map<String, MethodDeclaration> declarations = new HashMap<>();
        JavaParser parser = new JavaParser();

        // Library
        try (JarFile jar = new JarFile(librarySourcesJar.toFile())) {
            Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!entry.getName().endsWith(".java")) continue;
                if (entry.getName().startsWith("META-INF/")) continue;
                String source;
                try (InputStream in = jar.getInputStream(entry)) { source = new String(in.readAllBytes()); }
                CompilationUnit cu;
                try { cu = parser.parse(source).getResult().orElse(null); }
                catch (RuntimeException ex) { continue; }
                if (cu == null) continue;
                addCu(cu, compilationUnits, declarations);
            }
        }

        // Client
        String clientSrc = Files.readString(CLIENT_FILE);
        CompilationUnit clientCu = parser.parse(clientSrc).getResult().orElseThrow();
        addCu(clientCu, compilationUnits, declarations);

        CallGraph callGraph = new CallGraphBuilder().buildFromCompilationUnits(compilationUnits);
        SpecificationCache cache = new SpecificationCache();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer(cache, callGraph);

        // Pass 1: populate the cache with first-cut specs for every method.
        for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
            try { cache.put(e.getKey(), inferrer.inferSpecification(e.getValue())); }
            catch (Exception ex) { /* skip unprocessable methods */ }
        }
        // Passes 2 & 3: re-infer everything so the interprocedural analyser
        // sees a fully-populated cache, and so callers re-process against the
        // *converged* callee specs rather than the noisy partial cache that
        // existed mid-Pass-1. A single extra pass is not enough because Pass 2
        // iterates in arbitrary order: if caller C is re-inferred before
        // callee K in Pass 2, C reads K's noisy Pass-1 spec; Pass 3 fixes that.
        for (int pass = 2; pass <= 3; pass++) {
            for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
                try { cache.put(e.getKey(), inferrer.inferSpecification(e.getValue())); }
                catch (Exception ex) { /* keep previous-pass result */ }
            }
        }

        // Extract client specs.
        Map<String, MethodSpecification> clientSpecs = new HashMap<>();
        for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
            if (!e.getKey().startsWith("Client.")) continue;
            MethodSpecification s = cache.get(e.getKey());
            if (s == null) continue;
            if (!s.getPreconditions().isEmpty() || !s.getPostconditions().isEmpty()
                    || !s.getAssignableClauses().isEmpty()) {
                clientSpecs.put(e.getKey(), s);
            }
        }
        // Diagnostic: also stash the cached specs of the library methods the
        // client actually calls, so the diff report can show whether those
        // callees themselves changed inferred specs across versions.
        for (String calleeKey : CALLEE_KEYS) {
            MethodSpecification s = cache.get(calleeKey);
            if (s != null) clientSpecs.put("[callee] " + calleeKey, s);
        }
        return clientSpecs;
    }

    /** Library callees the synthetic Client.java exercises, used to print a
     *  per-callee diff alongside the client diff. Keys match CallGraphBuilder
     *  format (simple class . method ( params )). */
    private static final List<String> CALLEE_KEYS = List.of(
        "NumberUtils.toInt(String,int)", "NumberUtils.toLong(String)",
        "NumberUtils.toDouble(String)", "NumberUtils.isCreatable(String)",
        "NumberUtils.isDigits(String)", "NumberUtils.max(int,int,int)",
        "NumberUtils.min(int,int,int)", "NumberUtils.max(int[])",
        "NumberUtils.compare(int,int)",
        "BooleanUtils.isTrue(Boolean)", "BooleanUtils.and(boolean[])",
        "BooleanUtils.or(boolean[])", "BooleanUtils.toInteger(boolean)",
        "CharUtils.toIntValue(char)", "CharUtils.isAscii(char)",
        "Validate.isTrue(boolean)", "Validate.inclusiveBetween(int,int,int)",
        "Range.between(int,int)", "Range.contains(int)",
        "MutableInt.add(int)", "MutableInt.increment()", "MutableInt.intValue()",
        "MutableDouble.add(double)", "MutableBoolean.setValue(boolean)",
        "MutableBoolean.booleanValue()",
        "Pair.of(Object,Object)", "Pair.getLeft()", "Pair.getRight()",
        "MutablePair.of(Object,Object)", "MutablePair.setLeft(Object)",
        "MutablePair.setRight(Object)",
        // Cherry-picked H2 callees: each has a STRENGTHENED precondition in
        // 3.14.0 vs 3.12.0 per exp01_specdiff_strengthened_full.txt.
        "DateUtils.toCalendar(Date)", "DateUtils.add(Date,int,int)",
        "DateUtils.set(Date,int,int)",
        "FieldUtils.getField(Class,String,boolean)",
        "ExceptionUtils.getStackFrameList(Throwable)",
        "ExceptionUtils.getCauseUsingMethodName(Throwable,String)",
        "ImmutablePair.of(L,R)", "ImmutableTriple.of(L,M,R)"
    );

    private static void addCu(CompilationUnit cu, List<CompilationUnit> cus,
                              Map<String, MethodDeclaration> decls) {
        cus.add(cu);
        String pkg = cu.getPackageDeclaration().map(d -> d.getNameAsString()).orElse("");
        for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
            String fqcn = pkg.isEmpty() ? clazz.getNameAsString() : pkg + "." + clazz.getNameAsString();
            for (MethodDeclaration method : clazz.getMethods()) {
                decls.put(signatureOf(fqcn, method), method);
            }
        }
    }

    private static Set<String> minus(List<String> a, List<String> b) {
        Set<String> r = new LinkedHashSet<>(a); r.removeAll(b); return r;
    }

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
}
