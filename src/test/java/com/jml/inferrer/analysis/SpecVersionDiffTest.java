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
 * Experiment 01 (version-to-version compatibility), detection step.
 *
 * Runs the inferrer over two versions of Apache Commons Lang
 * (3.12.0 and 3.14.0), produces a per-method inferred specification for
 * each, and diffs them. The diff classifies every method present in both
 * versions by how its inferred contract changed: precondition strengthened
 * (new requires-clauses added), precondition weakened (requires-clauses
 * removed), postcondition changed, frame changed, or unchanged. Methods
 * present in only one version are reported as added / removed.
 *
 * This is the syntactic detection step (Experiment 01, H1): it shows that
 * comparing inferred specs across versions surfaces method-level contract
 * changes. The SMT-subsumption refinement (does pre_new imply pre_old?) and
 * changelog-validated precision/recall are deferred to the full Experiment 01
 * / 02 harnesses.
 *
 * Results are written to journal/thesis/experiments/results/exp01_specdiff.txt.
 */
class SpecVersionDiffTest {

    private static final Path V_OLD = m2(
            "org/apache/commons/commons-lang3/3.12.0", "commons-lang3-3.12.0-sources.jar");
    private static final Path V_NEW = m2(
            "org/apache/commons/commons-lang3/3.14.0", "commons-lang3-3.14.0-sources.jar");

    private static Path m2(String repoSub, String file) {
        return Paths.get(System.getProperty("user.home"), ".m2", "repository")
                .resolve(repoSub).resolve(file);
    }

    static boolean bothVersionsAvailable() {
        return Files.exists(V_OLD) && Files.exists(V_NEW);
    }

    @Test
    @EnabledIf("bothVersionsAvailable")
    void diffCommonsLang312vs314() throws IOException {
        Map<String, MethodSpecification> oldSpecs = inferAll(V_OLD);
        Map<String, MethodSpecification> newSpecs = inferAll(V_NEW);

        Set<String> inBoth = new TreeSet<>(oldSpecs.keySet());
        inBoth.retainAll(newSpecs.keySet());
        Set<String> onlyOld = new TreeSet<>(oldSpecs.keySet());
        onlyOld.removeAll(newSpecs.keySet());
        Set<String> onlyNew = new TreeSet<>(newSpecs.keySet());
        onlyNew.removeAll(oldSpecs.keySet());

        int unchanged = 0;
        int preStrengthened = 0, preWeakened = 0, preMixed = 0;
        int postStrengthened = 0, postWeakened = 0, postMixed = 0;
        int frameChanged = 0;
        int totalPreAdded = 0, totalPreRemoved = 0, totalPostAdded = 0, totalPostRemoved = 0;
        List<String> examples = new ArrayList<>();
        // Full per-method dump of methods with at least one added requires clause,
        // so downstream cherry-pick analysis (Exp01 H2) can target the precise
        // callees whose preconditions strengthened across the version step.
        StringBuilder fullStrengthenedDump = new StringBuilder();

        for (String sig : inBoth) {
            MethodSpecification o = oldSpecs.get(sig);
            MethodSpecification n = newSpecs.get(sig);

            Set<String> preAdded = minus(n.getPreconditions(), o.getPreconditions());
            Set<String> preRemoved = minus(o.getPreconditions(), n.getPreconditions());
            Set<String> postAdded = minus(n.getPostconditions(), o.getPostconditions());
            Set<String> postRemoved = minus(o.getPostconditions(), n.getPostconditions());
            Set<String> frameAdded = minus(n.getAssignableClauses(), o.getAssignableClauses());
            Set<String> frameRemoved = minus(o.getAssignableClauses(), n.getAssignableClauses());

            boolean anyChange = !preAdded.isEmpty() || !preRemoved.isEmpty()
                    || !postAdded.isEmpty() || !postRemoved.isEmpty()
                    || !frameAdded.isEmpty() || !frameRemoved.isEmpty();
            if (!anyChange) { unchanged++; continue; }

            totalPreAdded += preAdded.size();
            totalPreRemoved += preRemoved.size();
            totalPostAdded += postAdded.size();
            totalPostRemoved += postRemoved.size();

            if (!preAdded.isEmpty() && preRemoved.isEmpty()) preStrengthened++;
            else if (preAdded.isEmpty() && !preRemoved.isEmpty()) preWeakened++;
            else if (!preAdded.isEmpty()) preMixed++;

            if (!postAdded.isEmpty() && postRemoved.isEmpty()) postStrengthened++;
            else if (postAdded.isEmpty() && !postRemoved.isEmpty()) postWeakened++;
            else if (!postAdded.isEmpty()) postMixed++;

            if (!frameAdded.isEmpty() || !frameRemoved.isEmpty()) frameChanged++;

            // A precondition strengthened in the new version is the
            // candidate-breaking case: a client that called the old version
            // may now violate the added requires-clause.
            if (!preAdded.isEmpty() && examples.size() < 12) {
                examples.add(sig + "\n      +requires " + String.join(" | ", preAdded)
                        + (preRemoved.isEmpty() ? "" : "\n      -requires " + String.join(" | ", preRemoved)));
            }
            if (!preAdded.isEmpty()) {
                fullStrengthenedDump.append(sig).append('\n');
                for (String c : preAdded) fullStrengthenedDump.append("    +requires ").append(c).append('\n');
                for (String c : preRemoved) fullStrengthenedDump.append("    -requires ").append(c).append('\n');
            }
        }

        StringBuilder r = new StringBuilder();
        r.append("Experiment 01 (detection step): inferred-spec diff, ")
         .append("commons-lang3 3.12.0 -> 3.14.0\n");
        r.append("===========================================================\n");
        r.append(String.format("methods with inferred spec, 3.12.0   : %d%n", oldSpecs.size()));
        r.append(String.format("methods with inferred spec, 3.14.0   : %d%n", newSpecs.size()));
        r.append(String.format("methods present in both versions     : %d%n", inBoth.size()));
        r.append(String.format("methods only in 3.12.0 (removed)     : %d%n", onlyOld.size()));
        r.append(String.format("methods only in 3.14.0 (added)       : %d%n", onlyNew.size()));
        r.append("-----------------------------------------------------------\n");
        r.append(String.format("of the %d common methods:%n", inBoth.size()));
        r.append(String.format("  inferred spec UNCHANGED            : %d%n", unchanged));
        r.append(String.format("  inferred spec CHANGED              : %d%n", inBoth.size() - unchanged));
        r.append("-----------------------------------------------------------\n");
        r.append("precondition change (candidate compatibility signal):\n");
        r.append(String.format("  precondition STRENGTHENED (+req)   : %d   <- candidate-breaking%n", preStrengthened));
        r.append(String.format("  precondition WEAKENED (-req)       : %d%n", preWeakened));
        r.append(String.format("  precondition MIXED (+ and -)       : %d%n", preMixed));
        r.append("postcondition change:\n");
        r.append(String.format("  postcondition STRENGTHENED (+ens)  : %d%n", postStrengthened));
        r.append(String.format("  postcondition WEAKENED (-ens)      : %d   <- candidate-breaking%n", postWeakened));
        r.append(String.format("  postcondition MIXED (+ and -)      : %d%n", postMixed));
        r.append(String.format("  frame (assignable) changed         : %d%n", frameChanged));
        r.append("-----------------------------------------------------------\n");
        r.append(String.format("total requires-clauses added         : %d%n", totalPreAdded));
        r.append(String.format("total requires-clauses removed       : %d%n", totalPreRemoved));
        r.append(String.format("total ensures-clauses added          : %d%n", totalPostAdded));
        r.append(String.format("total ensures-clauses removed        : %d%n", totalPostRemoved));
        r.append("-----------------------------------------------------------\n");
        r.append("examples of methods with a STRENGTHENED precondition\n");
        r.append("(client calling 3.12.0 may violate the added requires in 3.14.0):\n");
        for (String ex : examples) r.append("    ").append(ex).append('\n');
        r.append("\nNote: this is the syntactic detection step (Exp01 H1). SMT\n");
        r.append("subsumption (does pre_new imply pre_old?) and changelog-validated\n");
        r.append("precision/recall (Exp01 H3 / Exp02) are not run here.\n");

        System.out.println(r);

        Path out = Paths.get("journal", "thesis", "experiments", "results", "exp01_specdiff.txt");
        Files.createDirectories(out.getParent());
        Files.writeString(out, r.toString());

        Path full = Paths.get("journal", "thesis", "experiments", "results",
                "exp01_specdiff_strengthened_full.txt");
        Files.writeString(full, "All methods with added requires clause (commons-lang3 3.12.0 -> 3.14.0)\n"
                + "===========================================================\n" + fullStrengthenedDump);

        assertTrue(inBoth.size() > 0, "expected overlapping methods between versions");
    }

    private static Set<String> minus(List<String> a, List<String> b) {
        Set<String> r = new LinkedHashSet<>(a);
        r.removeAll(b);
        return r;
    }

    private Map<String, MethodSpecification> inferAll(Path sourcesJar) throws IOException {
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
                String pkg = cu.getPackageDeclaration().map(d -> d.getNameAsString()).orElse("");
                for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                    String fqcn = pkg.isEmpty() ? clazz.getNameAsString() : pkg + "." + clazz.getNameAsString();
                    for (MethodDeclaration method : clazz.getMethods()) {
                        declarations.put(signatureOf(fqcn, method), method);
                    }
                }
            }
        }

        CallGraph callGraph = new CallGraphBuilder().buildFromCompilationUnits(compilationUnits);
        SpecificationCache cache = new SpecificationCache();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer(cache, callGraph);

        Map<String, MethodSpecification> specs = new HashMap<>();
        for (Map.Entry<String, MethodDeclaration> e : declarations.entrySet()) {
            try {
                MethodSpecification spec = inferrer.inferSpecification(e.getValue());
                cache.put(e.getKey(), spec);
                // Only keep methods that received at least one clause, so the
                // diff is over methods the inferrer actually specified.
                if (!spec.getPreconditions().isEmpty() || !spec.getPostconditions().isEmpty()
                        || !spec.getAssignableClauses().isEmpty()) {
                    specs.put(e.getKey(), spec);
                }
            } catch (Exception ex) {
                // skip methods the inferrer cannot process
            }
        }
        return specs;
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
