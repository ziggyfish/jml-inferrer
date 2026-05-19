package com.jml.inferrer.embedder;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.analysis.MethodSpecificationInferrer;
import com.jml.inferrer.model.MethodSpecification;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.read.AsmJmlSpecReader;
import com.jml.spec.write.AsmJmlSpecWriter;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.Opcodes;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Article 2 RQ2 follow-up: a real-world end-to-end evaluation of embedding
 * <em>actually inferred</em> JML specifications into Apache Commons
 * Lang's compiled bytecode.
 *
 * <p>The synthetic-spec validation in {@link OssJarValidationTest} isolates
 * the embedding mechanism (does the carrier preserve what was written?).
 * This test closes the synthetic-vs-real gap on the headline corpus: it
 * runs the {@link MethodSpecificationInferrer} over every Commons Lang
 * 3.14.0 source file, embeds the produced {@link MethodSpec} map into
 * the corresponding binary JAR, reads back, and measures fidelity plus
 * spec-shape coverage.</p>
 *
 * <p>Disabled when either the sources JAR or the binary JAR is missing
 * from the local Maven cache. Both are pulled by
 * {@code mvn dependency:get -Dartifact=org.apache.commons:commons-lang3:3.14.0:jar:sources}.</p>
 *
 * <p>Results are appended to
 * {@code journal/rq2_commons_lang_real_inference.txt}.</p>
 */
class CommonsLangRealInferenceTest {

    private static final Path COMMONS_LANG_JAR = Paths.get(
            System.getProperty("user.home"),
            ".m2", "repository", "org", "apache", "commons", "commons-lang3",
            "3.14.0", "commons-lang3-3.14.0.jar");

    private static final Path COMMONS_LANG_SOURCES = Paths.get(
            System.getProperty("user.home"),
            ".m2", "repository", "org", "apache", "commons", "commons-lang3",
            "3.14.0", "commons-lang3-3.14.0-sources.jar");

    static boolean inputsAvailable() {
        return Files.exists(COMMONS_LANG_JAR) && Files.exists(COMMONS_LANG_SOURCES);
    }

    @Test
    @EnabledIf("inputsAvailable")
    void commonsLangRealInferenceRoundtrip() throws IOException {
        // Pass 1: read every .java in the sources JAR, parse it, run the
        // inferrer on every method declaration.
        InferenceResult inference = runInferenceOverSourcesJar();
        assertTrue(inference.specsWithClauses.size() > 0,
                "should infer at least one non-empty spec from Commons Lang");

        // Pass 2: embed into a copy of the binary JAR.
        Path embeddedJar = Files.createTempFile("commons-lang-real-", ".jar");
        long embedStart = System.nanoTime();
        new AsmJmlSpecWriter().embedJar(COMMONS_LANG_JAR, embeddedJar, inference.specsWithClauses);
        long embedNanos = System.nanoTime() - embedStart;

        try {
            // Pass 3: read back the embedded JAR.
            long readStart = System.nanoTime();
            Map<MethodKey, MethodSpec> readBack = new AsmJmlSpecReader().readJar(embeddedJar);
            long readNanos = System.nanoTime() - readStart;

            // Match every inferred spec against its readback. Methods may
            // be missing from the JAR (synthetic accessors, javac
            // transformations) or descriptors may differ; we measure
            // fidelity rather than assert absolute equality.
            int matched = 0, mismatches = 0, missing = 0;
            for (Map.Entry<MethodKey, MethodSpec> e : inference.specsWithClauses.entrySet()) {
                MethodSpec out = readBack.get(e.getKey());
                if (out == null) { missing++; continue; }
                if (specEquals(e.getValue(), out)) matched++; else mismatches++;
            }
            double fidelity = (double) matched / inference.specsWithClauses.size();

            // Compute byte overhead between original JAR and embedded JAR.
            long originalBytes = Files.size(COMMONS_LANG_JAR);
            long embeddedBytes = Files.size(embeddedJar);
            double overheadPct = (double)(embeddedBytes - originalBytes) / originalBytes * 100.0;

            int totalMethods = inference.specsWithClauses.size();
            int embedThroughput = (int) (totalMethods / (embedNanos / 1_000_000_000.0));
            int readThroughput = (int) (totalMethods / (readNanos / 1_000_000_000.0));

            // Persist the headline metrics line plus the shape histogram.
            Path metrics = Paths.get("journal", "rq2_commons_lang_real_inference.txt");
            Files.createDirectories(metrics.getParent());
            StringBuilder report = new StringBuilder();
            report.append(String.format(
                    "commons-lang3-3.14.0 (real inference) | sourceFiles=%d totalMethods=%d specsInferred=%d "
                    + "specsWithClauses=%d matched=%d missing=%d mismatches=%d fidelity=%.2f%% "
                    + "originalBytes=%d embeddedBytes=%d overhead=%.2f%% "
                    + "embedThroughput=%d m/s readThroughput=%d m/s%n",
                    inference.sourceFilesProcessed,
                    inference.methodsSeen,
                    inference.specsInferred,
                    totalMethods,
                    matched, missing, mismatches,
                    100.0 * fidelity,
                    originalBytes, embeddedBytes, overheadPct,
                    embedThroughput, readThroughput));
            report.append(String.format(
                    "  shape coverage: requires=%d ensures=%d assignable=%d loopInvariant=%d "
                    + "withQuantifier=%d withOld=%d withResult=%d branchConditional=%d%n",
                    inference.shapeRequires, inference.shapeEnsures,
                    inference.shapeAssignable, inference.shapeLoopInvariant,
                    inference.shapeQuantifier, inference.shapeOld,
                    inference.shapeResult, inference.shapeBranchConditional));
            Files.writeString(metrics, report.toString(),
                    java.nio.file.StandardOpenOption.CREATE,
                    java.nio.file.StandardOpenOption.APPEND);

            // Console echo for the test log.
            System.out.println(report);

            // Headline assertion: among methods that received a spec AND
            // a matching descriptor in the JAR, equality must be exact.
            assertEquals(0, mismatches,
                    "every successfully-read spec must equal the spec written");
            assertTrue(fidelity >= 0.50,
                    String.format("real-inference fidelity %.1f%% unexpectedly low "
                            + "(matched=%d missing=%d total=%d)",
                            100*fidelity, matched, missing, totalMethods));
        } finally {
            Files.deleteIfExists(embeddedJar);
        }
    }

    /**
     * Walk every .java entry in the sources JAR. For each compilation unit,
     * resolve the class to its internal-name (com/example/Foo), then walk
     * every method declaration and run the inferrer. Cross-reference
     * inferred (sourceName) against the binary JAR's method-name set per
     * class to recover the bytecode descriptor.
     */
    private InferenceResult runInferenceOverSourcesJar() throws IOException {
        Map<String, Set<String>> bytecodeMethods = readBytecodeMethodNames(COMMONS_LANG_JAR);
        InferenceResult result = new InferenceResult();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer();
        JavaParser parser = new JavaParser();

        try (JarFile jar = new JarFile(COMMONS_LANG_SOURCES.toFile())) {
            Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!entry.getName().endsWith(".java")) continue;
                if (entry.getName().startsWith("META-INF/")) continue;
                result.sourceFilesProcessed++;
                String source;
                try (InputStream in = jar.getInputStream(entry)) {
                    source = new String(in.readAllBytes());
                }
                CompilationUnit cu = parser.parse(source).getResult().orElse(null);
                if (cu == null) continue;

                String pkg = cu.getPackageDeclaration()
                        .map(d -> d.getNameAsString().replace('.', '/'))
                        .orElse("");
                for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                    String internalClass = pkg.isEmpty() ? clazz.getNameAsString()
                            : pkg + "/" + clazz.getNameAsString();
                    Set<String> bytecodeForClass = bytecodeMethods.getOrDefault(internalClass, Set.of());
                    for (MethodDeclaration method : clazz.getMethods()) {
                        result.methodsSeen++;
                        MethodSpecification methodSpec;
                        try {
                            methodSpec = inferrer.inferSpecification(method);
                        } catch (Exception ex) {
                            result.inferenceFailures++;
                            continue;
                        }
                        result.specsInferred++;
                        if (methodSpec.getPreconditions().isEmpty()
                                && methodSpec.getPostconditions().isEmpty()
                                && methodSpec.getAssignableClauses().isEmpty()
                                && methodSpec.getLoopInvariants().isEmpty()) {
                            continue;
                        }
                        String descriptor = findMatchingDescriptor(
                                method.getNameAsString(),
                                method.getParameters().size(),
                                bytecodeForClass);
                        if (descriptor == null) continue;
                        MethodSpec embeddable = InferrerSpecConverter.toEmbeddable(methodSpec);
                        result.specsWithClauses.put(
                                new MethodKey(internalClass, method.getNameAsString(), descriptor),
                                embeddable);
                    }
                }
            }
        }
        // Compute shape coverage on the FINAL map so overload-collisions do
        // not inflate counters. One pass over the de-duplicated specs.
        for (MethodSpec s : result.specsWithClauses.values()) {
            countShape(result, s);
        }
        return result;
    }

    private static void countShape(InferenceResult r, MethodSpec s) {
        if (!s.requires().isEmpty()) r.shapeRequires++;
        if (!s.ensures().isEmpty()) r.shapeEnsures++;
        if (!s.assignable().isEmpty()) r.shapeAssignable++;
        if (!s.loopInvariant().isEmpty()) r.shapeLoopInvariant++;
        boolean q = false, o = false, res = false, br = false;
        java.util.List<String> all = new java.util.ArrayList<>();
        all.addAll(s.requires());
        all.addAll(s.ensures());
        all.addAll(s.loopInvariant());
        for (String clause : all) {
            if (clause.contains("\\forall") || clause.contains("\\exists")
                    || clause.contains("\\sum") || clause.contains("\\product")
                    || clause.contains("\\num_of")) q = true;
            if (clause.contains("\\old")) o = true;
            if (clause.contains("\\result")) res = true;
            if (clause.contains("==>")) br = true;
        }
        if (q) r.shapeQuantifier++;
        if (o) r.shapeOld++;
        if (res) r.shapeResult++;
        if (br) r.shapeBranchConditional++;
    }

    private static void updateShapeCounters(InferenceResult r, MethodSpecification s) {
        if (!s.getPreconditions().isEmpty()) r.shapeRequires++;
        if (!s.getPostconditions().isEmpty()) r.shapeEnsures++;
        if (!s.getAssignableClauses().isEmpty()) r.shapeAssignable++;
        if (!s.getLoopInvariants().isEmpty()) r.shapeLoopInvariant++;
        boolean q = false, o = false, res = false, br = false;
        for (String clause : s.getPreconditions()) {
            if (clause.contains("\\forall") || clause.contains("\\exists")
                    || clause.contains("\\sum") || clause.contains("\\product")
                    || clause.contains("\\num_of")) q = true;
            if (clause.contains("\\old")) o = true;
            if (clause.contains("==>")) br = true;
        }
        for (String clause : s.getPostconditions()) {
            if (clause.contains("\\forall") || clause.contains("\\exists")
                    || clause.contains("\\sum") || clause.contains("\\product")
                    || clause.contains("\\num_of")) q = true;
            if (clause.contains("\\old")) o = true;
            if (clause.contains("\\result")) res = true;
            if (clause.contains("==>")) br = true;
        }
        for (String clause : s.getLoopInvariants()) {
            if (clause.contains("\\forall") || clause.contains("\\exists")
                    || clause.contains("\\sum") || clause.contains("\\product")
                    || clause.contains("\\num_of")) q = true;
            if (clause.contains("\\old")) o = true;
            if (clause.contains("==>")) br = true;
        }
        if (q) r.shapeQuantifier++;
        if (o) r.shapeOld++;
        if (res) r.shapeResult++;
        if (br) r.shapeBranchConditional++;
    }

    private static Map<String, Set<String>> readBytecodeMethodNames(Path jarPath) throws IOException {
        Map<String, Set<String>> result = new HashMap<>();
        try (JarFile jar = new JarFile(jarPath.toFile())) {
            Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!entry.getName().endsWith(".class")) continue;
                String internal = entry.getName().substring(0,
                        entry.getName().length() - ".class".length());
                Set<String> methods = new HashSet<>();
                try (InputStream in = jar.getInputStream(entry)) {
                    new ClassReader(in.readAllBytes()).accept(new ClassVisitor(Opcodes.ASM9) {
                        @Override
                        public org.objectweb.asm.MethodVisitor visitMethod(int access, String name, String descriptor,
                                String signature, String[] exceptions) {
                            methods.add(name + descriptor);
                            return null;
                        }
                    }, ClassReader.SKIP_CODE | ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
                }
                result.put(internal, methods);
            }
        }
        return result;
    }

    /**
     * Find a bytecode descriptor matching the source method by name AND
     * parameter count. Handles overloads: {@code indexOf(String)} and
     * {@code indexOf(String, int)} get distinct keys in the embedded JAR.
     * If multiple bytecode entries share both name and arity, the first
     * is returned (rare; usually means a generic-erasure collision).
     */
    private static String findMatchingDescriptor(String name, int sourceArity,
                                                 Set<String> bytecodeMethods) {
        for (String entry : bytecodeMethods) {
            int sep = entry.indexOf('(');
            if (sep <= 0 || !entry.substring(0, sep).equals(name)) continue;
            String descriptor = entry.substring(sep);
            if (countDescriptorParameters(descriptor) == sourceArity) {
                return descriptor;
            }
        }
        return null;
    }

    /**
     * Count the parameter slots in a JVM method descriptor like
     * {@code (Ljava/lang/String;I[BJ)V}. Strings reference types ({@code L...;}),
     * primitives ({@code I, J, F, D, Z, B, S, C}), and array dimensions
     * ({@code [}) consume one slot each (excluding the array prefix).
     */
    private static int countDescriptorParameters(String descriptor) {
        int count = 0;
        int i = 1; // skip '('
        while (i < descriptor.length() && descriptor.charAt(i) != ')') {
            char c = descriptor.charAt(i);
            if (c == '[') { i++; continue; } // array prefix; consume and stay on element
            if (c == 'L') {
                int end = descriptor.indexOf(';', i);
                i = end + 1;
            } else {
                i++;
            }
            count++;
        }
        return count;
    }

    private static boolean specEquals(MethodSpec a, MethodSpec b) {
        return a.requires().equals(b.requires())
                && a.ensures().equals(b.ensures())
                && a.assignable().equals(b.assignable())
                && a.loopInvariant().equals(b.loopInvariant());
    }

    private static final class InferenceResult {
        int sourceFilesProcessed = 0;
        int methodsSeen = 0;
        int specsInferred = 0;
        int inferenceFailures = 0;
        // Shape coverage
        int shapeRequires = 0;
        int shapeEnsures = 0;
        int shapeAssignable = 0;
        int shapeLoopInvariant = 0;
        int shapeQuantifier = 0;
        int shapeOld = 0;
        int shapeResult = 0;
        int shapeBranchConditional = 0;
        Map<MethodKey, MethodSpec> specsWithClauses = new HashMap<>();
    }
}
