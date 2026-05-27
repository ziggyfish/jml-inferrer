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
 * Article 2 RQ2 follow-up: real-world end-to-end evaluation of embedding
 * actually inferred JML specifications into compiled bytecode, on each
 * of the three article-2 corpora (Commons Lang, Commons IO, Guava).
 *
 * <p>Runs the {@link MethodSpecificationInferrer} over each library's
 * source jar, resolves source signatures to bytecode descriptors by name
 * and parameter count, embeds the resulting {@link MethodSpec} map into
 * the corresponding binary jar via {@link AsmJmlSpecWriter}, reads back
 * via {@link AsmJmlSpecReader}, and checks clause-list equality plus
 * spec-shape coverage. Results appended to
 * {@code journal/rq2_commons_lang_real_inference.txt}.</p>
 *
 * <p>Each per-library test is disabled when its sources jar is absent.
 * Pull all three with:
 * {@code mvn dependency:get -Dartifact=org.apache.commons:commons-lang3:3.14.0:jar:sources},
 * and analogous invocations for {@code commons-io:commons-io:2.13.0} and
 * {@code com.google.guava:guava:33.3.0-jre}.</p>
 */
class CommonsLangRealInferenceTest {

    private static final Path COMMONS_LANG_JAR = m2Path(
            "org/apache/commons/commons-lang3/3.14.0", "commons-lang3-3.14.0.jar");
    private static final Path COMMONS_LANG_SOURCES = m2Path(
            "org/apache/commons/commons-lang3/3.14.0", "commons-lang3-3.14.0-sources.jar");

    private static final Path COMMONS_IO_JAR = m2Path(
            "commons-io/commons-io/2.13.0", "commons-io-2.13.0.jar");
    private static final Path COMMONS_IO_SOURCES = m2Path(
            "commons-io/commons-io/2.13.0", "commons-io-2.13.0-sources.jar");

    private static final Path GUAVA_JAR = m2Path(
            "com/google/guava/guava/33.3.0-jre", "guava-33.3.0-jre.jar");
    private static final Path GUAVA_SOURCES = m2Path(
            "com/google/guava/guava/33.3.0-jre", "guava-33.3.0-jre-sources.jar");

    private static final Path COMMONS_MATH_JAR = m2Path(
            "org/apache/commons/commons-math3/3.6.1", "commons-math3-3.6.1.jar");
    private static final Path COMMONS_MATH_SOURCES = m2Path(
            "org/apache/commons/commons-math3/3.6.1", "commons-math3-3.6.1-sources.jar");

    private static final Path JOOL_JAR = m2Path(
            "org/jooq/jool/0.9.14", "jool-0.9.14.jar");
    private static final Path JOOL_SOURCES = m2Path(
            "org/jooq/jool/0.9.14", "jool-0.9.14-sources.jar");

    private static final Path VAVR_JAR = m2Path(
            "io/vavr/vavr/0.10.4", "vavr-0.10.4.jar");
    private static final Path VAVR_SOURCES = m2Path(
            "io/vavr/vavr/0.10.4", "vavr-0.10.4-sources.jar");

    private static Path m2Path(String repoSub, String file) {
        return Paths.get(System.getProperty("user.home"), ".m2", "repository")
                .resolve(repoSub).resolve(file);
    }

    static boolean commonsLangAvailable() {
        return Files.exists(COMMONS_LANG_JAR) && Files.exists(COMMONS_LANG_SOURCES);
    }

    static boolean commonsIoAvailable() {
        return Files.exists(COMMONS_IO_JAR) && Files.exists(COMMONS_IO_SOURCES);
    }

    static boolean guavaAvailable() {
        return Files.exists(GUAVA_JAR) && Files.exists(GUAVA_SOURCES);
    }

    static boolean commonsMathAvailable() {
        return Files.exists(COMMONS_MATH_JAR) && Files.exists(COMMONS_MATH_SOURCES);
    }

    static boolean joolAvailable() {
        return Files.exists(JOOL_JAR) && Files.exists(JOOL_SOURCES);
    }

    static boolean vavrAvailable() {
        return Files.exists(VAVR_JAR) && Files.exists(VAVR_SOURCES);
    }

    @Test
    @EnabledIf("commonsLangAvailable")
    void commonsLangRealInferenceRoundtrip() throws IOException {
        runOn("commons-lang3-3.14.0", COMMONS_LANG_JAR, COMMONS_LANG_SOURCES);
    }

    @Test
    @EnabledIf("commonsIoAvailable")
    void commonsIoRealInferenceRoundtrip() throws IOException {
        runOn("commons-io-2.13.0", COMMONS_IO_JAR, COMMONS_IO_SOURCES);
    }

    @Test
    @EnabledIf("guavaAvailable")
    void guavaRealInferenceRoundtrip() throws IOException {
        runOn("guava-33.3.0-jre", GUAVA_JAR, GUAVA_SOURCES);
    }

    @Test
    @EnabledIf("commonsMathAvailable")
    void commonsMathRealInferenceRoundtrip() throws IOException {
        runOn("commons-math3-3.6.1", COMMONS_MATH_JAR, COMMONS_MATH_SOURCES);
    }

    @Test
    @EnabledIf("joolAvailable")
    void joolRealInferenceRoundtrip() throws IOException {
        runOn("jool-0.9.14", JOOL_JAR, JOOL_SOURCES);
    }

    @Test
    @EnabledIf("vavrAvailable")
    void vavrRealInferenceRoundtrip() throws IOException {
        runOn("vavr-0.10.4", VAVR_JAR, VAVR_SOURCES);
    }

    private void runOn(String label, Path binaryJar, Path sourcesJar) throws IOException {
        InferenceResult inference = runInferenceOverSourcesJar(binaryJar, sourcesJar);
        assertTrue(inference.specsWithClauses.size() > 0,
                "should infer at least one non-empty spec from " + label);

        Path embeddedJar = Files.createTempFile(label + "-real-", ".jar");
        long embedStart = System.nanoTime();
        new AsmJmlSpecWriter().embedJar(binaryJar, embeddedJar, inference.specsWithClauses);
        long embedNanos = System.nanoTime() - embedStart;

        try {
            long readStart = System.nanoTime();
            Map<MethodKey, MethodSpec> readBack = new AsmJmlSpecReader().readJar(embeddedJar);
            long readNanos = System.nanoTime() - readStart;

            int matched = 0, mismatches = 0, missing = 0;
            for (Map.Entry<MethodKey, MethodSpec> e : inference.specsWithClauses.entrySet()) {
                MethodSpec out = readBack.get(e.getKey());
                if (out == null) { missing++; continue; }
                if (specEquals(e.getValue(), out)) matched++; else mismatches++;
            }
            double fidelity = (double) matched / inference.specsWithClauses.size();

            long originalBytes = Files.size(binaryJar);
            long embeddedBytes = Files.size(embeddedJar);
            double overheadPct = (double)(embeddedBytes - originalBytes) / originalBytes * 100.0;

            int totalMethods = inference.specsWithClauses.size();
            int embedThroughput = (int) (totalMethods / (embedNanos / 1_000_000_000.0));
            int readThroughput = (int) (totalMethods / (readNanos / 1_000_000_000.0));

            Path metrics = Paths.get("journal", "rq2_commons_lang_real_inference.txt");
            Files.createDirectories(metrics.getParent());
            StringBuilder report = new StringBuilder();
            report.append(String.format(
                    "%s (real inference) | sourceFiles=%d totalMethods=%d specsInferred=%d "
                    + "specsWithClauses=%d matched=%d missing=%d mismatches=%d fidelity=%.2f%% "
                    + "originalBytes=%d embeddedBytes=%d overhead=%.2f%% "
                    + "embedThroughput=%d m/s readThroughput=%d m/s%n",
                    label,
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
            System.out.println(report);

            assertEquals(0, mismatches,
                    "every successfully-read spec must equal the spec written");
            assertTrue(fidelity >= 0.50,
                    String.format("%s: real-inference fidelity %.1f%% unexpectedly low "
                            + "(matched=%d missing=%d total=%d)",
                            label, 100*fidelity, matched, missing, totalMethods));
        } finally {
            Files.deleteIfExists(embeddedJar);
        }
    }

    private InferenceResult runInferenceOverSourcesJar(Path binaryJar, Path sourcesJar) throws IOException {
        Map<String, Set<String>> bytecodeMethods = readBytecodeMethodNames(binaryJar);
        InferenceResult result = new InferenceResult();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer();
        JavaParser parser = new JavaParser();

        try (JarFile jar = new JarFile(sourcesJar.toFile())) {
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
                CompilationUnit cu;
                try {
                    cu = parser.parse(source).getResult().orElse(null);
                } catch (RuntimeException ex) {
                    continue; // parse failure on this file -> skip
                }
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

    private static int countDescriptorParameters(String descriptor) {
        int count = 0;
        int i = 1;
        while (i < descriptor.length() && descriptor.charAt(i) != ')') {
            char c = descriptor.charAt(i);
            if (c == '[') { i++; continue; }
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
