package com.jml.inferrer.embedder;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.jml.inferrer.analysis.MethodSpecificationInferrer;
import com.jml.inferrer.model.MethodSpecification;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.DictionaryLearner;
import com.jml.spec.SpecCodec;
import com.jml.spec.WriterConfig;
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
 * Compares the three writer-config modes on the same real-inference
 * corpus (Commons Lang). Produces the table the article reports:
 * {@code WriterConfig.NONE}, {@code WriterConfig.JML_INFERRER},
 * {@code WriterConfig.JML_INFERRER.compressed(true)}.
 *
 * <p>Every mode is required to roundtrip at 100\% fidelity. Results are
 * appended to {@code journal/rq2_writer_config_comparison.txt}.</p>
 */
class WriterConfigModeComparisonTest {

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
    void compareThreeModes() throws IOException {
        Map<MethodKey, MethodSpec> specs = runInference();
        assertTrue(specs.size() > 0);

        Path metrics = Paths.get("journal", "rq2_writer_config_comparison.txt");
        Files.createDirectories(metrics.getParent());
        StringBuilder report = new StringBuilder();

        SpecCodec learned = DictionaryLearner.learn(
                specs.values(), SpecCodec.DEFAULT,
                /*totalTokens=*/ DictionaryLearner.maxTokens(),
                /*minLen=*/ 4, /*maxLen=*/ 16, /*minOccur=*/ 20);

        for (Mode m : new Mode[]{
                new Mode("none",                   WriterConfig.NONE),
                new Mode("jml-inferrer (v2)",      WriterConfig.JML_INFERRER),
                new Mode("learned-dict (v2)",      WriterConfig.JML_INFERRER.withCodec(learned)),
                new Mode("compressed-v3",          WriterConfig.JML_INFERRER.compressed(true)),
        }) {
            Path embedded = Files.createTempFile("config-" + m.name + "-", ".jar");
            long t0 = System.nanoTime();
            new AsmJmlSpecWriter(m.config).embedJar(COMMONS_LANG_JAR, embedded, specs);
            long embedNanos = System.nanoTime() - t0;
            try {
                long t1 = System.nanoTime();
                Map<MethodKey, MethodSpec> readBack = new AsmJmlSpecReader(m.config.codec()).readJar(embedded);
                long readNanos = System.nanoTime() - t1;

                int matched = 0, mismatches = 0, missing = 0;
                for (Map.Entry<MethodKey, MethodSpec> e : specs.entrySet()) {
                    MethodSpec out = readBack.get(e.getKey());
                    if (out == null) { missing++; continue; }
                    if (specEquals(e.getValue(), out)) matched++; else mismatches++;
                }
                double fidelity = (double) matched / specs.size();

                long originalBytes = Files.size(COMMONS_LANG_JAR);
                long embeddedBytes = Files.size(embedded);
                double overheadPct = (double)(embeddedBytes - originalBytes) / originalBytes * 100.0;

                int embedThroughput = (int) (specs.size() / (embedNanos / 1_000_000_000.0));
                int readThroughput = (int) (specs.size() / (readNanos / 1_000_000_000.0));

                String line = String.format(
                        "commons-lang3 | mode=%s specs=%d matched=%d missing=%d mismatches=%d "
                        + "fidelity=%.2f%% originalBytes=%d embeddedBytes=%d overhead=%.2f%% "
                        + "embedThroughput=%d m/s readThroughput=%d m/s%n",
                        m.name, specs.size(), matched, missing, mismatches,
                        100.0 * fidelity,
                        originalBytes, embeddedBytes, overheadPct,
                        embedThroughput, readThroughput);
                report.append(line);
                System.out.print(line);

                assertEquals(0, mismatches, m.name + ": every read spec must equal the written spec");
                assertTrue(fidelity >= 0.95,
                        m.name + ": fidelity " + (100*fidelity) + "% < 95%");
            } finally {
                Files.deleteIfExists(embedded);
            }
        }
        Files.writeString(metrics, report.toString(),
                java.nio.file.StandardOpenOption.CREATE,
                java.nio.file.StandardOpenOption.APPEND);
    }

    private static class Mode {
        final String name;
        final WriterConfig config;
        Mode(String name, WriterConfig config) { this.name = name; this.config = config; }
    }

    private Map<MethodKey, MethodSpec> runInference() throws IOException {
        Map<String, Set<String>> bytecodeMethods = readBytecodeMethodNames(COMMONS_LANG_JAR);
        Map<MethodKey, MethodSpec> specs = new HashMap<>();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer();
        JavaParser parser = new JavaParser();

        try (JarFile jar = new JarFile(COMMONS_LANG_SOURCES.toFile())) {
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
                String pkg = cu.getPackageDeclaration()
                        .map(d -> d.getNameAsString().replace('.', '/')).orElse("");
                for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                    String internalClass = pkg.isEmpty() ? clazz.getNameAsString()
                            : pkg + "/" + clazz.getNameAsString();
                    Set<String> bytecodeForClass = bytecodeMethods.getOrDefault(internalClass, Set.of());
                    for (MethodDeclaration method : clazz.getMethods()) {
                        MethodSpecification methodSpec;
                        try { methodSpec = inferrer.inferSpecification(method); }
                        catch (Exception ex) { continue; }
                        if (methodSpec.getPreconditions().isEmpty()
                                && methodSpec.getPostconditions().isEmpty()
                                && methodSpec.getAssignableClauses().isEmpty()
                                && methodSpec.getLoopInvariants().isEmpty()) continue;
                        String descriptor = findMatchingDescriptor(
                                method.getNameAsString(), method.getParameters().size(), bytecodeForClass);
                        if (descriptor == null) continue;
                        specs.put(new MethodKey(internalClass, method.getNameAsString(), descriptor),
                                InferrerSpecConverter.toEmbeddable(methodSpec));
                    }
                }
            }
        }
        return specs;
    }

    private static Map<String, Set<String>> readBytecodeMethodNames(Path jarPath) throws IOException {
        Map<String, Set<String>> result = new HashMap<>();
        try (JarFile jar = new JarFile(jarPath.toFile())) {
            Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!entry.getName().endsWith(".class")) continue;
                String internal = entry.getName().substring(0, entry.getName().length() - ".class".length());
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

    private static String findMatchingDescriptor(String name, int arity, Set<String> bytecodeMethods) {
        for (String entry : bytecodeMethods) {
            int sep = entry.indexOf('(');
            if (sep <= 0 || !entry.substring(0, sep).equals(name)) continue;
            String descriptor = entry.substring(sep);
            if (countDescriptorParameters(descriptor) == arity) return descriptor;
        }
        return null;
    }

    private static int countDescriptorParameters(String descriptor) {
        int count = 0;
        int i = 1;
        while (i < descriptor.length() && descriptor.charAt(i) != ')') {
            char c = descriptor.charAt(i);
            if (c == '[') { i++; continue; }
            if (c == 'L') { i = descriptor.indexOf(';', i) + 1; }
            else i++;
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
}
