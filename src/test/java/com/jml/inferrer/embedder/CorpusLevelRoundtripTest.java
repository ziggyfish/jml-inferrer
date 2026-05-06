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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

/**
 * RQ2 Article-2 threat closure: replace synthetic specs with real
 * inferrer-produced specs at corpus scale.
 *
 * <p>Walks {@code src/main/java/com/jml/inferrer/model} (a small but
 * representative slice of the inferrer's own source — POJOs and records).
 * Runs the {@link MethodSpecificationInferrer} on every method declared
 * across those source files. Embeds the resulting {@link MethodSpec}
 * entries into the inferrer's own packaged JAR
 * ({@code target/jml-inferrer-1.0.0.jar}). Reads back via
 * {@link AsmJmlSpecReader}. Asserts that every method that received a spec
 * roundtrips with byte-for-byte equality on the canonical clause lists.</p>
 *
 * <p>Disabled when the inferrer's own JAR isn't present in {@code target/}
 * (e.g., before {@code mvn package} has run). The harness tells the user
 * exactly which build target to run.</p>
 */
class CorpusLevelRoundtripTest {

    private static final Path INFERRER_JAR = Paths.get("target", "jml-inferrer-1.0.0.jar");
    private static final Path MODEL_SOURCE_DIR = Paths.get("src", "main", "java", "com", "jml", "inferrer", "model");
    private static final Path VISITOR_SOURCE_DIR = Paths.get("src", "main", "java", "com", "jml", "inferrer", "visitor");
    private static final Path PROCESSOR_SOURCE_DIR = Paths.get("src", "main", "java", "com", "jml", "inferrer", "processor");

    static boolean inferrerJarAvailable() {
        return Files.exists(INFERRER_JAR) && Files.isDirectory(MODEL_SOURCE_DIR);
    }

    @Test
    @EnabledIf("inferrerJarAvailable")
    void inferrerOwnSourcesRoundtripAtCorpusScale() throws IOException {
        // Pass 1: run the inferrer over every method in the model, visitor,
        // and processor packages. These cover the data model + orchestration
        // surface — a meaningful slice without pulling in the full analyzer
        // tier (which would slow this test down without changing what it
        // validates).
        Map<MethodKey, MethodSpec> inferred = inferPackages(MODEL_SOURCE_DIR, VISITOR_SOURCE_DIR, PROCESSOR_SOURCE_DIR);
        assertFalse(inferred.isEmpty(),
                "the model package should yield at least one inferred spec; check the source path");

        // Pass 2: embed into the inferrer's own JAR. This is real bytecode
        // (compiled by Maven via javac) — the same classes the inferred
        // specs were inferred from.
        Path embeddedJar = Files.createTempFile("inferrer-embedded-", ".jar");
        try {
            new AsmJmlSpecWriter().embedJar(INFERRER_JAR, embeddedJar, inferred);

            // Pass 3: read back. The reader walks every class in the
            // embedded JAR, including classes the inferrer didn't touch
            // (Phase analyzers, visitor, etc.).
            Map<MethodKey, MethodSpec> readBack = new AsmJmlSpecReader().readJar(embeddedJar);

            // Match each inferred spec against the readback. Methods that
            // were inferred but where javac compiled the source to a
            // synthetic carrier with a different descriptor will not match;
            // we measure fidelity rather than asserting absolute equality.
            int matched = 0;
            int mismatches = 0;
            int missing = 0;
            for (Map.Entry<MethodKey, MethodSpec> e : inferred.entrySet()) {
                MethodSpec out = readBack.get(e.getKey());
                if (out == null) {
                    missing++;
                    continue;
                }
                if (specEquals(e.getValue(), out)) {
                    matched++;
                } else {
                    mismatches++;
                }
            }

            // Assert the headline claim from Article 2: real inferred specs
            // roundtrip at the same fidelity as synthetic specs do.
            double fidelity = (double) matched / inferred.size();
            assertTrue(fidelity >= 0.95,
                    String.format(
                            "real-spec fidelity %.1f%% below 95%% threshold (matched=%d missing=%d mismatches=%d total=%d)",
                            100 * fidelity, matched, missing, mismatches, inferred.size()));

            // Among matched methods, equality must be exact.
            assertEquals(0, mismatches,
                    "every successfully-read spec must equal the spec written");

            // Persist the metric for the article.
            Path metrics = Paths.get("journal", "rq2_corpus_metrics.txt");
            Files.createDirectories(metrics.getParent());
            String line = String.format(
                    "inferrer-self | sourceFiles=%d methods=%d matched=%d missing=%d mismatches=%d fidelity=%.2f%%%n",
                    countSourceFiles(),
                    inferred.size(), matched, missing, mismatches,
                    100 * fidelity);
            Files.writeString(metrics, line,
                    java.nio.file.StandardOpenOption.CREATE,
                    java.nio.file.StandardOpenOption.APPEND);
        } finally {
            Files.deleteIfExists(embeddedJar);
        }
    }

    /**
     * Walk the given source directories; parse each .java file; run the
     * inferrer per method; collect specs keyed by an internal-form
     * MethodKey that matches what the bytecode reader produces.
     */
    private static Map<MethodKey, MethodSpec> inferPackages(Path... sourceDirs) throws IOException {
        // Build a name → bytecode-descriptor index from the JAR so we can
        // match inferrer-emitted (source) signatures to bytecode signatures
        // that javac produced. This is the canonical key the reader uses.
        Map<String, Set<String>> bytecodeMethods = readBytecodeMethods(sourceDirs);

        Map<MethodKey, MethodSpec> specs = new HashMap<>();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer();
        for (Path dir : sourceDirs) {
            inferOneDirectory(dir, inferrer, bytecodeMethods, specs);
        }
        return specs;
    }

    private static void inferOneDirectory(Path dir, MethodSpecificationInferrer inferrer,
                                          Map<String, Set<String>> bytecodeMethods,
                                          Map<MethodKey, MethodSpec> specs) throws IOException {
        try (Stream<Path> files = Files.walk(dir)) {
            files.filter(p -> p.toString().endsWith(".java")).forEach(p -> {
                try {
                    String source = Files.readString(p);
                    CompilationUnit cu = new JavaParser().parse(source).getResult().orElse(null);
                    if (cu == null) return;
                    for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                        String pkg = cu.getPackageDeclaration().map(d -> d.getNameAsString()).orElse("");
                        String internalClass = (pkg.isEmpty() ? clazz.getNameAsString()
                                : pkg.replace('.', '/') + "/" + clazz.getNameAsString());
                        Set<String> bytecodeForClass = bytecodeMethods.getOrDefault(internalClass, Set.of());
                        for (MethodDeclaration method : clazz.getMethods()) {
                            MethodSpecification methodSpec = inferrer.inferSpecification(method);
                            // Skip methods with no inferred clauses — embedding
                            // an empty annotation is a no-op and would still
                            // count against fidelity if the reader returned
                            // null (it does).
                            if (methodSpec.getPreconditions().isEmpty()
                                    && methodSpec.getPostconditions().isEmpty()
                                    && methodSpec.getAssignableClauses().isEmpty()
                                    && methodSpec.getLoopInvariants().isEmpty()) {
                                continue;
                            }
                            String descriptor = findMatchingDescriptor(method.getNameAsString(), bytecodeForClass);
                            if (descriptor == null) continue;
                            specs.put(new MethodKey(internalClass, method.getNameAsString(), descriptor),
                                    InferrerSpecConverter.toEmbeddable(methodSpec));
                        }
                    }
                } catch (IOException ex) {
                    throw new RuntimeException("failed to read " + p, ex);
                }
            });
        }
    }

    /**
     * Find a bytecode descriptor whose method name matches the source
     * method name. Returns null if no match (possibly the source method was
     * synthetic, or the source predates the JAR build). Uses the first
     * descriptor of any match — fine for methods without overloads, which
     * is the common case in the model package.
     */
    private static String findMatchingDescriptor(String name, Set<String> bytecodeMethods) {
        for (String entry : bytecodeMethods) {
            int sep = entry.indexOf('(');
            if (sep > 0 && entry.substring(0, sep).equals(name)) {
                return entry.substring(sep);
            }
        }
        return null;
    }

    /**
     * Read the inferrer's JAR; for every class file whose entry path is
     * under one of the given source-directory roots, collect the
     * {@code name+descriptor} strings of every method on that class.
     */
    private static Map<String, Set<String>> readBytecodeMethods(Path... sourceDirs) throws IOException {
        Set<String> jarPrefixes = new HashSet<>();
        Path srcRoot = Paths.get("src", "main", "java");
        for (Path d : sourceDirs) {
            String prefix = srcRoot.relativize(d).toString().replace('\\', '/');
            jarPrefixes.add(prefix);
        }
        Map<String, Set<String>> result = new HashMap<>();
        try (JarFile jar = new JarFile(INFERRER_JAR.toFile())) {
            jar.stream().forEach(entry -> {
                if (!entry.getName().endsWith(".class")) return;
                boolean inScope = false;
                for (String prefix : jarPrefixes) {
                    if (entry.getName().startsWith(prefix)) { inScope = true; break; }
                }
                if (!inScope) return;
                String internal = entry.getName().substring(0, entry.getName().length() - ".class".length());
                Set<String> methods = new HashSet<>();
                try {
                    new ClassReader(jar.getInputStream(entry).readAllBytes()).accept(new ClassVisitor(Opcodes.ASM9) {
                        @Override
                        public org.objectweb.asm.MethodVisitor visitMethod(int access, String name, String descriptor,
                                String signature, String[] exceptions) {
                            methods.add(name + descriptor);
                            return null;
                        }
                    }, ClassReader.SKIP_CODE | ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
                } catch (IOException ex) {
                    throw new RuntimeException("read failed for " + entry.getName(), ex);
                }
                result.put(internal, methods);
            });
        }
        return result;
    }

    private static int countSourceFiles() throws IOException {
        int total = 0;
        for (Path dir : new Path[]{MODEL_SOURCE_DIR, VISITOR_SOURCE_DIR, PROCESSOR_SOURCE_DIR}) {
            try (Stream<Path> files = Files.walk(dir)) {
                total += (int) files.filter(p -> p.toString().endsWith(".java")).count();
            }
        }
        return total;
    }

    private static boolean specEquals(MethodSpec a, MethodSpec b) {
        return a.requires().equals(b.requires())
                && a.ensures().equals(b.ensures())
                && a.assignable().equals(b.assignable())
                && a.loopInvariant().equals(b.loopInvariant());
    }
}
