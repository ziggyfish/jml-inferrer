package com.jml.inferrer.embedder;

import com.jml.spec.Kind;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.SignalsClause;
import com.jml.spec.read.AsmJmlSpecReader;
import com.jml.spec.write.AsmJmlSpecWriter;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import static org.junit.jupiter.api.Assertions.*;

/**
 * RQ2 Phase 2A.7 — empirical validation of the embedder against a real OSS
 * JAR. Measures:
 *
 * <ul>
 *   <li>Bytecode size overhead (% increase in JAR size after embedding).</li>
 *   <li>Embedding throughput (methods per second).</li>
 *   <li>Extraction throughput (methods per second).</li>
 *   <li>Roundtrip fidelity (% of methods whose embedded spec is read back
 *       byte-for-byte identical to the spec written).</li>
 * </ul>
 *
 * <p>Disabled when the target JAR isn't available locally (e.g., on CI without
 * the Maven cache populated). The harness is gated by {@link #commonsLangAvailable}
 * so the suite remains green in all environments.</p>
 *
 * <p>Numerical results are written to {@code journal/rq2_validation_metrics.txt}
 * for inclusion in Article 2's empirical validation section.</p>
 */
class OssJarValidationTest {

    private static final Path COMMONS_LANG_JAR = Paths.get(
            System.getProperty("user.home"),
            ".m2", "repository", "org", "apache", "commons", "commons-lang3",
            "3.14.0", "commons-lang3-3.14.0.jar");

    private static final Path GUAVA_JAR = Paths.get(
            System.getProperty("user.home"),
            ".m2", "repository", "com", "google", "guava", "guava",
            "33.3.0-jre", "guava-33.3.0-jre.jar");

    private static final Path COMMONS_IO_JAR = Paths.get(
            System.getProperty("user.home"),
            ".m2", "repository", "commons-io", "commons-io",
            "2.13.0", "commons-io-2.13.0.jar");

    static boolean commonsLangAvailable() {
        return Files.exists(COMMONS_LANG_JAR);
    }

    static boolean guavaAvailable() {
        return Files.exists(GUAVA_JAR);
    }

    static boolean commonsIoAvailable() {
        return Files.exists(COMMONS_IO_JAR);
    }

    @Test
    @EnabledIf("commonsLangAvailable")
    void commonsLangValidation() throws IOException {
        ValidationReport report = validate("commons-lang3-3.14.0", COMMONS_LANG_JAR);
        assertReasonableMetrics(report);
        appendMetrics(report);
    }

    @Test
    @EnabledIf("guavaAvailable")
    void guavaValidation() throws IOException {
        ValidationReport report = validate("guava-33.3.0-jre", GUAVA_JAR);
        assertReasonableMetrics(report);
        appendMetrics(report);
    }

    @Test
    @EnabledIf("commonsIoAvailable")
    void commonsIoValidation() throws IOException {
        ValidationReport report = validate("commons-io-2.13.0", COMMONS_IO_JAR);
        assertReasonableMetrics(report);
        appendMetrics(report);
    }

    @Test
    @EnabledIf("commonsLangAvailable")
    void embeddedClassLoadsWithoutJmlSpecOnClasspath() throws Exception {
        // Plan §2A.7 negative test: load an embedded class in a JVM that does
        // not have @JmlSpec on its classpath; must not raise NoClassDefFoundError
        // at class load. Reflective annotation access is allowed to throw
        // TypeNotPresentException (the documented constraint, per
        // `journal/rq2_embedding_design.md` §1).
        Map<MethodKey, MethodSpec> specs = generateSyntheticSpecs(COMMONS_LANG_JAR);
        Path embedded = Files.createTempFile("rq2-loadcheck-", ".jar");
        try {
            new AsmJmlSpecWriter().embedJar(COMMONS_LANG_JAR, embedded, specs);

            // Use a URLClassLoader rooted only at the embedded JAR — no @JmlSpec
            // type, no com.jml.* — and load a known commons-lang class.
            try (java.net.URLClassLoader loader = new java.net.URLClassLoader(
                    new java.net.URL[]{embedded.toUri().toURL()},
                    ClassLoader.getPlatformClassLoader())) {
                Class<?> stringUtils = Class.forName("org.apache.commons.lang3.StringUtils", true, loader);
                assertNotNull(stringUtils, "embedded class should load even without @JmlSpec");
                // Reflection on a method's annotations: allowed to throw
                // TypeNotPresentException, must not crash the JVM.
                java.lang.reflect.Method m = stringUtils.getDeclaredMethod("isEmpty", CharSequence.class);
                try {
                    m.getAnnotations();
                } catch (TypeNotPresentException expected) {
                    // documented behaviour
                }
            }
        } finally {
            Files.deleteIfExists(embedded);
        }
    }

    /**
     * Run the validation harness against a single JAR.
     * Loads each class, generates a representative synthetic spec per method
     * (so the test exercises real method shapes — generics erasure, inner
     * classes, synthetic methods — without needing source), embeds, measures,
     * extracts, and computes fidelity.
     */
    private static ValidationReport validate(String label, Path jar) throws IOException {
        Map<MethodKey, MethodSpec> specs = generateSyntheticSpecs(jar);
        long originalBytes = Files.size(jar);

        Path embedded = Files.createTempFile("rq2-embed-", ".jar");
        try {
            long embedStart = System.nanoTime();
            new AsmJmlSpecWriter().embedJar(jar, embedded, specs);
            long embedNanos = System.nanoTime() - embedStart;

            long embeddedBytes = Files.size(embedded);

            long readStart = System.nanoTime();
            Map<MethodKey, MethodSpec> readBack = new AsmJmlSpecReader().readJar(embedded);
            long readNanos = System.nanoTime() - readStart;

            int matched = 0;
            int specMismatches = 0;
            java.util.List<MethodKey> sampleUnmatched = new java.util.ArrayList<>();
            for (Map.Entry<MethodKey, MethodSpec> e : specs.entrySet()) {
                MethodSpec out = readBack.get(e.getKey());
                if (out == null) {
                    if (sampleUnmatched.size() < 10) sampleUnmatched.add(e.getKey());
                    continue;
                }
                matched++;
                if (!specEquals(e.getValue(), out)) specMismatches++;
            }
            if (!sampleUnmatched.isEmpty()) {
                System.out.println("[" + label + "] sample unmatched (" + (specs.size() - matched) + " total):");
                for (MethodKey k : sampleUnmatched) {
                    System.out.println("  " + k.className() + "::" + k.methodName() + k.descriptor());
                }
            }

            return new ValidationReport(
                    label,
                    specs.size(),
                    matched,
                    specMismatches,
                    originalBytes,
                    embeddedBytes,
                    embedNanos,
                    readNanos);
        } finally {
            Files.deleteIfExists(embedded);
        }
    }

    /**
     * Walk each .class entry in the JAR. For each method (excluding bridge,
     * synthetic, and static initialisers), emit a synthetic spec of realistic
     * shape: `requires` per non-primitive parameter (`p != null`), `ensures`
     * `\result != null` for reference returns, `assignable \nothing`.
     */
    private static Map<MethodKey, MethodSpec> generateSyntheticSpecs(Path jar) throws IOException {
        Map<MethodKey, MethodSpec> specs = new HashMap<>();
        try (JarFile jf = new JarFile(jar.toFile())) {
            jf.stream().forEach(entry -> {
                if (!entry.getName().endsWith(".class")) return;
                if (entry.getName().equals("module-info.class")) return;
                String internal = entry.getName().substring(0, entry.getName().length() - ".class".length());
                try {
                    ClassReader cr = new ClassReader(jf.getInputStream(entry).readAllBytes());
                    cr.accept(new ClassVisitor(Opcodes.ASM9) {
                        @Override
                        public MethodVisitor visitMethod(int access, String name, String descriptor, String signature, String[] exceptions) {
                            if ((access & Opcodes.ACC_BRIDGE) != 0) return null;
                            if ((access & Opcodes.ACC_SYNTHETIC) != 0) return null;
                            if (name.equals("<clinit>")) return null;
                            specs.put(new MethodKey(internal, name, descriptor),
                                    syntheticSpec(descriptor));
                            return null;
                        }
                    }, ClassReader.SKIP_CODE | ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
                } catch (IOException e) {
                    throw new RuntimeException("read failed for " + entry.getName(), e);
                }
            });
        }
        return specs;
    }

    private static MethodSpec syntheticSpec(String descriptor) {
        org.objectweb.asm.Type[] params = org.objectweb.asm.Type.getArgumentTypes(descriptor);
        java.util.List<String> requires = new java.util.ArrayList<>();
        for (int i = 0; i < params.length; i++) {
            if (params[i].getSort() == org.objectweb.asm.Type.OBJECT
                    || params[i].getSort() == org.objectweb.asm.Type.ARRAY) {
                requires.add("p" + i + " != null");
            }
        }
        org.objectweb.asm.Type ret = org.objectweb.asm.Type.getReturnType(descriptor);
        java.util.List<String> ensures = new java.util.ArrayList<>();
        if (ret.getSort() == org.objectweb.asm.Type.OBJECT
                || ret.getSort() == org.objectweb.asm.Type.ARRAY) {
            ensures.add("\\result != null");
        }
        return new MethodSpec(requires, ensures, List.of("\\nothing"), List.of(),
                List.of(), "1.0");
    }

    private static boolean specEquals(MethodSpec a, MethodSpec b) {
        return a.requires().equals(b.requires())
                && a.ensures().equals(b.ensures())
                && a.assignable().equals(b.assignable())
                && a.loopInvariant().equals(b.loopInvariant());
    }

    private static void assertReasonableMetrics(ValidationReport report) {
        assertTrue(report.methodCount() > 0, "should have found methods");

        // Plan §2A.2 success criterion: ≥95% roundtrip fidelity on a real OSS
        // library. The sub-100% gap on real JARs is a known-limit finding — see
        // `journal/rq2_validation_metrics.txt` for the reading and the
        // accompanying note for the suspected causes (class-file extras like
        // synthetic accessors that the reader filters out, multi-release JAR
        // duplicates, etc.).
        double fidelity = (double) report.matched() / report.methodCount();
        assertTrue(fidelity >= 0.95,
                String.format("roundtrip fidelity %.1f%% below 95%% threshold (%d / %d)",
                        100 * fidelity, report.matched(), report.methodCount()));

        // For matched methods, equality must be exact.
        assertEquals(0, report.mismatches(),
                "every successfully-read spec must equal the spec written");

        double overheadFraction = (double) (report.embeddedBytes() - report.originalBytes()) / report.originalBytes();
        assertTrue(overheadFraction < 1.0,
                "byte overhead unexpectedly large: " + (int) (100 * overheadFraction) + "%");
    }

    private static void appendMetrics(ValidationReport report) {
        Path metricsFile = Paths.get("journal", "rq2_validation_metrics.txt");
        try {
            Files.createDirectories(metricsFile.getParent());
            String line = String.format(
                    "%s | methods=%d matched=%d mismatches=%d originalBytes=%d embeddedBytes=%d overhead=%.2f%% embedThroughput=%.0f m/s readThroughput=%.0f m/s%n",
                    report.label(),
                    report.methodCount(), report.matched(), report.mismatches(),
                    report.originalBytes(), report.embeddedBytes(),
                    100.0 * (report.embeddedBytes() - report.originalBytes()) / report.originalBytes(),
                    report.methodCount() / (report.embedNanos() / 1e9),
                    report.matched() / (report.readNanos() / 1e9));
            Files.writeString(metricsFile, line,
                    java.nio.file.StandardOpenOption.CREATE,
                    java.nio.file.StandardOpenOption.APPEND);
        } catch (IOException ignored) {
            // metrics output is best-effort; assertions above carry the test's verdict
        }
    }

    private record ValidationReport(
            String label,
            int methodCount,
            int matched,
            int mismatches,
            long originalBytes,
            long embeddedBytes,
            long embedNanos,
            long readNanos) {
    }
}
