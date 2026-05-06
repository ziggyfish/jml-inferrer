package com.jml.spec;

import com.jml.spec.read.AsmJmlSpecReader;
import com.jml.spec.write.AsmJmlSpecWriter;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

class AsmRoundtripTest {

    @Test
    @DisplayName("Embedded @JmlSpec annotations are read back identically (single clause)")
    void singleClauseRoundtrip() {
        byte[] cls = makeMinimalClass("test/Sample", "compute", "(I)I");
        MethodSpec spec = new MethodSpec(
                List.of("p >= 0"),
                List.of("\\result == p"),
                List.of("\\nothing"),
                List.of(),
                List.of(),
                "1.0");

        byte[] embedded = new AsmJmlSpecWriter().embedClass(cls, Map.of("compute(I)I", spec));
        Map<MethodKey, MethodSpec> read = readBytes(embedded, "test/Sample");

        assertEquals(1, read.size(), "exactly one method should have specs: " + read);
        MethodSpec out = read.get(new MethodKey("test/Sample", "compute", "(I)I"));
        assertNotNull(out, "spec should be readable for compute(I)I; got keys " + read.keySet());
        assertEquals(List.of("p >= 0"), out.requires());
        assertEquals(List.of("\\result == p"), out.ensures());
        assertEquals(List.of("\\nothing"), out.assignable());
    }

    @Test
    @DisplayName("Multiple requires clauses preserve order")
    void requiresOrderPreserved() {
        byte[] cls = makeMinimalClass("test/Ordered", "lookup", "(I)I");
        MethodSpec spec = new MethodSpec(
                List.of("this.data != null", "i >= 0", "i < this.data.length"),
                List.of("\\result == this.data[i]"),
                List.of("\\nothing"),
                List.of(),
                List.of(),
                "1.0");

        byte[] embedded = new AsmJmlSpecWriter().embedClass(cls, Map.of("lookup(I)I", spec));
        Map<MethodKey, MethodSpec> read = readBytes(embedded, "test/Ordered");

        MethodSpec out = read.get(new MethodKey("test/Ordered", "lookup", "(I)I"));
        assertNotNull(out);
        assertEquals(List.of("this.data != null", "i >= 0", "i < this.data.length"), out.requires(),
                "well-definedness order must be preserved");
    }

    @Test
    @DisplayName("Methods without specs remain unchanged")
    void methodsWithoutSpecsUnchanged() {
        byte[] cls = makeMinimalClass("test/Empty", "compute", "(I)I");
        byte[] embedded = new AsmJmlSpecWriter().embedClass(cls, Map.of());
        Map<MethodKey, MethodSpec> read = readBytes(embedded, "test/Empty");
        assertTrue(read.isEmpty(), "no specs should be present: " + read);
    }

    @Test
    @DisplayName("Loop invariant clause survives roundtrip")
    void loopInvariantRoundtrip() {
        byte[] cls = makeMinimalClass("test/Loopy", "sum", "(I)I");
        MethodSpec spec = new MethodSpec(
                List.of(),
                List.of(),
                List.of(),
                List.of("0 <= i && i <= n", "s == (\\sum int k; 0 <= k && k < i; arr[k])"),
                List.of(),
                "1.0");

        byte[] embedded = new AsmJmlSpecWriter().embedClass(cls, Map.of("sum(I)I", spec));
        MethodSpec out = readBytes(embedded, "test/Loopy")
                .get(new MethodKey("test/Loopy", "sum", "(I)I"));
        assertEquals(List.of("0 <= i && i <= n", "s == (\\sum int k; 0 <= k && k < i; arr[k])"),
                out.loopInvariant());
    }

    @Test
    @DisplayName("Reader returns Optional.empty for methods without specs")
    void readerOptionalEmpty() {
        byte[] cls = makeMinimalClass("test/Plain", "compute", "(I)I");
        Map<MethodKey, MethodSpec> read = readBytes(cls, "test/Plain");
        assertTrue(read.isEmpty());
    }

    @Test
    @DisplayName("Sidecar JAR contains JML stub files keyed by class")
    void sidecarStubGeneration() throws java.io.IOException {
        byte[] cls = makeMinimalClass("test/Sidecar", "compute", "(I)I");
        java.nio.file.Path inputJar = java.nio.file.Files.createTempFile("sidecar-input-", ".jar");
        java.nio.file.Path sidecarJar = java.nio.file.Files.createTempFile("sidecar-", ".jar");
        try {
            try (var jos = new java.util.jar.JarOutputStream(java.nio.file.Files.newOutputStream(inputJar))) {
                jos.putNextEntry(new java.util.jar.JarEntry("test/Sidecar.class"));
                jos.write(cls);
                jos.closeEntry();
            }
            MethodSpec spec = new MethodSpec(
                    List.of("p >= 0"),
                    List.of("\\result == p + 1"),
                    List.of("\\nothing"),
                    List.of(),
                    List.of(),
                    "1.0");
            new com.jml.spec.write.AsmJmlSpecWriter().writeSidecar(
                    inputJar, sidecarJar,
                    Map.of(new MethodKey("test/Sidecar", "compute", "(I)I"), spec));

            try (var jf = new java.util.jar.JarFile(sidecarJar.toFile())) {
                java.util.jar.JarEntry entry = jf.getJarEntry("test/Sidecar.jmlspec");
                assertNotNull(entry, "sidecar should contain test/Sidecar.jmlspec");
                String content = new String(jf.getInputStream(entry).readAllBytes(),
                        java.nio.charset.StandardCharsets.UTF_8);
                assertTrue(content.contains("//@ requires p >= 0"), content);
                assertTrue(content.contains("//@ ensures \\result == p + 1"), content);
                assertTrue(content.contains("//@ assignable \\nothing"), content);
                assertTrue(content.contains("public native int compute(int p0);"), content);
            }
            try (var jf = new java.util.jar.JarFile(sidecarJar.toFile())) {
                java.util.jar.Manifest m = jf.getManifest();
                assertNotNull(m);
                assertEquals("1.0", m.getMainAttributes().getValue("jml-version"));
                assertNotNull(m.getMainAttributes().getValue("jml-source-sha256"));
            }
        } finally {
            java.nio.file.Files.deleteIfExists(inputJar);
            java.nio.file.Files.deleteIfExists(sidecarJar);
        }
    }

    private static Map<MethodKey, MethodSpec> readBytes(byte[] cls, String internalName) {
        try (var stream = new java.io.ByteArrayInputStream(cls)) {
            // Use the package-private static via a public path: build a synthetic ClassLoader
            // that serves the bytes for `internalName + ".class"`, then call readAll(Class).
            // Simpler: use the Jar variant via a temp file.
            java.nio.file.Path tmp = java.nio.file.Files.createTempFile("asm-roundtrip-", ".jar");
            try (var jos = new java.util.jar.JarOutputStream(java.nio.file.Files.newOutputStream(tmp))) {
                jos.putNextEntry(new java.util.jar.JarEntry(internalName + ".class"));
                jos.write(cls);
                jos.closeEntry();
            }
            try {
                return new AsmJmlSpecReader().readJar(tmp);
            } finally {
                java.nio.file.Files.deleteIfExists(tmp);
            }
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
    }

    /** Build a minimal class with one public method whose body is `return 0`. */
    private static byte[] makeMinimalClass(String internalName, String methodName, String descriptor) {
        ClassWriter cw = new ClassWriter(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES);
        cw.visit(Opcodes.V21, Opcodes.ACC_PUBLIC, internalName, null, "java/lang/Object", null);

        MethodVisitor init = cw.visitMethod(Opcodes.ACC_PUBLIC, "<init>", "()V", null, null);
        init.visitCode();
        init.visitVarInsn(Opcodes.ALOAD, 0);
        init.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/Object", "<init>", "()V", false);
        init.visitInsn(Opcodes.RETURN);
        init.visitMaxs(0, 0);
        init.visitEnd();

        MethodVisitor mv = cw.visitMethod(Opcodes.ACC_PUBLIC, methodName, descriptor, null, null);
        mv.visitCode();
        mv.visitInsn(Opcodes.ICONST_0);
        mv.visitInsn(Opcodes.IRETURN);
        mv.visitMaxs(0, 0);
        mv.visitEnd();

        cw.visitEnd();
        return cw.toByteArray();
    }
}
