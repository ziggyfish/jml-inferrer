package com.jml.spec.write;

import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.SignalsClause;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarOutputStream;

/**
 * Writes {@link com.jml.spec.JmlSpecs} annotations into compiled class
 * files via ASM (spec-format v2).
 *
 * <p>One {@code @JmlSpecs} annotation per method carries every clause as a
 * {@code String[]} member. Strings are token-encoded via
 * {@link com.jml.spec.SpecCodec} before being written, and the default
 * {@code assignable \nothing} clause is omitted (absence means
 * {@code \nothing} in v2). Together these reduce the bytecode-size
 * overhead of embedded specifications by roughly a third compared with
 * the v1 per-clause repeatable annotation format.</p>
 */
public class AsmJmlSpecWriter implements JmlSpecWriter {

    private static final Logger logger = LoggerFactory.getLogger(AsmJmlSpecWriter.class);
    private static final String JMLSPECS_DESC = "Lcom/jml/spec/JmlSpecs;";

    @Override
    public void embedJar(Path inputJar, Path outputJar, Map<MethodKey, MethodSpec> specs) throws IOException {
        Map<String, Map<MethodKey, MethodSpec>> byClass = groupByClass(specs);
        try (JarFile in = new JarFile(inputJar.toFile());
             JarOutputStream out = new JarOutputStream(Files.newOutputStream(outputJar))) {
            in.stream().forEach(entry -> {
                try {
                    out.putNextEntry(new JarEntry(entry.getName()));
                    if (entry.getName().endsWith(".class")) {
                        byte[] original = readEntry(in, entry);
                        String className = entry.getName().substring(0, entry.getName().length() - ".class".length());
                        Map<MethodKey, MethodSpec> classSpecs = byClass.get(className);
                        if (classSpecs == null || classSpecs.isEmpty()) {
                            out.write(original);
                        } else {
                            Map<String, MethodSpec> byMethod = new HashMap<>();
                            for (Map.Entry<MethodKey, MethodSpec> ms : classSpecs.entrySet()) {
                                byMethod.put(ms.getKey().methodName() + ms.getKey().descriptor(), ms.getValue());
                            }
                            out.write(embedClass(original, byMethod));
                        }
                    } else {
                        try (InputStream is = in.getInputStream(entry)) {
                            transfer(is, out);
                        }
                    }
                    out.closeEntry();
                } catch (IOException e) {
                    throw new RuntimeException("Failed embedding entry " + entry.getName(), e);
                }
            });
        }
    }

    @Override
    public byte[] embedClass(byte[] inputClass, Map<String, MethodSpec> specs) {
        ClassReader reader = new ClassReader(inputClass);
        ClassWriter writer = new ClassWriter(reader, ClassWriter.COMPUTE_MAXS);
        ClassVisitor visitor = new SpecEmittingClassVisitor(writer, specs);
        reader.accept(visitor, 0);
        return writer.toByteArray();
    }

    @Override
    public void writeSidecar(Path inputJar, Path sidecarJar, Map<MethodKey, MethodSpec> specs) throws IOException {
        // Sidecar format per `journal/rq2_embedding_design.md` §7. The sidecar
        // is a JAR containing one .jmlspec text file per class in the source
        // JAR, in JML stub-file format. The MANIFEST records the source JAR's
        // SHA-256 so consumers can detect drift.
        Map<String, Map<MethodKey, MethodSpec>> byClass = groupByClass(specs);
        java.security.MessageDigest sha;
        try {
            sha = java.security.MessageDigest.getInstance("SHA-256");
        } catch (java.security.NoSuchAlgorithmException e) {
            throw new IOException("SHA-256 unavailable", e);
        }
        byte[] sourceBytes = Files.readAllBytes(inputJar);
        sha.update(sourceBytes);
        String sourceSha = java.util.HexFormat.of().formatHex(sha.digest());

        java.util.jar.Manifest manifest = new java.util.jar.Manifest();
        manifest.getMainAttributes().putValue("Manifest-Version", "1.0");
        manifest.getMainAttributes().putValue("jml-version", "1.0");
        manifest.getMainAttributes().putValue("jml-source-jar", inputJar.getFileName().toString());
        manifest.getMainAttributes().putValue("jml-source-sha256", sourceSha);

        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(sidecarJar), manifest)) {
            for (Map.Entry<String, Map<MethodKey, MethodSpec>> classEntry : byClass.entrySet()) {
                String stubPath = classEntry.getKey() + ".jmlspec";
                out.putNextEntry(new JarEntry(stubPath));
                out.write(renderStub(classEntry.getKey(), classEntry.getValue()).getBytes(java.nio.charset.StandardCharsets.UTF_8));
                out.closeEntry();
            }
        }
    }

    private static String renderStub(String classInternalName, Map<MethodKey, MethodSpec> classSpecs) {
        StringBuilder sb = new StringBuilder();
        String dotted = classInternalName.replace('/', '.');
        int lastDot = dotted.lastIndexOf('.');
        if (lastDot > 0) {
            sb.append("package ").append(dotted, 0, lastDot).append(";\n\n");
        }
        sb.append("public class ").append(dotted.substring(lastDot + 1)).append(" {\n");
        for (Map.Entry<MethodKey, MethodSpec> e : classSpecs.entrySet()) {
            MethodKey k = e.getKey();
            MethodSpec spec = e.getValue();
            for (String r : spec.requires()) sb.append("    //@ requires ").append(r).append(";\n");
            for (String en : spec.ensures()) sb.append("    //@ ensures ").append(en).append(";\n");
            for (String a : spec.assignable()) sb.append("    //@ assignable ").append(a).append(";\n");
            for (String li : spec.loopInvariant()) sb.append("    //@ loop_invariant ").append(li).append(";\n");
            for (SignalsClause s : spec.signals()) {
                sb.append("    //@ signals (").append(s.exceptionType()).append(") ").append(s.condition()).append(";\n");
            }
            sb.append("    public native ");
            sb.append(returnTypeOf(k.descriptor())).append(' ').append(k.methodName()).append('(');
            sb.append(paramListOf(k.descriptor())).append(");\n\n");
        }
        sb.append("}\n");
        return sb.toString();
    }

    private static String returnTypeOf(String descriptor) {
        Type ret = Type.getReturnType(descriptor);
        return readableType(ret);
    }

    private static String paramListOf(String descriptor) {
        Type[] args = Type.getArgumentTypes(descriptor);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < args.length; i++) {
            if (i > 0) sb.append(", ");
            sb.append(readableType(args[i])).append(" p").append(i);
        }
        return sb.toString();
    }

    private static String readableType(Type t) {
        if (t.getSort() == Type.OBJECT) return t.getClassName();
        if (t.getSort() == Type.ARRAY) return readableType(t.getElementType()) + "[]".repeat(t.getDimensions());
        return t.getClassName();
    }

    private static Map<String, Map<MethodKey, MethodSpec>> groupByClass(Map<MethodKey, MethodSpec> specs) {
        Map<String, Map<MethodKey, MethodSpec>> grouped = new HashMap<>();
        for (Map.Entry<MethodKey, MethodSpec> e : specs.entrySet()) {
            grouped.computeIfAbsent(e.getKey().className(), k -> new HashMap<>()).put(e.getKey(), e.getValue());
        }
        return grouped;
    }

    private static byte[] readEntry(JarFile jar, JarEntry entry) throws IOException {
        try (InputStream is = jar.getInputStream(entry)) {
            return is.readAllBytes();
        }
    }

    private static void transfer(InputStream in, OutputStream out) throws IOException {
        byte[] buf = new byte[8192];
        int n;
        while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
    }

    /** ClassVisitor that intercepts each method visit and emits @JmlSpec annotations. */
    private static class SpecEmittingClassVisitor extends ClassVisitor {
        private final Map<String, MethodSpec> specsByMethodAndDesc;

        SpecEmittingClassVisitor(ClassVisitor delegate, Map<String, MethodSpec> specs) {
            super(Opcodes.ASM9, delegate);
            this.specsByMethodAndDesc = specs;
        }

        @Override
        public MethodVisitor visitMethod(int access, String name, String descriptor, String signature, String[] exceptions) {
            MethodVisitor mv = super.visitMethod(access, name, descriptor, signature, exceptions);
            MethodSpec spec = specsByMethodAndDesc.get(name + descriptor);
            if (spec == null) return mv;
            return new SpecEmittingMethodVisitor(mv, spec);
        }
    }

    /** MethodVisitor that emits @JmlSpec annotations once before any other
     * visitX call. Lazy emission is required because ASM's ClassWriter expects
     * annotations to be visited via the MethodVisitor as ASM drives the visit;
     * eager emission from {@code visitMethod} interferes with the ClassWriter's
     * internal state. The emission also fires from {@code visitEnd} so that
     * abstract / interface methods (which never call visitCode or visitParameter)
     * still receive their annotations. */
    private static class SpecEmittingMethodVisitor extends MethodVisitor {
        private final MethodSpec spec;
        private boolean emitted = false;

        SpecEmittingMethodVisitor(MethodVisitor delegate, MethodSpec spec) {
            super(Opcodes.ASM9, delegate);
            this.spec = spec;
        }

        @Override
        public void visitCode() {
            ensureEmitted();
            super.visitCode();
        }

        @Override
        public void visitParameter(String name, int access) {
            ensureEmitted();
            super.visitParameter(name, access);
        }

        @Override
        public AnnotationVisitor visitAnnotationDefault() {
            ensureEmitted();
            return super.visitAnnotationDefault();
        }

        @Override
        public AnnotationVisitor visitAnnotation(String descriptor, boolean visible) {
            ensureEmitted();
            return super.visitAnnotation(descriptor, visible);
        }

        @Override
        public void visitEnd() {
            // Catch abstract / interface methods that never call any other
            // visitX hook before visitEnd.
            ensureEmitted();
            super.visitEnd();
        }

        private void ensureEmitted() {
            if (emitted) return;
            emitted = true;
            emitJmlAnnotations(mv, spec);
        }
    }

    /**
     * Emit a single {@code @JmlSpecs} annotation per method (spec-format v2).
     *
     * <p>One annotation carries all four clause arrays plus packed signals,
     * each member emitted only when its array is non-default. Strings are
     * token-encoded via {@link com.jml.spec.SpecCodec} before being written.
     * The {@code assignable} member is omitted when its only entry is
     * {@code "\\nothing"} (the convention: absence means {@code \nothing}).</p>
     */
    private static void emitJmlAnnotations(MethodVisitor mv, MethodSpec spec) {
        java.util.List<String> requires = nonNull(spec.requires());
        java.util.List<String> ensures = nonNull(spec.ensures());
        java.util.List<String> assignable = nonNull(spec.assignable());
        java.util.List<String> loopInvariant = nonNull(spec.loopInvariant());
        java.util.List<SignalsClause> signals = spec.signals() == null ? java.util.List.of() : spec.signals();
        // Skip if the input spec is entirely empty (no clauses at all,
        // including no assignable). Specs with at least one clause --- even
        // if the only clause is assignable \nothing --- must produce a
        // detectable @JmlSpecs marker so the reader can synthesize the
        // default-assignable convention.
        boolean inputAllEmpty = requires.isEmpty() && ensures.isEmpty()
                && assignable.isEmpty() && loopInvariant.isEmpty() && signals.isEmpty();
        if (inputAllEmpty) return;
        // Drop the default assignable \nothing; absence means \nothing in v2.
        if (assignable.size() == 1 && "\\nothing".equals(assignable.get(0))) {
            assignable = java.util.List.of();
        }
        AnnotationVisitor specs = mv.visitAnnotation(JMLSPECS_DESC, true);
        if (!requires.isEmpty())      writeEncodedArray(specs, "requires", requires);
        if (!ensures.isEmpty())       writeEncodedArray(specs, "ensures", ensures);
        if (!assignable.isEmpty())    writeEncodedArray(specs, "assignable", assignable);
        if (!loopInvariant.isEmpty()) writeEncodedArray(specs, "loopInvariant", loopInvariant);
        if (!signals.isEmpty()) {
            AnnotationVisitor sigArr = specs.visitArray("signals");
            for (SignalsClause s : signals) {
                sigArr.visit(null, com.jml.spec.SpecCodec.encode(
                        s.exceptionType() + "|" + s.condition()));
            }
            sigArr.visitEnd();
        }
        // version="2" is the default in the new annotation; only emit if non-default.
        if (spec.version() != null && !"2".equals(spec.version()) && !"1.0".equals(spec.version())) {
            specs.visit("version", spec.version());
        }
        specs.visitEnd();
    }

    private static void writeEncodedArray(AnnotationVisitor ann, String member, java.util.List<String> items) {
        AnnotationVisitor arr = ann.visitArray(member);
        for (String s : items) arr.visit(null, com.jml.spec.SpecCodec.encode(s));
        arr.visitEnd();
    }

    private static <T> java.util.List<T> nonNull(java.util.List<T> in) {
        return in == null ? java.util.List.of() : in;
    }

    @SuppressWarnings("unused")
    private static String descriptorOf(Class<?>... params) {
        StringBuilder sb = new StringBuilder("(");
        for (Class<?> p : params) sb.append(Type.getDescriptor(p));
        sb.append(")");
        return sb.toString();
    }
}
