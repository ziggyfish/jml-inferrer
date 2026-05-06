package com.jml.spec.write;

import com.jml.spec.JmlSpec;
import com.jml.spec.Kind;
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
 * Writes {@link JmlSpec} annotations into compiled class files via ASM.
 *
 * <p>One {@code @JmlSpec} annotation is emitted per clause; clause kinds are taken
 * from {@link Kind}. The annotations are repeated via the {@code @JmlSpecs} container
 * so {@link AnnotationVisitor#visitArray} carries them as a single array attribute.
 * Order within a kind is preserved through the {@code order} element of each
 * annotation; the reader is responsible for sorting on read.
 */
public class AsmJmlSpecWriter implements JmlSpecWriter {

    private static final Logger logger = LoggerFactory.getLogger(AsmJmlSpecWriter.class);
    private static final String JMLSPEC_DESC = "Lcom/jml/spec/JmlSpec;";
    private static final String JMLSPECS_DESC = "Lcom/jml/spec/JmlSpecs;";
    private static final String KIND_DESC = "Lcom/jml/spec/Kind;";

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

    /** Emit the @JmlSpecs container with one @JmlSpec inner per clause. */
    private static void emitJmlAnnotations(MethodVisitor mv, MethodSpec spec) {
        List<EmissionRecord> records = collect(spec);
        if (records.isEmpty()) return;
        AnnotationVisitor container = mv.visitAnnotation(JMLSPECS_DESC, true);
        AnnotationVisitor array = container.visitArray("value");
        for (EmissionRecord r : records) {
            AnnotationVisitor inner = array.visitAnnotation(null, JMLSPEC_DESC);
            inner.visitEnum("kind", KIND_DESC, r.kind().name());
            inner.visit("text", r.text());
            if (r.order() != 0) inner.visit("order", r.order());
            if (!"1.0".equals(spec.version())) inner.visit("version", spec.version());
            inner.visitEnd();
        }
        array.visitEnd();
        container.visitEnd();
    }

    private static List<EmissionRecord> collect(MethodSpec spec) {
        List<EmissionRecord> out = new ArrayList<>();
        int order = 0;
        if (spec.requires() != null) {
            for (String r : spec.requires()) out.add(new EmissionRecord(Kind.REQUIRES, r, ++order));
        }
        order = 0;
        if (spec.ensures() != null) {
            for (String e : spec.ensures()) out.add(new EmissionRecord(Kind.ENSURES, e, ++order));
        }
        order = 0;
        if (spec.assignable() != null) {
            for (String a : spec.assignable()) out.add(new EmissionRecord(Kind.ASSIGNABLE, a, ++order));
        }
        order = 0;
        if (spec.loopInvariant() != null) {
            for (String l : spec.loopInvariant()) out.add(new EmissionRecord(Kind.LOOP_INVARIANT, l, ++order));
        }
        if (spec.signals() != null) {
            for (SignalsClause s : spec.signals()) {
                out.add(new EmissionRecord(Kind.SIGNALS, s.exceptionType() + "|" + s.condition(), 0));
            }
        }
        return out;
    }

    private record EmissionRecord(Kind kind, String text, int order) {
    }

    @SuppressWarnings("unused")
    private static String descriptorOf(Class<?>... params) {
        StringBuilder sb = new StringBuilder("(");
        for (Class<?> p : params) sb.append(Type.getDescriptor(p));
        sb.append(")");
        return sb.toString();
    }
}
