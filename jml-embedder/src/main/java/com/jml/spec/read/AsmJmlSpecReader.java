package com.jml.spec.read;

import com.jml.spec.Kind;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.SignalsClause;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;

import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * Reads {@code @JmlSpec} annotations from compiled class files via ASM.
 *
 * <p>Annotations may live in the {@code @JmlSpecs} container (the standard form
 * the {@link com.jml.spec.write.AsmJmlSpecWriter} emits) or as repeated standalone
 * annotations (Java's repeatable-annotation legacy shape). Both are supported.
 * Per-kind clauses are sorted by the {@code order} element on read.</p>
 */
public class AsmJmlSpecReader implements JmlSpecReader {

    private static final String JMLSPEC_DESC = "Lcom/jml/spec/JmlSpec;";
    private static final String JMLSPECS_DESC = "Lcom/jml/spec/JmlSpecs;";

    @Override
    public Optional<MethodSpec> readForMethod(Class<?> clazz, String methodName, Class<?>... paramTypes) {
        try {
            Method m = clazz.getDeclaredMethod(methodName, paramTypes);
            String descriptor = Type.getMethodDescriptor(m);
            String internal = clazz.getName().replace('.', '/');
            try (InputStream is = clazz.getClassLoader().getResourceAsStream(internal + ".class")) {
                if (is == null) return Optional.empty();
                Map<MethodKey, MethodSpec> all = readClassFile(is.readAllBytes(), internal);
                return Optional.ofNullable(all.get(new MethodKey(internal, methodName, descriptor)));
            }
        } catch (NoSuchMethodException | IOException e) {
            return Optional.empty();
        }
    }

    @Override
    public Map<MethodKey, MethodSpec> readAll(Class<?> clazz) {
        String internal = clazz.getName().replace('.', '/');
        try (InputStream is = clazz.getClassLoader().getResourceAsStream(internal + ".class")) {
            if (is == null) return Map.of();
            return readClassFile(is.readAllBytes(), internal);
        } catch (IOException e) {
            return Map.of();
        }
    }

    @Override
    public Map<MethodKey, MethodSpec> readJar(Path jar) throws IOException {
        Map<MethodKey, MethodSpec> all = new HashMap<>();
        try (JarFile jf = new JarFile(jar.toFile())) {
            jf.stream().forEach(entry -> {
                if (!entry.getName().endsWith(".class")) return;
                String internal = entry.getName().substring(0, entry.getName().length() - ".class".length());
                try (InputStream is = jf.getInputStream(entry)) {
                    all.putAll(readClassFile(is.readAllBytes(), internal));
                } catch (IOException e) {
                    throw new RuntimeException("Failed reading entry " + entry.getName(), e);
                }
            });
        }
        return all;
    }

    private static Map<MethodKey, MethodSpec> readClassFile(byte[] bytes, String internalName) {
        Map<MethodKey, MethodSpec> result = new HashMap<>();
        ClassReader reader = new ClassReader(bytes);
        reader.accept(new ClassVisitor(Opcodes.ASM9) {
            @Override
            public MethodVisitor visitMethod(int access, String name, String descriptor, String signature, String[] exceptions) {
                return new MethodVisitor(Opcodes.ASM9) {
                    final List<RawClause> clauses = new ArrayList<>();
                    String version = "1.0";

                    @Override
                    public AnnotationVisitor visitAnnotation(String desc, boolean visible) {
                        if (JMLSPECS_DESC.equals(desc)) {
                            return new AnnotationVisitor(Opcodes.ASM9) {
                                @Override
                                public AnnotationVisitor visitArray(String n) {
                                    return new AnnotationVisitor(Opcodes.ASM9) {
                                        @Override
                                        public AnnotationVisitor visitAnnotation(String inner, String innerDesc) {
                                            return innerVisitor();
                                        }
                                    };
                                }
                            };
                        }
                        if (JMLSPEC_DESC.equals(desc)) return innerVisitor();
                        return null;
                    }

                    private AnnotationVisitor innerVisitor() {
                        RawClause raw = new RawClause();
                        clauses.add(raw);
                        return new AnnotationVisitor(Opcodes.ASM9) {
                            @Override
                            public void visit(String n, Object v) {
                                if ("text".equals(n)) raw.text = (String) v;
                                else if ("order".equals(n)) raw.order = (Integer) v;
                                else if ("version".equals(n)) raw.version = (String) v;
                                else if ("targetSignature".equals(n)) raw.targetSignature = (String) v;
                            }

                            @Override
                            public void visitEnum(String n, String d, String value) {
                                if ("kind".equals(n)) raw.kind = Kind.valueOf(value);
                            }
                        };
                    }

                    @Override
                    public void visitEnd() {
                        if (clauses.isEmpty()) return;
                        clauses.sort(Comparator.comparingInt(c -> c.order));
                        List<String> requires = new ArrayList<>();
                        List<String> ensures = new ArrayList<>();
                        List<String> assignable = new ArrayList<>();
                        List<String> loopInvariant = new ArrayList<>();
                        List<SignalsClause> signals = new ArrayList<>();
                        for (RawClause c : clauses) {
                            if (c.kind == null || c.text == null) continue;
                            if (!"1.0".equals(c.version)) version = c.version;
                            switch (c.kind) {
                                case REQUIRES -> requires.add(c.text);
                                case ENSURES -> ensures.add(c.text);
                                case ASSIGNABLE -> assignable.add(c.text);
                                case LOOP_INVARIANT -> loopInvariant.add(c.text);
                                case SIGNALS -> {
                                    int sep = c.text.indexOf('|');
                                    if (sep > 0) signals.add(new SignalsClause(c.text.substring(0, sep), c.text.substring(sep + 1)));
                                }
                                default -> { /* unknown kinds skipped */ }
                            }
                        }
                        result.put(new MethodKey(internalName, name, descriptor),
                                new MethodSpec(requires, ensures, assignable, loopInvariant, signals, version));
                    }
                };
            }
        }, ClassReader.SKIP_CODE | ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
        return result;
    }

    private static class RawClause {
        Kind kind;
        String text;
        int order;
        String version = "1.0";
        String targetSignature = "";
    }
}
