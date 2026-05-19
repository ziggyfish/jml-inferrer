package com.jml.spec.read;

import com.jml.spec.Kind;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.SignalsClause;
import com.jml.spec.SpecCodec;
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
 * Reads embedded JML specifications from compiled class files via ASM.
 *
 * <p>Supports both spec-format v1 (the legacy {@code @JmlSpec}
 * repeatable annotation with per-clause metadata, optionally wrapped in
 * the {@code @JmlSpecs(value=...)} container) and spec-format v2 (a
 * single {@code @JmlSpecs} annotation per method whose members are the
 * clause arrays). Strings are decoded via {@link SpecCodec} when read
 * from v2 to reverse the writer's token compression. For v2, the
 * {@code assignable} member is implicitly {@code \nothing} when absent,
 * matching the writer's default-omission convention.</p>
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
                    final List<String> v2Requires = new ArrayList<>();
                    final List<String> v2Ensures = new ArrayList<>();
                    final List<String> v2Assignable = new ArrayList<>();
                    final List<String> v2LoopInvariant = new ArrayList<>();
                    final List<SignalsClause> v2Signals = new ArrayList<>();
                    String v2Version = null;
                    boolean v2Seen = false;

                    final List<RawClause> v1Clauses = new ArrayList<>();
                    String v1Version = "1.0";

                    @Override
                    public AnnotationVisitor visitAnnotation(String desc, boolean visible) {
                        if (JMLSPECS_DESC.equals(desc)) {
                            v2Seen = true;
                            return new AnnotationVisitor(Opcodes.ASM9) {
                                @Override
                                public AnnotationVisitor visitArray(String n) {
                                    // v1 legacy: @JmlSpecs(value=@JmlSpec[]) -> nested annotation array
                                    if ("value".equals(n)) {
                                        return new AnnotationVisitor(Opcodes.ASM9) {
                                            @Override
                                            public AnnotationVisitor visitAnnotation(String inner, String innerDesc) {
                                                return v1InnerVisitor();
                                            }
                                        };
                                    }
                                    // v2: string arrays per clause kind
                                    return new AnnotationVisitor(Opcodes.ASM9) {
                                        @Override
                                        public void visit(String dummy, Object value) {
                                            if (!(value instanceof String s)) return;
                                            String decoded = SpecCodec.decode(s);
                                            switch (n) {
                                                case "requires"      -> v2Requires.add(decoded);
                                                case "ensures"       -> v2Ensures.add(decoded);
                                                case "assignable"    -> v2Assignable.add(decoded);
                                                case "loopInvariant" -> v2LoopInvariant.add(decoded);
                                                case "signals" -> {
                                                    int sep = decoded.indexOf('|');
                                                    if (sep > 0) {
                                                        v2Signals.add(new SignalsClause(
                                                                decoded.substring(0, sep),
                                                                decoded.substring(sep + 1)));
                                                    }
                                                }
                                                default -> { /* unknown member -> ignore */ }
                                            }
                                        }
                                    };
                                }

                                @Override
                                public void visit(String n, Object v) {
                                    if ("version".equals(n)) v2Version = (String) v;
                                }
                            };
                        }
                        if (JMLSPEC_DESC.equals(desc)) return v1InnerVisitor();
                        return null;
                    }

                    private AnnotationVisitor v1InnerVisitor() {
                        RawClause raw = new RawClause();
                        v1Clauses.add(raw);
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
                        // Treat any presence of @JmlSpecs as a v2 spec, even
                        // if all members were dropped to defaults (the writer
                        // omits the assignable=[\nothing] member, so an
                        // otherwise pure method emits an empty @JmlSpecs).
                        if (v2Seen) {
                            // v2: apply the default-assignable convention.
                            List<String> assignable = v2Assignable.isEmpty()
                                    ? List.of("\\nothing")
                                    : v2Assignable;
                            String version = v2Version != null ? v2Version : "2";
                            result.put(new MethodKey(internalName, name, descriptor),
                                    new MethodSpec(v2Requires, v2Ensures, assignable,
                                            v2LoopInvariant, v2Signals, version));
                            return;
                        }
                        if (v1Clauses.isEmpty()) return;
                        // v1: sort by order and demultiplex by kind.
                        v1Clauses.sort(Comparator.comparingInt(c -> c.order));
                        List<String> requires = new ArrayList<>();
                        List<String> ensures = new ArrayList<>();
                        List<String> assignable = new ArrayList<>();
                        List<String> loopInvariant = new ArrayList<>();
                        List<SignalsClause> signals = new ArrayList<>();
                        for (RawClause c : v1Clauses) {
                            if (c.kind == null || c.text == null) continue;
                            if (!"1.0".equals(c.version)) v1Version = c.version;
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
                                new MethodSpec(requires, ensures, assignable, loopInvariant, signals, v1Version));
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
