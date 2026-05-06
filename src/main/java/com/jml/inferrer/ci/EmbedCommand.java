package com.jml.inferrer.ci;

import com.jml.inferrer.analysis.MethodSpecificationInferrer;
import com.jml.inferrer.embedder.InferrerSpecConverter;
import com.jml.inferrer.model.MethodSpecification;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.write.AsmJmlSpecWriter;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.Opcodes;

import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarFile;
import java.util.stream.Stream;

/**
 * {@code jml-ci embed} — run the inferrer over a source tree and embed
 * the resulting JML specifications into a JAR via {@code @JmlSpec}
 * annotations.
 *
 * <p>This is the deployment-time complement to {@code jml-ci infer}.
 * Whereas {@code infer} writes JML annotations into source files in
 * place, {@code embed} writes them into the compiled JAR so downstream
 * consumers (test generators, IDEs, runtime checkers) can read them
 * without source access.</p>
 */
class EmbedCommand {

    int execute(Map<String, String> opts, PrintStream out) throws Exception {
        String sourceRoot = opts.getOrDefault("source", "src/main/java");
        String inputJar = required(opts, "jar");
        String outputJar = required(opts, "output");

        Path sourcePath = Paths.get(sourceRoot);
        Path jarPath = Paths.get(inputJar);
        Path outPath = Paths.get(outputJar);

        if (!Files.isDirectory(sourcePath)) {
            out.println("[jml-ci embed] source path is not a directory: " + sourcePath);
            return 1;
        }
        if (!Files.exists(jarPath)) {
            out.println("[jml-ci embed] input JAR not found: " + jarPath);
            return 1;
        }

        Map<String, Set<String>> bytecodeMethods = readBytecodeMethods(jarPath);
        Map<MethodKey, MethodSpec> specs = inferSourceTree(sourcePath, bytecodeMethods);

        if (specs.isEmpty()) {
            out.println("[jml-ci embed] no specs to embed (no source matched the JAR's classes)");
            return 0;
        }

        new AsmJmlSpecWriter().embedJar(jarPath, outPath, specs);

        out.printf("[jml-ci embed] %d methods embedded into %s%n", specs.size(), outPath);
        return 0;
    }

    private static String required(Map<String, String> opts, String key) {
        String v = opts.get(key);
        if (v == null || v.isBlank()) {
            throw new IllegalArgumentException("--" + key + " is required");
        }
        return v;
    }

    private static Map<MethodKey, MethodSpec> inferSourceTree(Path sourceRoot,
                                                               Map<String, Set<String>> bytecodeMethods) throws Exception {
        Map<MethodKey, MethodSpec> specs = new HashMap<>();
        MethodSpecificationInferrer inferrer = new MethodSpecificationInferrer();
        try (Stream<Path> files = Files.walk(sourceRoot)) {
            files.filter(p -> p.toString().endsWith(".java")).forEach(p -> {
                try {
                    CompilationUnit cu = new JavaParser().parse(Files.readString(p))
                            .getResult().orElse(null);
                    if (cu == null) return;
                    for (ClassOrInterfaceDeclaration clazz : cu.findAll(ClassOrInterfaceDeclaration.class)) {
                        String pkg = cu.getPackageDeclaration().map(d -> d.getNameAsString()).orElse("");
                        String internal = (pkg.isEmpty() ? clazz.getNameAsString()
                                : pkg.replace('.', '/') + "/" + clazz.getNameAsString());
                        Set<String> bytecodeForClass = bytecodeMethods.getOrDefault(internal, Set.of());
                        for (MethodDeclaration method : clazz.getMethods()) {
                            MethodSpecification spec = inferrer.inferSpecification(method);
                            if (isEmpty(spec)) continue;
                            String descriptor = findDescriptor(method.getNameAsString(), bytecodeForClass);
                            if (descriptor == null) continue;
                            specs.put(new MethodKey(internal, method.getNameAsString(), descriptor),
                                    InferrerSpecConverter.toEmbeddable(spec));
                        }
                    }
                } catch (Exception e) {
                    // log and continue — fail-open per design doc
                    System.err.println("[jml-ci embed] skipping " + p + ": " + e.getMessage());
                }
            });
        }
        return specs;
    }

    private static boolean isEmpty(MethodSpecification spec) {
        return spec.getPreconditions().isEmpty() && spec.getPostconditions().isEmpty()
                && spec.getAssignableClauses().isEmpty() && spec.getLoopInvariants().isEmpty();
    }

    private static String findDescriptor(String name, Set<String> entries) {
        for (String e : entries) {
            int sep = e.indexOf('(');
            if (sep > 0 && e.substring(0, sep).equals(name)) return e.substring(sep);
        }
        return null;
    }

    private static Map<String, Set<String>> readBytecodeMethods(Path jar) throws Exception {
        Map<String, Set<String>> result = new HashMap<>();
        try (JarFile jf = new JarFile(jar.toFile())) {
            jf.stream().forEach(entry -> {
                if (!entry.getName().endsWith(".class")) return;
                String internal = entry.getName().substring(0, entry.getName().length() - ".class".length());
                Set<String> methods = new HashSet<>();
                try {
                    new ClassReader(jf.getInputStream(entry).readAllBytes()).accept(new ClassVisitor(Opcodes.ASM9) {
                        @Override
                        public org.objectweb.asm.MethodVisitor visitMethod(int access, String name, String descriptor,
                                String signature, String[] exceptions) {
                            methods.add(name + descriptor);
                            return null;
                        }
                    }, ClassReader.SKIP_CODE | ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
                } catch (Exception ex) {
                    // Skip unreadable entries — fail-open
                }
                result.put(internal, methods);
            });
        }
        return result;
    }
}
