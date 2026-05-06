package com.jml.inferrer.embedder;

import com.jml.inferrer.analysis.MethodSpecificationInferrer;
import com.jml.inferrer.model.MethodSpecification;
import com.jml.spec.MethodKey;
import com.jml.spec.MethodSpec;
import com.jml.spec.read.AsmJmlSpecReader;
import com.jml.spec.write.AsmJmlSpecWriter;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * RQ2 end-to-end roundtrip:
 *   source -> JML-Inferrer -> MethodSpecification ->
 *   InferrerSpecConverter -> MethodSpec -> AsmJmlSpecWriter -> annotated bytes ->
 *   AsmJmlSpecReader -> MethodSpec -> InferrerSpecConverter -> MethodSpecification
 *
 * <p>Asserts that the inferred preconditions, postconditions, assignable clauses,
 * and loop invariants survive the round trip with set-equality.</p>
 */
class InferrerToEmbedderRoundtripTest {

    @Test
    @DisplayName("Inferred spec for a simple field-getter survives bytecode roundtrip")
    void getterRoundtrip() {
        MethodSpecification inferred = inferOne("""
                class Box {
                    private int value;
                    int getValue() {
                        return value;
                    }
                }
                """, "getValue");
        roundtrip(inferred, "Box", "getValue", "()I");
    }

    @Test
    @DisplayName("Inferred spec for null-checked parameter survives bytecode roundtrip")
    void nullCheckRoundtrip() {
        MethodSpecification inferred = inferOne("""
                class Util {
                    int firstChar(String s) {
                        return s.charAt(0);
                    }
                }
                """, "firstChar");
        // Confirm the inferred spec actually contains the precondition we expect,
        // so the roundtrip is non-vacuous.
        assertTrue(inferred.getPreconditions().stream().anyMatch(p -> p.contains("s != null")),
                "expected s != null precondition; got: " + inferred.getPreconditions());
        roundtrip(inferred, "Util", "firstChar", "(Ljava/lang/String;)I");
    }

    @Test
    @DisplayName("Inferred spec for cross-field length loop survives bytecode roundtrip")
    void crossFieldLengthRoundtrip() {
        MethodSpecification inferred = inferOne("""
                class Matrix {
                    private int[] data;
                    private int size;
                    int sum() {
                        int s = 0;
                        for (int i = 0; i < size; i++) {
                            s += data[i];
                        }
                        return s;
                    }
                }
                """, "sum");
        // Confirm the new P1 heuristic fired — non-vacuous roundtrip.
        assertTrue(inferred.getPreconditions().stream()
                        .anyMatch(p -> p.contains("size <= this.data.length")
                                || p.contains("this.size <= this.data.length")),
                "expected cross-field length precondition; got: " + inferred.getPreconditions());
        roundtrip(inferred, "Matrix", "sum", "()I");
    }

    @Test
    @DisplayName("Empty spec list survives bytecode roundtrip without failure")
    void emptySpecRoundtrip() {
        MethodSpecification empty = new MethodSpecification();
        roundtrip(empty, "Empty", "noop", "()V");
    }

    private static MethodSpecification inferOne(String source, String methodName) {
        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> result = parser.parse(source);
        CompilationUnit cu = result.getResult().orElseThrow(() ->
                new AssertionError("parse failed: " + result.getProblems()));
        MethodDeclaration method = cu.findFirst(MethodDeclaration.class,
                m -> m.getNameAsString().equals(methodName))
                .orElseThrow(() -> new AssertionError("method not found: " + methodName));
        return new MethodSpecificationInferrer().inferSpecification(method);
    }

    private static void roundtrip(MethodSpecification original, String className, String methodName,
                                   String descriptor) {
        // Convert inferrer model -> embedder model.
        MethodSpec spec = InferrerSpecConverter.toEmbeddable(original);

        // Build a minimal class file carrying the method signature.
        byte[] cls = makeMinimalClass(className, methodName, descriptor);

        // Embed.
        byte[] embedded = new AsmJmlSpecWriter().embedClass(cls, Map.of(methodName + descriptor, spec));

        // Read back via the JAR API.
        try {
            java.nio.file.Path tmp = java.nio.file.Files.createTempFile("rt-", ".jar");
            try (var jos = new java.util.jar.JarOutputStream(java.nio.file.Files.newOutputStream(tmp))) {
                jos.putNextEntry(new java.util.jar.JarEntry(className + ".class"));
                jos.write(embedded);
                jos.closeEntry();
            }
            try {
                Map<MethodKey, MethodSpec> read = new AsmJmlSpecReader().readJar(tmp);
                MethodSpec readBack = read.get(new MethodKey(className, methodName, descriptor));
                if (original.getPreconditions().isEmpty() && original.getPostconditions().isEmpty()
                        && original.getAssignableClauses().isEmpty() && original.getLoopInvariants().isEmpty()) {
                    // No clauses → no annotation written → reader sees nothing.
                    assertNull(readBack, "empty spec should not produce an annotation; got " + readBack);
                    return;
                }
                assertNotNull(readBack, "spec should be readable back from bytecode");

                MethodSpecification roundTripped = InferrerSpecConverter.fromEmbeddable(readBack);
                assertEquals(original.getPreconditions(), roundTripped.getPreconditions(),
                        "preconditions drift");
                assertEquals(original.getPostconditions(), roundTripped.getPostconditions(),
                        "postconditions drift");
                assertEquals(original.getAssignableClauses(), roundTripped.getAssignableClauses(),
                        "assignable drift");
                assertEquals(original.getLoopInvariants(), roundTripped.getLoopInvariants(),
                        "loop invariant drift");
            } finally {
                java.nio.file.Files.deleteIfExists(tmp);
            }
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
    }

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
        if (descriptor.endsWith("V")) {
            mv.visitInsn(Opcodes.RETURN);
        } else if (descriptor.endsWith("I")) {
            mv.visitInsn(Opcodes.ICONST_0);
            mv.visitInsn(Opcodes.IRETURN);
        } else {
            mv.visitInsn(Opcodes.ACONST_NULL);
            mv.visitInsn(Opcodes.ARETURN);
        }
        mv.visitMaxs(0, 0);
        mv.visitEnd();

        cw.visitEnd();
        return cw.toByteArray();
    }
}
