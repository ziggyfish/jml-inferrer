package com.jml.inferrer.validation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.stmt.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Converts Java source files with JML annotation syntax (@Requires, @Ensures, etc.)
 * into JML comment syntax (//@ requires expr;) that OpenJML can verify.
 *
 * This is a text-level transformation that:
 * 1. Parses the source with JavaParser to find annotation positions
 * 2. Rebuilds the source with annotations replaced by JML comments
 */
public class AnnotationToJMLConverter {

    private static final Logger logger = LoggerFactory.getLogger(AnnotationToJMLConverter.class);

    // Annotations that map to JML method-level spec comments
    private static final Set<String> METHOD_SPEC_ANNOTATIONS = Set.of(
            "Requires", "Ensures", "Signals", "Assignable", "LoopInvariant", "LoopDecreases"
    );

    // Annotations that map to JML method modifiers
    private static final Set<String> METHOD_MODIFIER_ANNOTATIONS = Set.of("Pure");

    // Annotations with no OpenJML equivalent (to be removed)
    private static final Set<String> NON_JML_ANNOTATIONS = Set.of(
            "Observer", "Mutator", "Complexity", "Confidence", "InheritedSpec",
            "SkipInference", "ThreadSafe", "NonNull", "Nullable", "Immutable",
            "MustCall"
    );

    // Class-level annotations
    private static final Set<String> CLASS_SPEC_ANNOTATIONS = Set.of("Invariant");

    private final JavaParser parser;

    public AnnotationToJMLConverter() {
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        this.parser = new JavaParser(config);
    }

    /**
     * Converts a Java source file with JML annotations to JML comment syntax.
     *
     * @param sourceFile the annotated Java source file
     * @return the converted source text with JML comments, or null if no annotations found
     * @throws IOException if the file cannot be read
     */
    public String convert(Path sourceFile) throws IOException {
        String source = Files.readString(sourceFile);
        var parseResult = parser.parse(source);

        if (!parseResult.isSuccessful() || parseResult.getResult().isEmpty()) {
            logger.warn("Failed to parse {}: {}", sourceFile, parseResult.getProblems());
            return null;
        }

        CompilationUnit cu = parseResult.getResult().get();
        List<Replacement> replacements = new ArrayList<>();
        boolean hasAnnotations = false;
        // Collected field names referenced by any inferred spec. Used after the per-method
        // pass to inject /*@ spec_public @*/ before non-public fields so OpenJML allows
        // public-method specs to mention them.
        Set<String> specReferencedFields = new java.util.LinkedHashSet<>();
        Set<String> specReferencedMethods = new java.util.LinkedHashSet<>();

        // Process class-level annotations. Class invariants (//@ public invariant ...)
        // must appear INSIDE the class body — emitting them at the annotation position
        // above `public class Foo { ... }` produces a JML parse error. We collect them
        // here and emit the inside-body replacements LAST so they land ABOVE any
        // spec_public annotations injected before the first field.
        Map<ClassOrInterfaceDeclaration, List<String>> classInvariantsByClass = new java.util.LinkedHashMap<>();
        for (ClassOrInterfaceDeclaration classDecl : cu.findAll(ClassOrInterfaceDeclaration.class)) {
            List<String> pendingClassInvariants = new ArrayList<>();
            for (AnnotationExpr ann : new ArrayList<>(classDecl.getAnnotations())) {
                String name = getSimpleName(ann.getNameAsString());

                if (CLASS_SPEC_ANNOTATIONS.contains(name)) {
                    hasAnnotations = true;
                    String jmlComment = convertClassAnnotation(name, ann);
                    if (jmlComment != null && ann.getBegin().isPresent()) {
                        int startLine = ann.getBegin().get().line;
                        int endLine = ann.getEnd().get().line;
                        replacements.add(new Replacement(startLine, endLine, null));
                        pendingClassInvariants.add(jmlComment);
                        collectClassFieldReferences(extractAnnotationValue(ann), classDecl, specReferencedFields);
                    }
                } else if (NON_JML_ANNOTATIONS.contains(name)) {
                    if (ann.getBegin().isPresent()) {
                        int startLine = ann.getBegin().get().line;
                        int endLine = ann.getEnd().get().line;
                        replacements.add(new Replacement(startLine, endLine, null));
                    }
                }
            }
            if (!pendingClassInvariants.isEmpty()) {
                classInvariantsByClass.put(classDecl, pendingClassInvariants);
            }
        }

        // Process method-level annotations
        for (MethodDeclaration methodDecl : cu.findAll(MethodDeclaration.class)) {
            List<String> specComments = new ArrayList<>();
            // Loop invariants tagged by their owning loop's source line. line 0 means
            // "default to the first loop" (legacy single-loop behaviour).
            Map<Integer, List<String>> invariantsByLoop = new java.util.LinkedHashMap<>();
            // Termination measures, keyed the same way as invariantsByLoop. Emitted as
            // `loop_decreases` clauses immediately after the loop_invariant block for
            // the same loop, so OpenJML sees the variant in the same spec context.
            Map<Integer, List<String>> decreasesByLoop = new java.util.LinkedHashMap<>();
            boolean isPure = false;
            List<int[]> annotationLineRanges = new ArrayList<>();
            // Collect assignable values so we can merge multiple `@Assignable` annotations
            // into a single `assignable a, b, c;` clause. JML treats each `assignable` on
            // its own line as a separate spec case, so emitting `this.r` and `this.g`
            // separately makes each case forbid the other's write.
            List<String> assignableValues = new ArrayList<>();
            // Group signals conditions by exception type so we can emit a single
            // `signals (E e) c1 || c2 || ...;` per type. Multiple `signals` clauses
            // for the same exception are conjunctive in JML, so emitting each guard
            // as its own clause makes each one unprovable (they must ALL hold at
            // every throw, but only one actually holds per throw path).
            Map<String, List<String>> signalsByType = new java.util.LinkedHashMap<>();
            // Signals clauses without a condition (pure exception-type declarations)
            // or with non-when shapes are passed through verbatim.
            List<String> signalsPassthrough = new ArrayList<>();

            for (AnnotationExpr ann : new ArrayList<>(methodDecl.getAnnotations())) {
                String name = getSimpleName(ann.getNameAsString());

                if (METHOD_SPEC_ANNOTATIONS.contains(name)) {
                    hasAnnotations = true;
                    String value = extractAnnotationValue(ann);
                    if (value != null) {
                        if (name.equals("LoopInvariant")) {
                            int loopLine = extractLoopLineMember(ann);
                            invariantsByLoop.computeIfAbsent(loopLine, k -> new ArrayList<>())
                                    .add(normalizeJMLExpression(value));
                        } else if (name.equals("LoopDecreases")) {
                            int loopLine = extractLoopLineMember(ann);
                            decreasesByLoop.computeIfAbsent(loopLine, k -> new ArrayList<>())
                                    .add(normalizeJMLExpression(value));
                        } else if (name.equals("Assignable")) {
                            String normalized = normalizeJMLExpression(value);
                            if (!assignableValues.contains(normalized)) {
                                assignableValues.add(normalized);
                            }
                        } else if (name.equals("Signals")) {
                            String normalized = normalizeJMLExpression(value);
                            int whenIdx = normalized.indexOf(" when ");
                            if (whenIdx > 0) {
                                String excType = normalized.substring(0, whenIdx).trim();
                                String cond = normalized.substring(whenIdx + 6).trim();
                                signalsByType.computeIfAbsent(excType, k -> new ArrayList<>())
                                        .add(cond);
                            } else if (normalized.matches("(?:[\\w.]+\\.)?[A-Z]\\w*")) {
                                // Bare exception-type passthrough — comes from a wrap-and-rethrow
                                // catch (ThrowStmt with no enclosing IfStmt). The exception is
                                // thrown when execution reaches the catch, which can happen on
                                // any path that doesn't take an explicit guard. Fold this into
                                // the per-type group with `true` so it disjuncts with any guard
                                // clauses; otherwise the conjunction `(guard) AND (true)` would
                                // restrict the exception to only the guard's condition, which
                                // is wrong when there's a separate catch path.
                                signalsByType.computeIfAbsent(normalized, k -> new ArrayList<>())
                                        .add("true");
                            } else {
                                String jmlClause = convertMethodAnnotation(name, value);
                                if (jmlClause != null) {
                                    signalsPassthrough.add(jmlClause);
                                }
                            }
                        } else {
                            String jmlClause = convertMethodAnnotation(name, value);
                            if (jmlClause != null) {
                                specComments.add(jmlClause);
                            }
                        }
                        // Record any field references that appear in the spec text so the
                        // class-level `spec_public` injection below can find them.
                        if (methodDecl.isPublic()) {
                            collectFieldReferences(value, methodDecl, specReferencedFields);
                            collectMethodReferences(value, methodDecl, specReferencedMethods);
                        }
                    }
                    if (ann.getBegin().isPresent()) {
                        annotationLineRanges.add(new int[]{
                                ann.getBegin().get().line,
                                ann.getEnd().get().line
                        });
                    }
                } else if (METHOD_MODIFIER_ANNOTATIONS.contains(name)) {
                    hasAnnotations = true;
                    if (name.equals("Pure")) {
                        isPure = true;
                    }
                    if (ann.getBegin().isPresent()) {
                        annotationLineRanges.add(new int[]{
                                ann.getBegin().get().line,
                                ann.getEnd().get().line
                        });
                    }
                } else if (NON_JML_ANNOTATIONS.contains(name)) {
                    if (ann.getBegin().isPresent()) {
                        annotationLineRanges.add(new int[]{
                                ann.getBegin().get().line,
                                ann.getEnd().get().line
                        });
                    }
                }
            }

            // Merge all assignable values into a single clause so JML sees one frame
            // condition, not N per-case frames.
            if (!assignableValues.isEmpty()) {
                specComments.add("assignable " + String.join(", ", assignableValues) + ";");
            }

            // Merge per-guard signals into `signals (E e) c1 || c2 || ...;` to turn the
            // JML-conjunctive clauses into the disjunction that actually characterises
            // the set of throw states.
            for (Map.Entry<String, List<String>> entry : signalsByType.entrySet()) {
                String excType = entry.getKey();
                List<String> conditions = entry.getValue();
                List<String> unique = new ArrayList<>();
                for (String c : conditions) {
                    if (!unique.contains(c)) unique.add(c);
                }
                // If any disjunct is a tautology (`true`), the whole disjunction reduces
                // to `true` — collapse to avoid a noisy `(guard) || (true)` form that
                // adds no information but can confuse the prover.
                String joined;
                if (unique.contains("true")) {
                    joined = "true";
                } else if (unique.size() == 1) {
                    joined = unique.get(0);
                } else {
                    joined = unique.stream()
                            .map(c -> "(" + c + ")")
                            .collect(java.util.stream.Collectors.joining(" || "));
                }
                specComments.add("signals (" + excType + " e) " + joined + ";");
            }
            specComments.addAll(signalsPassthrough);

            if (!specComments.isEmpty() || isPure || !invariantsByLoop.isEmpty() || !decreasesByLoop.isEmpty()) {
                // Build JML spec block to insert before method declaration
                String indent = "";
                if (methodDecl.getBegin().isPresent()) {
                    indent = getIndent(source, methodDecl.getBegin().get().line);
                }

                // Order: spec lines first, then `/*@ pure @*/` on its own line immediately
                // before the method declaration. OpenJML rejects `/*@ pure @*/` appearing
                // above lightweight spec cases — `pure` must read as a method modifier.
                StringBuilder jmlBlock = new StringBuilder();
                for (String spec : specComments) {
                    jmlBlock.append(indent).append("//@ ").append(spec).append("\n");
                }
                if (isPure) {
                    jmlBlock.append(indent).append("/*@ pure @*/\n");
                }

                // Mark annotation lines for removal
                for (int[] range : annotationLineRanges) {
                    replacements.add(new Replacement(range[0], range[1], null));
                }

                // Insert JML comments before the method (at first annotation line, or method line)
                int insertLine;
                if (!annotationLineRanges.isEmpty()) {
                    insertLine = annotationLineRanges.stream()
                            .mapToInt(r -> r[0])
                            .min().orElse(methodDecl.getBegin().get().line);
                } else {
                    insertLine = methodDecl.getBegin().get().line;
                }
                replacements.add(new Replacement(insertLine, insertLine, jmlBlock.toString(), true));

                // Handle loop invariants and loop_decreases: insert each tagged group
                // above its loop. Tag 0 means "first loop" (legacy fallback for entries
                // the analyzer didn't attribute). Both clause types share the same
                // ordinal-to-loop mapping; loop_decreases lines follow the
                // loop_invariant block for the same loop.
                if ((!invariantsByLoop.isEmpty() || !decreasesByLoop.isEmpty())
                        && methodDecl.getBody().isPresent()) {
                    BlockStmt body = methodDecl.getBody().get();
                    List<Statement> loopsByOrdinal = collectLoopsInVisitOrder(body);

                    java.util.Set<Integer> allOrdinals = new java.util.LinkedHashSet<>();
                    allOrdinals.addAll(invariantsByLoop.keySet());
                    allOrdinals.addAll(decreasesByLoop.keySet());
                    for (Integer ordinal : allOrdinals) {
                        // Ordinal 0 is the legacy/untagged form (and matches the first loop too).
                        // Out-of-range ordinals fall back to the first loop.
                        Statement targetLoop;
                        if (ordinal >= 0 && ordinal < loopsByOrdinal.size()) {
                            targetLoop = loopsByOrdinal.get(ordinal);
                        } else {
                            targetLoop = loopsByOrdinal.isEmpty() ? null : loopsByOrdinal.get(0);
                        }
                        if (targetLoop == null || targetLoop.getBegin().isEmpty()) continue;

                        int loopLine = targetLoop.getBegin().get().line;
                        String loopIndent = getIndent(source, loopLine);
                        StringBuilder loopJml = new StringBuilder();
                        for (String inv : invariantsByLoop.getOrDefault(ordinal, List.of())) {
                            loopJml.append(loopIndent).append("//@ loop_invariant ")
                                    .append(inv).append(";\n");
                        }
                        for (String dec : decreasesByLoop.getOrDefault(ordinal, List.of())) {
                            loopJml.append(loopIndent).append("//@ loop_decreases ")
                                    .append(dec).append(";\n");
                        }
                        replacements.add(new Replacement(loopLine, loopLine,
                                loopJml.toString(), true));
                    }
                }
            }
        }

        if (!hasAnnotations) {
            return null;
        }

        // Note: field-level non-JML annotations (e.g. @Nullable, @NonNull) are stripped
        // by the final regex scrub rather than by line-based removal — they frequently
        // share a line with the field declaration, and removing a whole line would take
        // the declaration with them.

        // Collect non-public fields that need /*@ spec_public @*/ so a post-pass can
        // splice the marker INLINE on the field declaration line. A standalone marker
        // line above the field is rejected by OpenJML as a floating modifier.
        Set<String> fieldsNeedingSpecPublic = new java.util.LinkedHashSet<>();
        for (com.github.javaparser.ast.body.FieldDeclaration field
                : cu.findAll(com.github.javaparser.ast.body.FieldDeclaration.class)) {
            if (field.isPublic()) continue;
            for (var v : field.getVariables()) {
                if (specReferencedFields.contains(v.getNameAsString())) {
                    fieldsNeedingSpecPublic.add(v.getNameAsString());
                }
            }
        }

        // Collect non-public methods referenced by any public-method spec.
        Set<String> methodsNeedingSpecPublic = new java.util.LinkedHashSet<>();
        for (MethodDeclaration md : cu.findAll(MethodDeclaration.class)) {
            if (md.isPublic()) continue;
            if (specReferencedMethods.contains(md.getNameAsString())) {
                methodsNeedingSpecPublic.add(md.getNameAsString());
            }
        }

        // Emit class invariants last. Because applyReplacements processes same-line
        // inserts in reverse-of-insertion order, adding these AFTER spec_public places
        // them ABOVE the spec_public line, inside the class body — the correct shape:
        //     //@ public invariant value >= 0;
        //     /*@ spec_public @*/
        //     int value;
        for (Map.Entry<ClassOrInterfaceDeclaration, List<String>> entry : classInvariantsByClass.entrySet()) {
            ClassOrInterfaceDeclaration classDecl = entry.getKey();
            List<String> invariants = entry.getValue();
            if (classDecl.getBegin().isEmpty()) continue;
            int insertLine;
            String bodyIndent;
            if (!classDecl.getMembers().isEmpty()
                    && classDecl.getMembers().get(0).getBegin().isPresent()) {
                int firstMemberLine = classDecl.getMembers().get(0).getBegin().get().line;
                insertLine = firstMemberLine;
                bodyIndent = getIndent(source, firstMemberLine);
            } else {
                insertLine = classDecl.getBegin().get().line + 1;
                bodyIndent = "    ";
            }
            StringBuilder invBlock = new StringBuilder();
            for (String inv : invariants) {
                invBlock.append(bodyIndent).append(inv).append("\n");
            }
            replacements.add(new Replacement(insertLine, insertLine, invBlock.toString(), true));
        }

        // Also remove import lines for our annotation package
        String result = applyReplacements(source, replacements);
        result = removeAnnotationImports(result);
        // Scrub any residual inferrer annotations that shared a line with a declaration
        // (line-based removal can't reach those). Handles both marker and normal forms.
        result = result.replaceAll(
                "@com\\.jml\\.inferrer\\.annotations\\.\\w+(?:\\s*\\([^)]*\\))?\\s*", "");
        // Splice /*@ spec_public @*/ INLINE before each qualifying field declaration.
        // OpenJML rejects the marker on its own line; it must read as a modifier on
        // the immediately-adjacent declaration.
        for (String fieldName : fieldsNeedingSpecPublic) {
            result = injectInlineSpecPublic(result, fieldName);
        }
        for (String methodName : methodsNeedingSpecPublic) {
            result = injectInlineMethodSpecPublic(result, methodName);
        }
        return result;
    }

    /**
     * Adds {@code /*@ spec_public @*\/} inline on the declaration line of a non-public
     * method whose name is referenced by a public method's spec.
     */
    private String injectInlineMethodSpecPublic(String source, String methodName) {
        String escaped = Pattern.quote(methodName);
        Pattern pat = Pattern.compile(
                "(?m)^(\\s*)((?:(?:private|protected|static|final|synchronized|native|abstract|default)\\s+)+)"
                        + "((?:int|long|short|byte|char|boolean|float|double|void|String"
                        + "|[A-Z]\\w*(?:\\s*<[^<>]+>)?)\\s*(?:\\[\\s*\\])*)"
                        + "\\s+" + escaped + "\\s*\\(");
        Matcher m = pat.matcher(source);
        if (!m.find()) return source;

        String beforeMatch = source.substring(0, m.start());
        int lineStart = Math.max(0, beforeMatch.lastIndexOf('\n') + 1);
        if (source.substring(lineStart, m.start()).contains("/*@ spec_public @*/")) {
            return source;
        }
        String rebuilt = m.group(1) + "/*@ spec_public @*/ " + m.group(2) + m.group(3)
                + " " + methodName + "(";
        return source.substring(0, m.start()) + rebuilt + source.substring(m.end());
    }

    /**
     * Finds the declaration line for {@code fieldName} in the source text and prepends
     * a {@code /*@ spec_public @*\/} modifier inline (after any existing indentation).
     * Conservative pattern — matches a type token (primitive, capitalised identifier,
     * or bracketed array form) followed by the field name.
     */
    private String injectInlineSpecPublic(String source, String fieldName) {
        String escaped = Pattern.quote(fieldName);
        Pattern pat = Pattern.compile(
                "(?m)^(\\s*)((?:(?:public|protected|private|static|final|transient|volatile)\\s+)*)"
                        + "((?:int|long|short|byte|char|boolean|float|double|String"
                        + "|[A-Z]\\w*(?:\\s*<[^<>]+>)?)\\s*(?:\\[\\s*\\])*)"
                        + "\\s+" + escaped + "\\s*[,=;]");
        Matcher m = pat.matcher(source);
        if (!m.find()) return source;

        // Skip if this specific declaration already has spec_public inline (re-run safety).
        String beforeMatch = source.substring(0, m.start());
        int lineStart = Math.max(0, beforeMatch.lastIndexOf('\n') + 1);
        if (source.substring(lineStart, m.start()).contains("/*@ spec_public @*/")) {
            return source;
        }

        String rebuilt = m.group(1) + "/*@ spec_public @*/ " + m.group(2) + m.group(3)
                + " " + fieldName + source.charAt(m.end() - 1);
        return source.substring(0, m.start()) + rebuilt + source.substring(m.end());
    }

    /**
     * Scans {@code specValue} for bare identifiers that match instance-field names of the
     * enclosing class and records them in {@code into}. Used to seed the spec_public
     * injection pass.
     */
    private void collectFieldReferences(String specValue,
                                        MethodDeclaration methodDecl,
                                        Set<String> into) {
        if (specValue == null) return;
        Optional<ClassOrInterfaceDeclaration> classOpt = methodDecl
                .findAncestor(ClassOrInterfaceDeclaration.class);
        if (classOpt.isEmpty()) return;
        collectClassFieldReferences(specValue, classOpt.get(), into);
    }

    private void collectClassFieldReferences(String specValue,
                                              ClassOrInterfaceDeclaration classDecl,
                                              Set<String> into) {
        if (specValue == null) return;
        Set<String> fieldNames = new java.util.HashSet<>();
        classDecl.getFields().forEach(fd -> fd.getVariables()
                .forEach(v -> fieldNames.add(v.getNameAsString())));
        if (fieldNames.isEmpty()) return;

        Matcher m = Pattern.compile("\\b([a-zA-Z_$][a-zA-Z_$0-9]*)\\b").matcher(specValue);
        while (m.find()) {
            String tok = m.group(1);
            if (fieldNames.contains(tok)) into.add(tok);
        }
    }

    /**
     * Scans {@code specValue} for identifiers matching private/package methods of the
     * enclosing class. These need {@code /*@ spec_public @*\/} so a public-method spec
     * can legally reference them.
     */
    private void collectMethodReferences(String specValue,
                                          MethodDeclaration methodDecl,
                                          Set<String> into) {
        if (specValue == null) return;
        Optional<ClassOrInterfaceDeclaration> classOpt = methodDecl
                .findAncestor(ClassOrInterfaceDeclaration.class);
        if (classOpt.isEmpty()) return;
        Set<String> nonPublicMethodNames = new java.util.HashSet<>();
        classOpt.get().getMethods().forEach(md -> {
            if (!md.isPublic()) nonPublicMethodNames.add(md.getNameAsString());
        });
        if (nonPublicMethodNames.isEmpty()) return;

        Matcher m = Pattern.compile("\\b([a-zA-Z_$][a-zA-Z_$0-9]*)\\s*\\(").matcher(specValue);
        while (m.find()) {
            String tok = m.group(1);
            if (nonPublicMethodNames.contains(tok)) into.add(tok);
        }
    }

    /**
     * Checks if a source file contains any JML annotations worth converting.
     */
    public boolean hasJMLAnnotations(Path sourceFile) throws IOException {
        String source = Files.readString(sourceFile);
        return source.contains("@Requires") || source.contains("@Ensures")
                || source.contains("@LoopInvariant") || source.contains("@Signals")
                || source.contains("@Assignable") || source.contains("@Pure")
                || source.contains("@Invariant");
    }

    private String convertMethodAnnotation(String name, String value) {
        String normalized = normalizeJMLExpression(value);
        return switch (name) {
            case "Requires" -> "requires " + normalized + ";";
            case "Ensures" -> "ensures " + normalized + ";";
            case "Signals" -> convertSignals(normalized);
            case "Assignable" -> "assignable " + normalized + ";";
            default -> null;
        };
    }

    private String convertClassAnnotation(String name, AnnotationExpr ann) {
        if (name.equals("Invariant")) {
            String value = extractAnnotationValue(ann);
            if (value != null) {
                return "//@ public invariant " + normalizeJMLExpression(value) + ";";
            }
        }
        return null;
    }

    /**
     * Converts the inferrer's exception descriptions (some natural-language) to
     * well-formed JML {@code signals} clauses. Returns {@code null} for shapes
     * the converter can't confidently translate — the caller drops those.
     */
    private String convertSignals(String value) {
        if (value == null) return null;
        value = value.trim();

        if (value.startsWith("propagates ")) {
            return "signals (" + value.substring("propagates ".length()).trim() + " e) true;";
        }
        if (value.startsWith("wraps ") && value.contains(" in ")) {
            String exc = value.substring("wraps ".length(), value.indexOf(" in ")).trim();
            return "signals (" + exc + " e) false;";
        }
        if (value.startsWith("on ") && value.contains(" returns ")) {
            String exc = value.substring("on ".length(), value.indexOf(" returns ")).trim();
            return "signals (" + exc + " e) false;";
        }
        if (value.startsWith("handles ")) {
            String exc = value.substring("handles ".length())
                    .replaceFirst("\\s*\\(.*\\)$", "").trim();
            return "signals (" + exc + " e) false;";
        }
        if (value.startsWith("suppresses ")) {
            return "signals (" + value.substring("suppresses ".length()).trim() + " e) false;";
        }
        if (value.startsWith("recovers from ")) {
            String exc = value.substring("recovers from ".length())
                    .replaceFirst("\\s+and\\s+retries$", "").trim();
            return "signals (" + exc + " e) false;";
        }
        if (value.startsWith("falls back on ")) {
            return "signals (" + value.substring("falls back on ".length()).trim() + " e) false;";
        }

        int whenIndex = value.indexOf(" when ");
        if (whenIndex > 0) {
            String excType = value.substring(0, whenIndex).trim();
            String condition = value.substring(whenIndex + 6).trim();
            return "signals (" + excType + " e) " + condition + ";";
        }

        // Bare exception type name (Capitalized identifier).
        if (value.matches("(?:[\\w.]+\\.)?[A-Z]\\w*")) {
            return "signals (" + value + " e) true;";
        }

        return null;
    }

    /**
     * Normalizes JML expressions for OpenJML compatibility.
     */
    String normalizeJMLExpression(String expr) {
        String result = expr;

        // Remove surrounding quotes if present (defensive — extractAnnotationValue
        // should already have stripped them for StringLiteralExpr inputs).
        if (result.startsWith("\"") && result.endsWith("\"")) {
            result = result.substring(1, result.length() - 1);
        }

        return result.trim();
    }

    private String extractAnnotationValue(AnnotationExpr ann) {
        com.github.javaparser.ast.expr.Expression valueExpr = null;
        if (ann.isSingleMemberAnnotationExpr()) {
            valueExpr = ann.asSingleMemberAnnotationExpr().getMemberValue();
        } else if (ann.isNormalAnnotationExpr()) {
            for (MemberValuePair pair : ann.asNormalAnnotationExpr().getPairs()) {
                if (pair.getNameAsString().equals("value")) {
                    valueExpr = pair.getValue();
                    break;
                }
            }
        }
        if (valueExpr == null) return null;
        // For string literals, return the actual unescaped string value — not the
        // source-form toString() which keeps Java escape sequences (\", \\, \n).
        if (valueExpr.isStringLiteralExpr()) {
            return valueExpr.asStringLiteralExpr().asString();
        }
        String value = valueExpr.toString();
        if (value.startsWith("\"") && value.endsWith("\"")) {
            value = value.substring(1, value.length() - 1);
        }
        return value;
    }

    private String getSimpleName(String annotationName) {
        int lastDot = annotationName.lastIndexOf('.');
        return lastDot >= 0 ? annotationName.substring(lastDot + 1) : annotationName;
    }

    private String getIndent(String source, int lineNumber) {
        String[] lines = source.split("\n", -1);
        if (lineNumber > 0 && lineNumber <= lines.length) {
            String line = lines[lineNumber - 1];
            int i = 0;
            while (i < line.length() && (line.charAt(i) == ' ' || line.charAt(i) == '\t')) {
                i++;
            }
            return line.substring(0, i);
        }
        return "    ";
    }

    private Optional<Statement> findFirstLoop(BlockStmt body) {
        for (Statement stmt : body.getStatements()) {
            if (stmt instanceof ForStmt || stmt instanceof ForEachStmt
                    || stmt instanceof WhileStmt || stmt instanceof DoStmt) {
                return Optional.of(stmt);
            }
        }
        return Optional.empty();
    }

    /**
     * Returns all loop statements in the method body in document (visit) order — depth-first
     * preorder, matching {@link com.github.javaparser.ast.visitor.VoidVisitorAdapter}'s walk
     * order. The analyzer assigns each loop an ordinal in the same traversal order so each
     * invariant tag matches the correct loop irrespective of source-line shifts.
     */
    private List<Statement> collectLoopsInVisitOrder(BlockStmt body) {
        List<Statement> loops = new ArrayList<>();
        body.accept(new com.github.javaparser.ast.visitor.VoidVisitorAdapter<Void>() {
            @Override public void visit(ForStmt n, Void arg) { loops.add(n); super.visit(n, arg); }
            @Override public void visit(WhileStmt n, Void arg) { loops.add(n); super.visit(n, arg); }
            @Override public void visit(ForEachStmt n, Void arg) { loops.add(n); super.visit(n, arg); }
            @Override public void visit(DoStmt n, Void arg) { loops.add(n); super.visit(n, arg); }
        }, null);
        return loops;
    }

    /**
     * Reads the {@code loopLine} member from a {@code @LoopInvariant(...)} annotation, or
     * 0 if absent (legacy single-member form).
     */
    private int extractLoopLineMember(AnnotationExpr ann) {
        if (ann instanceof com.github.javaparser.ast.expr.NormalAnnotationExpr nae) {
            for (var pair : nae.getPairs()) {
                if ("loopLine".equals(pair.getNameAsString())) {
                    var v = pair.getValue();
                    if (v.isIntegerLiteralExpr()) {
                        return v.asIntegerLiteralExpr().asInt();
                    }
                }
            }
        }
        return 0;
    }

    /**
     * Removes import statements for our annotation package.
     */
    private String removeAnnotationImports(String source) {
        return source.replaceAll(
                "(?m)^import\\s+com\\.jml\\.inferrer\\.annotations\\.\\w+;\\s*\\n?", "");
    }

    /**
     * Applies line-based replacements to source text.
     */
    private String applyReplacements(String source, List<Replacement> replacements) {
        if (replacements.isEmpty()) {
            return source;
        }

        // Sort: insertions (before=true) first by line ascending, then removals by line descending
        // Process from bottom to top so line numbers stay valid
        List<Replacement> inserts = replacements.stream()
                .filter(r -> r.insertBefore)
                .sorted(Comparator.comparingInt(r -> r.startLine))
                .toList();

        List<Replacement> removalsAndReplacements = replacements.stream()
                .filter(r -> !r.insertBefore)
                .sorted(Comparator.comparingInt((Replacement r) -> r.startLine).reversed())
                .toList();

        String[] lines = source.split("\n", -1);
        List<String> result = new ArrayList<>(Arrays.asList(lines));

        // First apply removals/replacements (bottom to top)
        Set<Integer> removedLines = new HashSet<>();
        for (Replacement r : removalsAndReplacements) {
            int startIdx = r.startLine - 1;
            int endIdx = r.endLine - 1;
            if (startIdx >= 0 && endIdx < result.size()) {
                for (int i = endIdx; i >= startIdx; i--) {
                    removedLines.add(i);
                }
                if (r.replacement != null) {
                    // Replace the range with new content
                    for (int i = endIdx; i > startIdx; i--) {
                        result.remove(i);
                    }
                    result.set(startIdx, r.replacement);
                } else {
                    // Remove the range
                    for (int i = endIdx; i >= startIdx; i--) {
                        result.remove(i);
                    }
                }
            }
        }

        // Then apply insertions (bottom to top to preserve line numbers)
        List<Replacement> sortedInserts = new ArrayList<>(inserts);
        sortedInserts.sort(Comparator.comparingInt((Replacement r) -> r.startLine).reversed());

        for (Replacement r : sortedInserts) {
            if (r.replacement != null) {
                // Find the current index for this line number, accounting for removals
                int targetIdx = findAdjustedIndex(r.startLine - 1, removalsAndReplacements);
                if (targetIdx >= 0 && targetIdx <= result.size()) {
                    // Insert lines before the target
                    String[] newLines = r.replacement.split("\n", -1);
                    // Remove trailing empty line from split
                    List<String> toInsert = new ArrayList<>();
                    for (String line : newLines) {
                        if (!line.isEmpty() || toInsert.size() < newLines.length - 1) {
                            toInsert.add(line);
                        }
                    }
                    // Remove trailing empty string if replacement ended with \n
                    if (!toInsert.isEmpty() && toInsert.get(toInsert.size() - 1).isEmpty()
                            && r.replacement.endsWith("\n")) {
                        toInsert.remove(toInsert.size() - 1);
                    }
                    result.addAll(targetIdx, toInsert);
                }
            }
        }

        return String.join("\n", result);
    }

    /**
     * Adjusts an original line index based on prior removals.
     */
    private int findAdjustedIndex(int originalIdx, List<Replacement> removals) {
        int adjustment = 0;
        for (Replacement r : removals) {
            if (r.replacement == null) {
                int startIdx = r.startLine - 1;
                int endIdx = r.endLine - 1;
                if (endIdx < originalIdx) {
                    adjustment -= (endIdx - startIdx + 1);
                }
            }
        }
        return originalIdx + adjustment;
    }

    private record Replacement(int startLine, int endLine, String replacement, boolean insertBefore) {
        Replacement(int startLine, int endLine, String replacement) {
            this(startLine, endLine, replacement, false);
        }
    }
}
