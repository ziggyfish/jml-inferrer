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
            "Requires", "Ensures", "Signals", "Assignable", "LoopInvariant"
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

        // Process class-level annotations
        for (ClassOrInterfaceDeclaration classDecl : cu.findAll(ClassOrInterfaceDeclaration.class)) {
            for (AnnotationExpr ann : new ArrayList<>(classDecl.getAnnotations())) {
                String name = getSimpleName(ann.getNameAsString());

                if (CLASS_SPEC_ANNOTATIONS.contains(name)) {
                    hasAnnotations = true;
                    String jmlComment = convertClassAnnotation(name, ann);
                    if (jmlComment != null && ann.getBegin().isPresent()) {
                        int startLine = ann.getBegin().get().line;
                        int endLine = ann.getEnd().get().line;
                        String indent = getIndent(source, startLine);
                        replacements.add(new Replacement(startLine, endLine, indent + jmlComment));
                    }
                } else if (NON_JML_ANNOTATIONS.contains(name)) {
                    if (ann.getBegin().isPresent()) {
                        int startLine = ann.getBegin().get().line;
                        int endLine = ann.getEnd().get().line;
                        replacements.add(new Replacement(startLine, endLine, null)); // Remove
                    }
                }
            }
        }

        // Process method-level annotations
        for (MethodDeclaration methodDecl : cu.findAll(MethodDeclaration.class)) {
            List<String> specComments = new ArrayList<>();
            // Loop invariants tagged by their owning loop's source line. line 0 means
            // "default to the first loop" (legacy single-loop behaviour).
            Map<Integer, List<String>> invariantsByLoop = new java.util.LinkedHashMap<>();
            boolean isPure = false;
            List<int[]> annotationLineRanges = new ArrayList<>();

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

            if (!specComments.isEmpty() || isPure || !invariantsByLoop.isEmpty()) {
                // Build JML spec block to insert before method declaration
                String indent = "";
                if (methodDecl.getBegin().isPresent()) {
                    indent = getIndent(source, methodDecl.getBegin().get().line);
                }

                StringBuilder jmlBlock = new StringBuilder();
                if (isPure) {
                    jmlBlock.append(indent).append("/*@ pure @*/\n");
                }
                for (String spec : specComments) {
                    jmlBlock.append(indent).append("//@ ").append(spec).append("\n");
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

                // Handle loop invariants: insert each tagged group above its loop. Tag 0 means
                // "first loop" (legacy fallback for invariants the analyzer didn't attribute).
                if (!invariantsByLoop.isEmpty() && methodDecl.getBody().isPresent()) {
                    BlockStmt body = methodDecl.getBody().get();
                    List<Statement> loopsByOrdinal = collectLoopsInVisitOrder(body);

                    for (Map.Entry<Integer, List<String>> entry : invariantsByLoop.entrySet()) {
                        int ordinal = entry.getKey();
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
                        for (String inv : entry.getValue()) {
                            loopJml.append(loopIndent).append("//@ loop_invariant ")
                                    .append(inv).append(";\n");
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

        // For each non-public field referenced by an inferred public-method spec, inject
        // /*@ spec_public @*/ before the field declaration. Without this, OpenJML rejects
        // ensures/assignable clauses on public methods that name the field.
        for (com.github.javaparser.ast.body.FieldDeclaration field
                : cu.findAll(com.github.javaparser.ast.body.FieldDeclaration.class)) {
            if (field.isPublic()) continue;
            boolean referenced = field.getVariables().stream()
                    .anyMatch(v -> specReferencedFields.contains(v.getNameAsString()));
            if (!referenced) continue;
            if (field.getBegin().isEmpty()) continue;
            int line = field.getBegin().get().line;
            String indent = getIndent(source, line);
            replacements.add(new Replacement(line, line, indent + "/*@ spec_public @*/\n", true));
        }

        // Also remove import lines for our annotation package
        String result = applyReplacements(source, replacements);
        result = removeAnnotationImports(result);
        return result;
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
        Set<String> fieldNames = new java.util.HashSet<>();
        classOpt.get().getFields().forEach(fd -> fd.getVariables()
                .forEach(v -> fieldNames.add(v.getNameAsString())));
        if (fieldNames.isEmpty()) return;

        Matcher m = Pattern.compile("\\b([a-zA-Z_$][a-zA-Z_$0-9]*)\\b").matcher(specValue);
        while (m.find()) {
            String tok = m.group(1);
            if (fieldNames.contains(tok)) into.add(tok);
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
     * Converts @Signals("ExcType when condition") to
     * //@ signals (ExcType e) condition;
     */
    private String convertSignals(String value) {
        // Format: "ExcType when condition"
        int whenIndex = value.indexOf(" when ");
        if (whenIndex > 0) {
            String excType = value.substring(0, whenIndex).trim();
            String condition = value.substring(whenIndex + 6).trim();
            return "signals (" + excType + " e) " + condition + ";";
        }
        // Fallback: treat entire value as exception type
        return "signals (" + value.trim() + " e) true;";
    }

    /**
     * Normalizes JML expressions for OpenJML compatibility.
     */
    String normalizeJMLExpression(String expr) {
        String result = expr;

        // Remove surrounding quotes if present
        if (result.startsWith("\"") && result.endsWith("\"")) {
            result = result.substring(1, result.length() - 1);
        }

        // Unescape backslashes from annotation string values
        result = result.replace("\\\\", "\\");

        // Normalize \forall range shorthand if needed
        // e.g., "\forall int i; 0 <= i < arr.length; arr[i] >= 0"
        // This is already valid OpenJML syntax, so we just clean it up

        return result.trim();
    }

    private String extractAnnotationValue(AnnotationExpr ann) {
        if (ann.isSingleMemberAnnotationExpr()) {
            String value = ann.asSingleMemberAnnotationExpr()
                    .getMemberValue().toString();
            // Remove surrounding quotes
            if (value.startsWith("\"") && value.endsWith("\"")) {
                value = value.substring(1, value.length() - 1);
            }
            return value;
        }
        if (ann.isNormalAnnotationExpr()) {
            for (MemberValuePair pair : ann.asNormalAnnotationExpr().getPairs()) {
                if (pair.getNameAsString().equals("value")) {
                    String value = pair.getValue().toString();
                    if (value.startsWith("\"") && value.endsWith("\"")) {
                        value = value.substring(1, value.length() - 1);
                    }
                    return value;
                }
            }
        }
        return null;
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
