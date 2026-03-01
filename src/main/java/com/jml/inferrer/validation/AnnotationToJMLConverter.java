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
            List<String> loopInvariants = new ArrayList<>();
            boolean isPure = false;
            List<int[]> annotationLineRanges = new ArrayList<>();

            for (AnnotationExpr ann : new ArrayList<>(methodDecl.getAnnotations())) {
                String name = getSimpleName(ann.getNameAsString());

                if (METHOD_SPEC_ANNOTATIONS.contains(name)) {
                    hasAnnotations = true;
                    String value = extractAnnotationValue(ann);
                    if (value != null) {
                        if (name.equals("LoopInvariant")) {
                            loopInvariants.add(normalizeJMLExpression(value));
                        } else {
                            String jmlClause = convertMethodAnnotation(name, value);
                            if (jmlClause != null) {
                                specComments.add(jmlClause);
                            }
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

            if (!specComments.isEmpty() || isPure || !loopInvariants.isEmpty()) {
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

                // Handle loop invariants: insert before first loop in method body
                if (!loopInvariants.isEmpty() && methodDecl.getBody().isPresent()) {
                    BlockStmt body = methodDecl.getBody().get();
                    Optional<Statement> firstLoop = findFirstLoop(body);
                    if (firstLoop.isPresent() && firstLoop.get().getBegin().isPresent()) {
                        int loopLine = firstLoop.get().getBegin().get().line;
                        String loopIndent = getIndent(source, loopLine);
                        StringBuilder loopJml = new StringBuilder();
                        for (String inv : loopInvariants) {
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

        // Also remove import lines for our annotation package
        String result = applyReplacements(source, replacements);
        result = removeAnnotationImports(result);
        return result;
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
