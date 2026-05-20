package com.jml.inferrer.experiment;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.JavadocComment;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.jml.inferrer.processor.CodebaseProcessor;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.file.*;
import java.time.Duration;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Experiment runner for LLM-based test generation evaluation.
 * <p>
 * Implements the multi-phase experiment described in the journal article:
 * 1. Runs JML-Inferrer on target classes
 * 2. Extracts method signatures, JML specs, and source code
 * 3. Calls Gemini API with 4 prompt templates (P1-P4)
 * 4. Generates test files in the commons-test-project structure
 * 5. Collects generation metrics
 */
public class ExperimentRunner {

    private static final Logger logger = LoggerFactory.getLogger(ExperimentRunner.class);
    private static final Gson GSON = new GsonBuilder().setPrettyPrinting().create();

    // The 11 target classes from the paper
    private static final List<ClassInfo> TARGET_CLASSES = List.of(
            new ClassInfo("NumberUtils", "org.apache.commons.lang3.math", "math/NumberUtils.java"),
            new ClassInfo("BooleanUtils", "org.apache.commons.lang3", "BooleanUtils.java"),
            new ClassInfo("CharUtils", "org.apache.commons.lang3", "CharUtils.java"),
            new ClassInfo("MutableInt", "org.apache.commons.lang3.mutable", "mutable/MutableInt.java"),
            new ClassInfo("MutableDouble", "org.apache.commons.lang3.mutable", "mutable/MutableDouble.java"),
            new ClassInfo("MutableBoolean", "org.apache.commons.lang3.mutable", "mutable/MutableBoolean.java"),
            new ClassInfo("Pair", "org.apache.commons.lang3.tuple", "tuple/Pair.java"),
            new ClassInfo("MutablePair", "org.apache.commons.lang3.tuple", "tuple/MutablePair.java"),
            new ClassInfo("Validate", "org.apache.commons.lang3", "Validate.java"),
            new ClassInfo("Range", "org.apache.commons.lang3", "Range.java"),
            new ClassInfo("Mutable", "org.apache.commons.lang3.mutable", "mutable/Mutable.java")
    );

    // Phase prompt templates from the paper (Appendix D)
    private static final String P1_TEMPLATE =
            "Write unit tests for the following function signatures under typical development constraints. " +
            "Provide the tests as a developer would normally write them, without any formal specification guidance.\n\n" +
            "Class: %s\nPackage: %s\n\nMethod signatures:\n%s\n\n" +
            "Generate a complete JUnit 5 test class named %sTestP1 in package %s. " +
            "Use static imports for assertions. Import the class under test from %s.";

    private static final String P2_TEMPLATE =
            "Given the following function signatures, write a comprehensive set of unit tests. " +
            "Ensure that the tests cover normal behavior, edge cases, and potential failure scenarios.\n\n" +
            "Class: %s\nPackage: %s\n\nMethod signatures:\n%s\n\n" +
            "Generate a complete JUnit 5 test class named %sTestP2 in package %s. " +
            "Use static imports for assertions. Import the class under test from %s.";

    private static final String P3_TEMPLATE =
            "Given the following function signatures and formal specifications, write a comprehensive set of unit tests. " +
            "Ensure that the tests cover normal behavior, edge cases, and potential failure scenarios. " +
            "The specification uses JML notation where @requires specifies preconditions and @ensures specifies postconditions.\n\n" +
            "Class: %s\nPackage: %s\n\nMethod signatures with JML specifications:\n%s\n\n" +
            "Generate a complete JUnit 5 test class named %sTestP3 in package %s. " +
            "Use static imports for assertions. Import the class under test from %s.";

    private static final String P3C_TEMPLATE =
            "Given the following function signatures and formal specifications, write a comprehensive set of unit tests. " +
            "Ensure that the tests cover normal behavior, edge cases, and potential failure scenarios. " +
            "The specification uses JML notation where @requires specifies preconditions and @ensures specifies postconditions.\n\n" +
            "Class: %s\nPackage: %s\n\nMethod signatures with JML specifications:\n%s\n\n" +
            "Generate a complete JUnit 5 test class named %sTestP3C in package %s. " +
            "Use static imports for assertions. Import the class under test from %s.";

    private static final String P4_TEMPLATE =
            "Given the following function implementations, write a comprehensive set of unit tests. " +
            "Ensure that the tests cover normal behavior, edge cases, and potential failure scenarios.\n\n" +
            "Class: %s\nPackage: %s\n\nMethod implementations:\n%s\n\n" +
            "Generate a complete JUnit 5 test class named %sTestP4 in package %s. " +
            "Use static imports for assertions. Import the class under test from %s.";

    // LLM configuration from paper Table 2
    private static final double TEMPERATURE = 0.3;
    private static final int MAX_TOKENS = 16384;
    private static final double TOP_P = 0.95;

    // Configuration
    private String apiKey;
    private String model = "gemini-2.0-flash";
    private Path sourceDir;
    private Path outputDir;
    private Path testProjectDir;
    private int runs = 5;
    private boolean skipInference = false;
    private Set<String> phases = new LinkedHashSet<>(List.of("P1", "P2", "P3", "P4"));

    private final JavaParser javaParser;
    private final HttpClient httpClient;

    public ExperimentRunner() {
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_21);
        this.javaParser = new JavaParser(config);
        this.httpClient = HttpClient.newBuilder()
                .connectTimeout(Duration.ofSeconds(30))
                .build();
    }

    public static void main(String[] args) throws Exception {
        ExperimentRunner runner = new ExperimentRunner();
        runner.parseArgs(args);
        runner.run();
    }

    private void parseArgs(String[] args) {
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--api-key" -> apiKey = args[++i];
                case "--model" -> model = args[++i];
                case "--source-dir" -> sourceDir = Path.of(args[++i]);
                case "--output-dir" -> outputDir = Path.of(args[++i]);
                case "--test-project-dir" -> testProjectDir = Path.of(args[++i]);
                case "--runs" -> runs = Integer.parseInt(args[++i]);
                case "--skip-inference" -> skipInference = true;
                case "--phases" -> {
                    phases = new LinkedHashSet<>();
                    for (String p : args[++i].split(",")) {
                        phases.add(p.trim().toUpperCase());
                    }
                }
                case "--help" -> {
                    printUsage();
                    System.exit(0);
                }
                default -> {
                    System.err.println("Unknown argument: " + args[i]);
                    printUsage();
                    System.exit(1);
                }
            }
        }

        // Resolve defaults
        if (apiKey == null) {
            apiKey = System.getenv("GEMINI_API_KEY");
        }
        if (apiKey == null || apiKey.isBlank()) {
            System.err.println("ERROR: Gemini API key required. Use --api-key KEY or set GEMINI_API_KEY env var.");
            System.exit(1);
        }
        if (testProjectDir == null) {
            testProjectDir = Path.of("experiment/commons-test-project");
        }
        if (sourceDir == null) {
            sourceDir = testProjectDir.resolve("src/main/java");
        }
        if (outputDir == null) {
            outputDir = Path.of("experiment/results");
        }
    }

    private void printUsage() {
        System.out.println("""
                Usage: java -cp <jar> com.jml.inferrer.experiment.ExperimentRunner [options]

                Options:
                  --api-key KEY          Gemini API key (or set GEMINI_API_KEY env var)
                  --model MODEL          Gemini model (default: gemini-2.0-flash)
                  --source-dir DIR       Source directory (default: <test-project>/src/main/java)
                  --output-dir DIR       Output directory (default: experiment/results)
                  --test-project-dir DIR Test project directory (default: experiment/commons-test-project)
                  --runs N               Number of runs per configuration (default: 5)
                  --skip-inference       Skip JML inference, use existing annotations
                  --phases P1,P2,...     Phases to run (default: P1,P2,P3,P4)
                  --help                 Show this help message
                """);
    }

    private void run() throws Exception {
        logger.info("=== JML Experiment Runner ===");
        logger.info("Model: {}", model);
        logger.info("Runs per configuration: {}", runs);
        logger.info("Phases: {}", phases);
        logger.info("Source dir: {}", sourceDir.toAbsolutePath());
        logger.info("Output dir: {}", outputDir.toAbsolutePath());
        logger.info("Test project dir: {}", testProjectDir.toAbsolutePath());

        // Create output directories
        Files.createDirectories(outputDir.resolve("methods"));
        Files.createDirectories(outputDir.resolve("metrics"));

        // Step 1: Prepare working copy and run inference (isolated baseline)
        Path workingDir = outputDir.resolve("annotated-source");
        prepareWorkingCopy(workingDir);

        if (!skipInference) {
            logger.info("Running JML-Inferrer (isolated baseline) on working copy...");
            CodebaseProcessor processor = new CodebaseProcessor(false);
            int processed = processor.processCodebase(workingDir);
            logger.info("JML inference complete. Processed {} files.", processed);
        } else {
            logger.info("Skipping JML inference (--skip-inference).");
        }

        // Step 1b: If P3C is requested, run a second inference pass with
        // compositional refinement enabled, into a parallel directory.
        // Article 3 (RQ3) uses the resulting JML as the alternative spec
        // source for the LLM prompt.
        Path workingDirCompositional = null;
        if (phases.contains("P3C")) {
            workingDirCompositional = outputDir.resolve("annotated-source-compositional");
            prepareWorkingCopy(workingDirCompositional);
            if (!skipInference) {
                logger.info("Running JML-Inferrer (compositional refinement) on parallel working copy...");
                CodebaseProcessor processor =
                        new CodebaseProcessor(false, /*withCompositional=*/ true);
                int processed = processor.processCodebase(workingDirCompositional);
                logger.info("Compositional inference complete. Processed {} files.", processed);
            }
        }

        // Step 2: Extract method information from both original and annotated versions
        logger.info("Extracting method information...");
        Map<String, ClassMethodInfo> classMethodInfoMap = new LinkedHashMap<>();

        for (ClassInfo classInfo : TARGET_CLASSES) {
            Path originalFile = sourceDir.resolve(
                    "org/apache/commons/lang3/" + classInfo.relativePath);
            Path annotatedFile = workingDir.resolve(
                    "org/apache/commons/lang3/" + classInfo.relativePath);

            if (!Files.exists(originalFile)) {
                logger.warn("Source file not found: {}. Skipping.", originalFile);
                continue;
            }

            ClassMethodInfo methodInfo = extractMethodInfo(classInfo, originalFile, annotatedFile);

            // If P3C requested, also extract compositional Javadoc for the
            // same methods from the parallel working dir; store as a side
            // channel on each MethodInfo so the prompt builder can pick the
            // right spec source per phase.
            if (workingDirCompositional != null) {
                Path annotatedCompositional = workingDirCompositional.resolve(
                        "org/apache/commons/lang3/" + classInfo.relativePath);
                if (Files.exists(annotatedCompositional)) {
                    attachCompositionalJml(methodInfo, annotatedCompositional);
                }
            }

            classMethodInfoMap.put(classInfo.className, methodInfo);

            // Save method info as JSON
            Path methodJsonPath = outputDir.resolve("methods/" + classInfo.className + ".json");
            Files.writeString(methodJsonPath, GSON.toJson(methodInfo.toJson()));
            logger.info("  {} - {} methods extracted", classInfo.className, methodInfo.methods.size());
        }

        // Step 3: Generate tests for each class x phase x run
        logger.info("Starting test generation...");
        JsonObject generationMetrics = new JsonObject();
        int totalApiCalls = classMethodInfoMap.size() * phases.size() * runs;
        int completedCalls = 0;

        for (Map.Entry<String, ClassMethodInfo> entry : classMethodInfoMap.entrySet()) {
            String className = entry.getKey();
            ClassMethodInfo methodInfo = entry.getValue();
            JsonObject classMetrics = new JsonObject();

            for (String phase : phases) {
                JsonObject phaseMetrics = new JsonObject();

                for (int run = 1; run <= runs; run++) {
                    completedCalls++;
                    logger.info("[{}/{}] Generating tests: {} / {} / run{}",
                            completedCalls, totalApiCalls, className, phase, run);

                    try {
                        String prompt = buildPrompt(phase, methodInfo);
                        String response = callGeminiApi(prompt);
                        String testCode = extractJavaCode(response);

                        if (testCode == null || testCode.isBlank()) {
                            logger.warn("No valid Java code extracted from response for {} {} run{}",
                                    className, phase, run);
                            // One-off dump of the raw response so the extractor
                            // can be retargeted at whatever shape the current
                            // model is emitting. Bounded to first 1.5 KB to
                            // keep the log readable.
                            String sample = response == null ? "<null>"
                                    : response.substring(0, Math.min(1500, response.length()));
                            logger.warn("Raw response (first 1500 chars): >>>\n{}\n<<<", sample);
                            phaseMetrics.addProperty("run" + run, 0);
                            continue;
                        }

                        // Fix package and class name if needed
                        testCode = fixTestCode(testCode, methodInfo, phase);

                        // Save to results directory
                        Path resultsTestDir = outputDir.resolve(
                                "tests/" + phase + "/run" + run);
                        Files.createDirectories(resultsTestDir);
                        Path resultsTestFile = resultsTestDir.resolve(
                                className + "Test" + phase + ".java");
                        Files.writeString(resultsTestFile, testCode);

                        // Copy to test project directory
                        String phaseLower = phase.toLowerCase();
                        Path testProjectTestDir = resolveTestDir(methodInfo.classInfo, phaseLower);
                        Files.createDirectories(testProjectTestDir);
                        Path testProjectTestFile = testProjectTestDir.resolve(
                                className + "Test" + phase + ".java");

                        // For run > 1, append run number to avoid overwriting
                        if (run > 1) {
                            String runTestCode = testCode.replace(
                                    className + "Test" + phase,
                                    className + "Test" + phase + "Run" + run);
                            testProjectTestFile = testProjectTestDir.resolve(
                                    className + "Test" + phase + "Run" + run + ".java");
                            Files.writeString(testProjectTestFile, runTestCode);
                        } else {
                            Files.writeString(testProjectTestFile, testCode);
                        }

                        // Count @Test annotations
                        int testCount = countTestMethods(testCode);
                        phaseMetrics.addProperty("run" + run, testCount);
                        logger.info("  Generated {} test methods", testCount);

                    } catch (Exception e) {
                        logger.error("Error generating tests for {} {} run{}: {}",
                                className, phase, run, e.getMessage());
                        phaseMetrics.addProperty("run" + run, 0);
                    }

                    // Rate limiting: 1 second between API calls
                    if (completedCalls < totalApiCalls) {
                        Thread.sleep(1000);
                    }
                }
                classMetrics.add(phase, phaseMetrics);
            }
            generationMetrics.add(className, classMetrics);
        }

        // Step 4: Save generation metrics
        Path metricsFile = outputDir.resolve("metrics/generation-metrics.json");
        Files.writeString(metricsFile, GSON.toJson(generationMetrics));
        logger.info("Generation metrics saved to {}", metricsFile);

        // Print summary
        printGenerationSummary(generationMetrics);

        logger.info("=== Experiment generation phase complete ===");
        logger.info("Test files generated in: {}", outputDir.resolve("tests"));
        logger.info("Test files copied to: {}", testProjectDir.resolve("src/test/java"));
        logger.info("Next steps:");
        logger.info("  1. Run: cd {} && mvn test", testProjectDir);
        logger.info("  2. Run: cd {} && mvn pitest:mutationCoverage", testProjectDir);
        logger.info("  Or use run-experiment.sh / run-experiment.bat for full automation.");
    }

    /**
     * Copies the 11 target class files to a working directory for annotation.
     */
    private void prepareWorkingCopy(Path workingDir) throws IOException {
        logger.info("Preparing working copy in {}", workingDir);

        for (ClassInfo classInfo : TARGET_CLASSES) {
            Path source = sourceDir.resolve("org/apache/commons/lang3/" + classInfo.relativePath);
            Path target = workingDir.resolve("org/apache/commons/lang3/" + classInfo.relativePath);

            if (Files.exists(source)) {
                Files.createDirectories(target.getParent());
                Files.copy(source, target, StandardCopyOption.REPLACE_EXISTING);
            } else {
                logger.warn("Source file not found: {}", source);
            }
        }
    }

    /**
     * Extracts method information from both original and annotated versions of a class.
     */
    private ClassMethodInfo extractMethodInfo(ClassInfo classInfo,
                                               Path originalFile,
                                               Path annotatedFile) throws IOException {
        ClassMethodInfo info = new ClassMethodInfo();
        info.classInfo = classInfo;
        info.methods = new ArrayList<>();

        // Parse original file
        CompilationUnit originalCu = javaParser.parse(originalFile).getResult()
                .orElseThrow(() -> new IOException("Failed to parse: " + originalFile));

        // Parse annotated file (may be same as original if inference skipped)
        CompilationUnit annotatedCu;
        if (Files.exists(annotatedFile)) {
            annotatedCu = javaParser.parse(annotatedFile).getResult()
                    .orElseThrow(() -> new IOException("Failed to parse: " + annotatedFile));
        } else {
            annotatedCu = originalCu;
        }

        // Extract methods from the primary class declaration
        Optional<ClassOrInterfaceDeclaration> originalClassOpt =
                originalCu.findFirst(ClassOrInterfaceDeclaration.class,
                        c -> c.getNameAsString().equals(classInfo.className));
        Optional<ClassOrInterfaceDeclaration> annotatedClassOpt =
                annotatedCu.findFirst(ClassOrInterfaceDeclaration.class,
                        c -> c.getNameAsString().equals(classInfo.className));

        if (originalClassOpt.isEmpty()) {
            logger.warn("Class {} not found in {}", classInfo.className, originalFile);
            return info;
        }

        ClassOrInterfaceDeclaration originalClass = originalClassOpt.get();
        ClassOrInterfaceDeclaration annotatedClass = annotatedClassOpt.orElse(originalClass);

        // Build a map of annotated methods by signature for lookup
        Map<String, MethodDeclaration> annotatedMethodMap = new HashMap<>();
        for (MethodDeclaration md : annotatedClass.getMethods()) {
            String sig = buildMethodKey(md);
            annotatedMethodMap.put(sig, md);
        }

        for (MethodDeclaration method : originalClass.getMethods()) {
            MethodInfo mi = new MethodInfo();
            mi.name = method.getNameAsString();
            mi.signature = method.getDeclarationAsString(true, true, true);
            mi.returnType = method.getTypeAsString();
            mi.isStatic = method.isStatic();
            mi.isAbstract = method.isAbstract();

            // Get full source code
            mi.sourceCode = method.toString();

            // Get JML annotations from the annotated version
            String key = buildMethodKey(method);
            MethodDeclaration annotatedMethod = annotatedMethodMap.get(key);
            if (annotatedMethod != null) {
                mi.jmlAnnotations = extractJmlAnnotations(annotatedMethod);
                mi.annotatedSignature = buildAnnotatedSignature(annotatedMethod);
            } else {
                mi.jmlAnnotations = "";
                mi.annotatedSignature = mi.signature;
            }

            info.methods.add(mi);
        }

        return info;
    }

    /**
     * Builds a unique key for a method based on name and parameter types.
     */
    private String buildMethodKey(MethodDeclaration method) {
        return method.getNameAsString() + "(" +
                method.getParameters().stream()
                        .map(p -> p.getTypeAsString())
                        .collect(Collectors.joining(",")) + ")";
    }

    /**
     * Extracts JML annotations from a method's Javadoc comment.
     */
    private String extractJmlAnnotations(MethodDeclaration method) {
        Optional<JavadocComment> javadoc = method.getJavadocComment();
        if (javadoc.isEmpty()) return "";

        String comment = javadoc.get().getContent();
        StringBuilder jml = new StringBuilder();

        for (String line : comment.split("\n")) {
            String trimmed = line.trim().replaceFirst("^\\*\\s*", "");
            if (trimmed.startsWith("@requires") || trimmed.startsWith("@ensures") ||
                    trimmed.startsWith("@signals") || trimmed.startsWith("@assignable") ||
                    trimmed.startsWith("@loop_invariant") || trimmed.startsWith("@pure")) {
                if (jml.length() > 0) jml.append("\n");
                jml.append(trimmed);
            }
        }

        return jml.toString();
    }

    /**
     * Populate {@code jmlAnnotationsCompositional} on every method in
     * {@code info} by re-parsing the compositionally-annotated source file.
     * Methods not present in that file (e.g.\ inferrer skipped them) leave
     * the field null and fall back to the isolated annotations for P3C.
     */
    private void attachCompositionalJml(ClassMethodInfo info, Path annotatedCompositional) {
        try {
            ParseResult<CompilationUnit> parseResult = javaParser.parse(annotatedCompositional);
            if (parseResult.getResult().isEmpty()) return;
            CompilationUnit cu = parseResult.getResult().get();
            ClassOrInterfaceDeclaration cls = cu.findFirst(ClassOrInterfaceDeclaration.class).orElse(null);
            if (cls == null) return;
            Map<String, MethodDeclaration> byKey = new HashMap<>();
            for (MethodDeclaration md : cls.getMethods()) byKey.put(buildMethodKey(md), md);
            for (MethodInfo mi : info.methods) {
                MethodDeclaration md = byKey.get(buildMethodKeyForName(mi));
                if (md != null) mi.jmlAnnotationsCompositional = extractJmlAnnotations(md);
            }
        } catch (IOException e) {
            logger.warn("Failed to attach compositional JML from {}: {}", annotatedCompositional, e.getMessage());
        }
    }

    /** Reconstruct the buildMethodKey form from a stored MethodInfo. */
    private String buildMethodKeyForName(MethodInfo mi) {
        // The MethodInfo's signature contains the full Java-style declaration
        // (modifiers, return type, name, params). Extract name + param-type
        // list to match buildMethodKey's format.
        String sig = mi.signature;
        int parenOpen = sig.indexOf('(');
        if (parenOpen < 0) return mi.name + "()";
        int nameEnd = parenOpen;
        // Walk back from parenOpen to find the start of the method name.
        while (nameEnd > 0 && (Character.isJavaIdentifierPart(sig.charAt(nameEnd - 1)))) {
            nameEnd--;
        }
        String name = sig.substring(nameEnd, parenOpen);
        int parenClose = sig.indexOf(')', parenOpen);
        if (parenClose < 0) return name + "()";
        String paramList = sig.substring(parenOpen + 1, parenClose).trim();
        if (paramList.isEmpty()) return name + "()";
        // paramList is like "final int a, String b" — strip modifiers and
        // names to get a comma-separated type list.
        StringBuilder types = new StringBuilder();
        for (String p : paramList.split(",")) {
            String[] tokens = p.trim().split("\\s+");
            // The type is the second-to-last token (last is the param name);
            // earlier tokens are modifiers.
            if (tokens.length >= 2) {
                if (types.length() > 0) types.append(',');
                types.append(tokens[tokens.length - 2]);
            } else if (tokens.length == 1) {
                if (types.length() > 0) types.append(',');
                types.append(tokens[0]);
            }
        }
        return name + "(" + types + ")";
    }

    /**
     * Builds a method signature with JML annotations prepended.
     */
    private String buildAnnotatedSignature(MethodDeclaration method) {
        String jml = extractJmlAnnotations(method);
        String sig = method.getDeclarationAsString(true, true, true);
        if (jml.isEmpty()) return sig;
        return "/*@\n" + jml + "\n@*/\n" + sig;
    }

    /**
     * Builds the prompt for a given phase and class method info.
     */
    private String buildPrompt(String phase, ClassMethodInfo info) {
        String className = info.classInfo.className;
        String pkg = info.classInfo.packageName;
        String testPkg = resolveTestPackage(info.classInfo, phase.toLowerCase());
        String importPkg = pkg + "." + className;

        String methodContent = switch (phase) {
            case "P1" -> info.methods.stream()
                    .map(m -> m.signature + ";")
                    .collect(Collectors.joining("\n"));
            case "P2" -> info.methods.stream()
                    .map(m -> m.signature + ";")
                    .collect(Collectors.joining("\n"));
            case "P3" -> info.methods.stream()
                    .map(m -> {
                        if (m.jmlAnnotations.isEmpty()) return m.signature + ";";
                        return "/*@\n" + m.jmlAnnotations + "\n@*/\n" + m.signature + ";";
                    })
                    .collect(Collectors.joining("\n\n"));
            case "P3C" -> info.methods.stream()
                    .map(m -> {
                        String jml = m.jmlAnnotationsCompositional != null
                                && !m.jmlAnnotationsCompositional.isEmpty()
                                ? m.jmlAnnotationsCompositional
                                : m.jmlAnnotations;
                        if (jml == null || jml.isEmpty()) return m.signature + ";";
                        return "/*@\n" + jml + "\n@*/\n" + m.signature + ";";
                    })
                    .collect(Collectors.joining("\n\n"));
            case "P4" -> info.methods.stream()
                    .map(m -> m.sourceCode)
                    .collect(Collectors.joining("\n\n"));
            default -> throw new IllegalArgumentException("Unknown phase: " + phase);
        };

        String template = switch (phase) {
            case "P1" -> P1_TEMPLATE;
            case "P2" -> P2_TEMPLATE;
            case "P3" -> P3_TEMPLATE;
            case "P3C" -> P3C_TEMPLATE;
            case "P4" -> P4_TEMPLATE;
            default -> throw new IllegalArgumentException("Unknown phase: " + phase);
        };

        return String.format(template,
                className, pkg, methodContent,
                className, testPkg, importPkg);
    }

    /**
     * Calls the Gemini API with the given prompt.
     */
    private String callGeminiApi(String prompt) throws IOException, InterruptedException {
        String apiUrl = String.format(
                "https://generativelanguage.googleapis.com/v1beta/models/%s:generateContent?key=%s",
                model, apiKey);

        JsonObject requestBody = new JsonObject();

        // contents
        JsonArray contents = new JsonArray();
        JsonObject content = new JsonObject();
        JsonArray parts = new JsonArray();
        JsonObject part = new JsonObject();
        part.addProperty("text", prompt);
        parts.add(part);
        content.add("parts", parts);
        contents.add(content);
        requestBody.add("contents", contents);

        // generationConfig
        JsonObject generationConfig = new JsonObject();
        generationConfig.addProperty("temperature", TEMPERATURE);
        generationConfig.addProperty("maxOutputTokens", MAX_TOKENS);
        generationConfig.addProperty("topP", TOP_P);
        // Disable Gemini-2.5's internal "thinking" budget so the full
        // maxOutputTokens go to the visible response. Without this, 2.5-flash
        // burns most of its token budget on hidden reasoning and returns a
        // truncated code block that the extractor cannot find a closing fence
        // for. The field is a no-op on models that don't support it.
        JsonObject thinkingConfig = new JsonObject();
        thinkingConfig.addProperty("thinkingBudget", 0);
        generationConfig.add("thinkingConfig", thinkingConfig);
        requestBody.add("generationConfig", generationConfig);

        HttpRequest request = HttpRequest.newBuilder()
                .uri(URI.create(apiUrl))
                .header("Content-Type", "application/json")
                .POST(HttpRequest.BodyPublishers.ofString(GSON.toJson(requestBody)))
                .timeout(Duration.ofSeconds(120))
                .build();

        HttpResponse<String> response = httpClient.send(request, HttpResponse.BodyHandlers.ofString());

        if (response.statusCode() != 200) {
            throw new IOException("Gemini API error (HTTP " + response.statusCode() + "): " + response.body());
        }

        // Parse response
        JsonObject responseJson = JsonParser.parseString(response.body()).getAsJsonObject();
        JsonArray candidates = responseJson.getAsJsonArray("candidates");
        if (candidates == null || candidates.isEmpty()) {
            throw new IOException("No candidates in Gemini response");
        }

        JsonObject firstCandidate = candidates.get(0).getAsJsonObject();
        JsonObject contentObj = firstCandidate.getAsJsonObject("content");
        JsonArray partsArr = contentObj.getAsJsonArray("parts");
        if (partsArr == null || partsArr.isEmpty()) {
            throw new IOException("No parts in Gemini response");
        }

        return partsArr.get(0).getAsJsonObject().get("text").getAsString();
    }

    /**
     * Extracts Java code from a Gemini response, handling markdown code blocks.
     */
    private String extractJavaCode(String response) {
        if (response == null || response.isBlank()) return null;

        // Try to extract from ```java ... ``` block. Permissive about
        // optional whitespace/newline between the fence and the code.
        Pattern javaBlockPattern = Pattern.compile("```\\s*java\\b\\s*(.*?)```", Pattern.DOTALL);
        Matcher matcher = javaBlockPattern.matcher(response);
        if (matcher.find()) {
            return matcher.group(1).trim();
        }

        // Try generic code block (no language tag).
        Pattern codeBlockPattern = Pattern.compile("```\\s*(.*?)```", Pattern.DOTALL);
        matcher = codeBlockPattern.matcher(response);
        if (matcher.find()) {
            String inner = matcher.group(1).trim();
            if (inner.contains("class ") || inner.contains("import ") || inner.contains("@Test")) {
                return inner;
            }
        }

        // Fallback for truncated responses: the response opens a
        // ```java block but is cut off before the closing fence. Take
        // everything after the opening fence as the body if it looks
        // Java-shaped.
        Pattern openOnly = Pattern.compile("```\\s*java\\b\\s*(.*)", Pattern.DOTALL);
        matcher = openOnly.matcher(response);
        if (matcher.find()) {
            String tail = matcher.group(1).trim();
            if (tail.contains("class ") || tail.contains("import ") || tail.contains("@Test")) {
                // Drop any trailing stray ``` if the close was partial.
                int lastFence = tail.lastIndexOf("```");
                if (lastFence > 0) tail = tail.substring(0, lastFence).trim();
                return tail;
            }
        }

        // If response itself looks like Java code, use as-is.
        String trimmed = response.trim();
        if (trimmed.startsWith("package ") || trimmed.startsWith("import ")
                || trimmed.startsWith("@Test") || trimmed.contains("public class ")) {
            return trimmed;
        }

        return null;
    }

    /**
     * Fixes the test code to ensure correct package declaration and class name.
     */
    private String fixTestCode(String code, ClassMethodInfo info, String phase) {
        String className = info.classInfo.className;
        String phaseLower = phase.toLowerCase();
        String expectedTestPkg = resolveTestPackage(info.classInfo, phaseLower);
        String expectedClassName = className + "Test" + phase;

        // Fix package declaration
        String fixed = code.replaceFirst(
                "package\\s+[\\w.]+;",
                "package " + expectedTestPkg + ";");

        // If no package declaration, add one
        if (!fixed.contains("package ")) {
            fixed = "package " + expectedTestPkg + ";\n\n" + fixed;
        }

        // Ensure import for the class under test
        String classImport = "import " + info.classInfo.packageName + "." + className + ";";
        if (!fixed.contains(classImport)) {
            // Add after package declaration
            fixed = fixed.replaceFirst("(package\\s+[\\w.]+;)", "$1\n\n" + classImport);
        }

        // Fix class name if needed (common LLM naming variations)
        String[] possibleNames = {
                className + "Test",
                className + "Tests",
                className + "Test" + phase.charAt(1),  // e.g., TestP1 -> Test1
                className + phase + "Test"
        };
        for (String possibleName : possibleNames) {
            if (fixed.contains("class " + possibleName) && !possibleName.equals(expectedClassName)) {
                fixed = fixed.replace("class " + possibleName, "class " + expectedClassName);
            }
        }

        return fixed;
    }

    /**
     * Counts @Test annotations in the generated code.
     */
    private int countTestMethods(String code) {
        int count = 0;
        Pattern testPattern = Pattern.compile("@Test\\b");
        Matcher matcher = testPattern.matcher(code);
        while (matcher.find()) {
            count++;
        }
        return count;
    }

    /**
     * Resolves the test package for a given class and phase.
     */
    private String resolveTestPackage(ClassInfo classInfo, String phaseLower) {
        // For classes in sub-packages (math, mutable, tuple), use that sub-package + phase
        // For root-level classes, use the phase directly
        String basePkg = "org.apache.commons.lang3";
        String subPkg = classInfo.packageName.replace(basePkg, "").replaceFirst("^\\.", "");

        if (subPkg.isEmpty()) {
            return basePkg + "." + phaseLower;
        } else {
            return basePkg + "." + subPkg + "." + phaseLower;
        }
    }

    /**
     * Resolves the test directory for a given class and phase.
     */
    private Path resolveTestDir(ClassInfo classInfo, String phaseLower) {
        String testPkg = resolveTestPackage(classInfo, phaseLower);
        String testPkgPath = testPkg.replace('.', '/');
        return testProjectDir.resolve("src/test/java/" + testPkgPath);
    }

    /**
     * Prints a summary table of generation metrics.
     */
    private void printGenerationSummary(JsonObject metrics) {
        System.out.println("\n========================================");
        System.out.println("  Test Generation Summary");
        System.out.println("========================================");
        System.out.printf("%-20s", "Class");
        for (String phase : phases) {
            System.out.printf("  %-8s", phase);
        }
        System.out.println();
        System.out.println("-".repeat(20 + phases.size() * 10));

        for (Map.Entry<String, JsonElement> classEntry : metrics.entrySet()) {
            String className = classEntry.getKey();
            JsonObject classMetrics = classEntry.getValue().getAsJsonObject();
            System.out.printf("%-20s", className);

            for (String phase : phases) {
                if (classMetrics.has(phase)) {
                    JsonObject phaseMetrics = classMetrics.getAsJsonObject(phase);
                    // Average test count across runs
                    double total = 0;
                    int count = 0;
                    for (Map.Entry<String, JsonElement> runEntry : phaseMetrics.entrySet()) {
                        total += runEntry.getValue().getAsInt();
                        count++;
                    }
                    double avg = count > 0 ? total / count : 0;
                    System.out.printf("  %-8.1f", avg);
                } else {
                    System.out.printf("  %-8s", "-");
                }
            }
            System.out.println();
        }
        System.out.println("========================================");
        System.out.println("(Values are average test count per run)");
    }

    // ---- Inner data classes ----

    record ClassInfo(String className, String packageName, String relativePath) {}

    static class ClassMethodInfo {
        ClassInfo classInfo;
        List<MethodInfo> methods;

        JsonObject toJson() {
            JsonObject obj = new JsonObject();
            obj.addProperty("className", classInfo.className);
            obj.addProperty("packageName", classInfo.packageName);
            obj.addProperty("methodCount", methods.size());

            JsonArray methodsArr = new JsonArray();
            for (MethodInfo m : methods) {
                methodsArr.add(m.toJson());
            }
            obj.add("methods", methodsArr);
            return obj;
        }
    }

    static class MethodInfo {
        String name;
        String signature;
        String returnType;
        boolean isStatic;
        boolean isAbstract;
        String sourceCode;
        String jmlAnnotations;
        String jmlAnnotationsCompositional;  // Article 3 / P3C: compositional refinement
        String annotatedSignature;

        JsonObject toJson() {
            JsonObject obj = new JsonObject();
            obj.addProperty("name", name);
            obj.addProperty("signature", signature);
            obj.addProperty("returnType", returnType);
            obj.addProperty("isStatic", isStatic);
            obj.addProperty("isAbstract", isAbstract);
            obj.addProperty("sourceCode", sourceCode);
            obj.addProperty("jmlAnnotations", jmlAnnotations);
            if (jmlAnnotationsCompositional != null) {
                obj.addProperty("jmlAnnotationsCompositional", jmlAnnotationsCompositional);
            }
            obj.addProperty("annotatedSignature", annotatedSignature);
            return obj;
        }
    }
}
