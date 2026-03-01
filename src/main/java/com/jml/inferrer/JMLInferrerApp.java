package com.jml.inferrer;

import com.jml.inferrer.processor.CodebaseProcessor;
import com.jml.inferrer.validation.OpenJMLValidator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Main application entry point for the JML Specification Inferrer.
 * Analyzes Java codebases and generates JML specifications for methods.
 */
public class JMLInferrerApp {

    private static final Logger logger = LoggerFactory.getLogger(JMLInferrerApp.class);

    public static void main(String[] args) {
        if (args.length < 1) {
            printUsage();
            System.exit(1);
        }

        boolean validate = false;
        boolean validateOnly = false;
        String codebasePath = null;

        // Parse arguments
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--validate" -> validate = true;
                case "--validate-only" -> validateOnly = true;
                case "--help", "-h" -> {
                    printUsage();
                    System.exit(0);
                }
                default -> {
                    if (codebasePath == null) {
                        codebasePath = args[i];
                    }
                }
            }
        }

        if (codebasePath == null) {
            System.err.println("Error: No codebase path specified.");
            printUsage();
            System.exit(1);
        }

        logger.info("Starting JML Specification Inferrer");
        logger.info("Target codebase: {}", codebasePath);

        try {
            Path path = Paths.get(codebasePath);

            // Run inference unless --validate-only
            if (!validateOnly) {
                CodebaseProcessor processor = new CodebaseProcessor();

                logger.info("Processing codebase...");
                int processedFiles = processor.processCodebase(path);

                logger.info("Processing complete!");
                logger.info("Total files processed: {}", processedFiles);
            }

            // Run validation if --validate or --validate-only
            if (validate || validateOnly) {
                logger.info("Starting OpenJML theorem prover validation...");
                Path reportPath = Paths.get("jml-validation-report.json");
                OpenJMLValidator validator = new OpenJMLValidator();
                validator.validate(path, reportPath);
            }

        } catch (Exception e) {
            logger.error("Error processing codebase", e);
            System.err.println("Error: " + e.getMessage());
            System.exit(1);
        }
    }

    private static void printUsage() {
        System.err.println("Usage: java -jar jml-inferrer.jar [options] <path-to-java-codebase>");
        System.err.println();
        System.err.println("Options:");
        System.err.println("  --validate        Run inference then validate with OpenJML");
        System.err.println("  --validate-only   Skip inference, validate existing annotated files");
        System.err.println("  --help, -h        Show this help message");
        System.err.println();
        System.err.println("Examples:");
        System.err.println("  java -jar jml-inferrer.jar /path/to/project/src");
        System.err.println("  java -jar jml-inferrer.jar /path/to/project/src --validate");
        System.err.println("  java -jar jml-inferrer.jar --validate-only /path/to/annotated/src");
    }
}
