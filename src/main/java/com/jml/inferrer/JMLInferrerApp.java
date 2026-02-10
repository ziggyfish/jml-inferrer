package com.jml.inferrer;

import com.jml.inferrer.processor.CodebaseProcessor;
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
            System.err.println("Usage: java -jar jml-inferrer.jar <path-to-java-codebase>");
            System.err.println("Example: java -jar jml-inferrer.jar /path/to/project/src");
            System.exit(1);
        }

        String codebasePath = args[0];
        logger.info("Starting JML Specification Inferrer");
        logger.info("Target codebase: {}", codebasePath);

        try {
            Path path = Paths.get(codebasePath);
            CodebaseProcessor processor = new CodebaseProcessor();

            logger.info("Processing codebase...");
            int processedFiles = processor.processCodebase(path);

            logger.info("Processing complete!");
            logger.info("Total files processed: {}", processedFiles);

        } catch (Exception e) {
            logger.error("Error processing codebase", e);
            System.err.println("Error: " + e.getMessage());
            System.exit(1);
        }
    }
}
