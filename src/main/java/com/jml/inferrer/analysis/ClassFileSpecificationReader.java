package com.jml.inferrer.analysis;

import com.jml.inferrer.annotations.Ensures;
import com.jml.inferrer.annotations.LoopInvariant;
import com.jml.inferrer.annotations.Requires;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Reads JML specifications from compiled class files using reflection.
 * Enables interprocedural analysis for libraries without source code.
 */
public class ClassFileSpecificationReader {

    private static final Logger logger = LoggerFactory.getLogger(ClassFileSpecificationReader.class);

    /**
     * Loads specifications from a compiled class file.
     *
     * @param classFilePath Path to the .class file
     * @param cache The specification cache to populate
     */
    public void loadSpecificationsFromClassFile(Path classFilePath, SpecificationCache cache) {
        try {
            // Get the class name from the file path
            String className = extractClassName(classFilePath);
            if (className == null) {
                logger.warn("Could not extract class name from: {}", classFilePath);
                return;
            }

            // Load the class
            File classFile = classFilePath.toFile();
            File classDir = classFile.getParentFile();

            // Find the root of the class hierarchy
            File rootDir = findClassRoot(classFile, className);
            if (rootDir == null) {
                logger.warn("Could not find class root for: {}", className);
                return;
            }

            // Create a class loader
            URLClassLoader classLoader = new URLClassLoader(
                new URL[]{rootDir.toURI().toURL()},
                ClassFileSpecificationReader.class.getClassLoader()
            );

            // Load the class
            Class<?> clazz = classLoader.loadClass(className);
            logger.debug("Loaded class: {}", className);

            // Read specifications from all methods
            for (Method method : clazz.getDeclaredMethods()) {
                MethodSpecification spec = readMethodSpecification(method);
                if (spec.hasSpecifications()) {
                    String signature = buildMethodSignature(className, method);
                    cache.put(signature, spec);
                    logger.debug("Loaded spec from class file: {}", signature);
                }
            }

            classLoader.close();

        } catch (Exception e) {
            logger.error("Error loading specifications from class file: {}", classFilePath, e);
        }
    }

    /**
     * Reads JML specifications from a method's annotations.
     *
     * @param method The reflected method
     * @return The method specification
     */
    private MethodSpecification readMethodSpecification(Method method) {
        MethodSpecification spec = new MethodSpecification();

        // Read @Requires annotations
        Requires[] requiresArray = method.getAnnotationsByType(Requires.class);
        for (Requires req : requiresArray) {
            spec.addPrecondition(req.value());
        }

        // Read @Ensures annotations
        Ensures[] ensuresArray = method.getAnnotationsByType(Ensures.class);
        for (Ensures ens : ensuresArray) {
            spec.addPostcondition(ens.value());
        }

        // Read @LoopInvariant annotations
        LoopInvariant[] loopInvArray = method.getAnnotationsByType(LoopInvariant.class);
        for (LoopInvariant inv : loopInvArray) {
            spec.addLoopInvariant(inv.value());
        }

        return spec;
    }

    /**
     * Builds a method signature for caching.
     *
     * @param className The class name
     * @param method The method
     * @return A signature string
     */
    private String buildMethodSignature(String className, Method method) {
        // Use simple ClassName.methodName format
        return className + "." + method.getName();
    }

    /**
     * Extracts the fully qualified class name from a .class file path.
     *
     * @param classFilePath The path to the .class file
     * @return The fully qualified class name, or null if extraction fails
     */
    private String extractClassName(Path classFilePath) {
        String pathStr = classFilePath.toString().replace('\\', '/');

        // Find where the package structure starts
        // Look for common patterns like /classes/, /target/classes/, /bin/, /build/
        int classesIdx = pathStr.lastIndexOf("/classes/");
        if (classesIdx == -1) {
            classesIdx = pathStr.lastIndexOf("/bin/");
        }
        if (classesIdx == -1) {
            classesIdx = pathStr.lastIndexOf("/build/");
        }

        if (classesIdx != -1) {
            String packagePath = pathStr.substring(classesIdx + "/classes/".length());
            // Remove .class extension
            if (packagePath.endsWith(".class")) {
                packagePath = packagePath.substring(0, packagePath.length() - 6);
            }
            // Convert path separators to dots
            return packagePath.replace('/', '.');
        }

        return null;
    }

    /**
     * Finds the root directory containing compiled classes.
     *
     * @param classFile The class file
     * @param className The fully qualified class name
     * @return The root directory, or null if not found
     */
    private File findClassRoot(File classFile, String className) {
        // Convert class name to path components
        String[] parts = className.split("\\.");
        File current = classFile.getParentFile();

        // Walk up the directory tree based on package depth
        for (int i = parts.length - 2; i >= 0; i--) {
            if (current == null) {
                return null;
            }
            current = current.getParentFile();
        }

        return current;
    }

    /**
     * Loads all specifications from a directory containing class files.
     *
     * @param directory The directory to scan
     * @param cache The specification cache to populate
     */
    public void loadSpecificationsFromDirectory(Path directory, SpecificationCache cache) {
        try {
            java.nio.file.Files.walk(directory)
                .filter(path -> path.toString().endsWith(".class"))
                .forEach(classFile -> loadSpecificationsFromClassFile(classFile, cache));

            logger.info("Loaded specifications from {} class files in {}", cache.size(), directory);
        } catch (Exception e) {
            logger.error("Error loading specifications from directory: {}", directory, e);
        }
    }
}
