package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Cache for storing and retrieving method specifications.
 * Enables interprocedural analysis by allowing methods to use
 * specifications from methods they call.
 *
 * Enhanced with:
 * - Multiple signature format support for flexible lookups
 * - Inheritance-aware lookups
 * - Pattern matching for similar signatures
 */
public class SpecificationCache {

    private static final Logger logger = LoggerFactory.getLogger(SpecificationCache.class);

    private final Map<String, MethodSpecification> cache = new HashMap<>();

    // Secondary index: method name -> list of full signatures
    private final Map<String, List<String>> methodNameIndex = new HashMap<>();

    // Class to methods index
    private final Map<String, Set<String>> classMethodsIndex = new HashMap<>();

    /**
     * Stores a method specification in the cache.
     *
     * @param methodSignature The method signature (e.g., "ClassName.methodName(ParamType1,ParamType2)")
     * @param specification The inferred specification
     */
    public void put(String methodSignature, MethodSpecification specification) {
        cache.put(methodSignature, specification);

        // Update method name index
        String methodName = extractMethodName(methodSignature);
        methodNameIndex.computeIfAbsent(methodName, k -> new ArrayList<>()).add(methodSignature);

        // Update class methods index
        String className = extractClassName(methodSignature);
        if (className != null) {
            classMethodsIndex.computeIfAbsent(className, k -> new HashSet<>()).add(methodSignature);
        }

        logger.debug("Cached specification for: {}", methodSignature);
    }

    /**
     * Extracts the method name from a signature.
     */
    private String extractMethodName(String signature) {
        int parenIdx = signature.indexOf('(');
        String withoutParams = parenIdx > 0 ? signature.substring(0, parenIdx) : signature;

        int dotIdx = withoutParams.lastIndexOf('.');
        return dotIdx > 0 ? withoutParams.substring(dotIdx + 1) : withoutParams;
    }

    /**
     * Extracts the class name from a signature.
     */
    private String extractClassName(String signature) {
        int parenIdx = signature.indexOf('(');
        String withoutParams = parenIdx > 0 ? signature.substring(0, parenIdx) : signature;

        int dotIdx = withoutParams.lastIndexOf('.');
        return dotIdx > 0 ? withoutParams.substring(0, dotIdx) : null;
    }

    /**
     * Retrieves a method specification from the cache.
     * Tries exact match first, then falls back to fuzzy matching.
     *
     * @param methodSignature The method signature
     * @return The cached specification, or null if not found
     */
    public MethodSpecification get(String methodSignature) {
        // Try exact match first
        MethodSpecification spec = cache.get(methodSignature);
        if (spec != null) {
            return spec;
        }

        // Try without parameters
        String withoutParams = methodSignature.contains("(") ?
                methodSignature.substring(0, methodSignature.indexOf('(')) : methodSignature;
        spec = cache.get(withoutParams);
        if (spec != null) {
            return spec;
        }

        // Try method name only
        String methodName = extractMethodName(methodSignature);
        List<String> candidates = methodNameIndex.get(methodName);
        if (candidates != null && candidates.size() == 1) {
            // Unambiguous match
            return cache.get(candidates.get(0));
        }

        return null;
    }

    /**
     * Retrieves a method specification with inheritance lookup.
     * If not found for the given class, searches parent classes.
     *
     * @param methodSignature The method signature
     * @param callGraph The call graph for inheritance information
     * @return The cached specification, or null if not found
     */
    public MethodSpecification getWithInheritance(String methodSignature, CallGraph callGraph) {
        // Try direct lookup first
        MethodSpecification spec = get(methodSignature);
        if (spec != null) {
            return spec;
        }

        if (callGraph == null) {
            return null;
        }

        // Extract class and method name
        String className = extractClassName(methodSignature);
        String methodName = extractMethodName(methodSignature);

        if (className == null) {
            return null;
        }

        // Search superclass chain
        for (String superclass : callGraph.getSuperclassChain(className)) {
            String parentSignature = superclass + "." + methodName;
            spec = get(parentSignature);
            if (spec != null) {
                logger.debug("Found inherited spec from {} for {}", superclass, methodSignature);
                return spec;
            }
        }

        // Search interfaces
        for (String iface : callGraph.getAllImplementedInterfaces(className)) {
            String ifaceSignature = iface + "." + methodName;
            spec = get(ifaceSignature);
            if (spec != null) {
                logger.debug("Found interface spec from {} for {}", iface, methodSignature);
                return spec;
            }
        }

        return null;
    }

    /**
     * Gets all specifications for methods in a class.
     *
     * @param className The class name
     * @return Map of method signatures to specifications
     */
    public Map<String, MethodSpecification> getClassSpecifications(String className) {
        Map<String, MethodSpecification> result = new HashMap<>();
        Set<String> methodSigs = classMethodsIndex.get(className);

        if (methodSigs != null) {
            for (String sig : methodSigs) {
                MethodSpecification spec = cache.get(sig);
                if (spec != null) {
                    result.put(sig, spec);
                }
            }
        }

        return result;
    }

    /**
     * Finds all specifications matching a method name pattern.
     *
     * @param methodNamePattern The method name (or prefix)
     * @return List of matching specifications
     */
    public List<MethodSpecification> findByMethodName(String methodNamePattern) {
        List<MethodSpecification> result = new ArrayList<>();

        for (Map.Entry<String, List<String>> entry : methodNameIndex.entrySet()) {
            if (entry.getKey().startsWith(methodNamePattern) ||
                entry.getKey().equals(methodNamePattern)) {
                for (String sig : entry.getValue()) {
                    MethodSpecification spec = cache.get(sig);
                    if (spec != null) {
                        result.add(spec);
                    }
                }
            }
        }

        return result;
    }

    /**
     * Checks if a specification exists for a method.
     *
     * @param methodSignature The method signature
     * @return true if specification exists
     */
    public boolean contains(String methodSignature) {
        return cache.containsKey(methodSignature);
    }

    /**
     * Gets the number of cached specifications.
     *
     * @return The cache size
     */
    public int size() {
        return cache.size();
    }

    /**
     * Clears all cached specifications.
     */
    public void clear() {
        cache.clear();
        methodNameIndex.clear();
        classMethodsIndex.clear();
        logger.debug("Cleared specification cache");
    }

    /**
     * Gets all cached specifications.
     *
     * @return Unmodifiable view of all cached specifications
     */
    public Map<String, MethodSpecification> getAll() {
        return Collections.unmodifiableMap(cache);
    }

    /**
     * Merges another cache into this one.
     *
     * @param other The cache to merge from
     */
    public void merge(SpecificationCache other) {
        for (Map.Entry<String, MethodSpecification> entry : other.cache.entrySet()) {
            if (!this.cache.containsKey(entry.getKey())) {
                this.put(entry.getKey(), entry.getValue());
            }
        }
    }

    /**
     * Creates a method signature string from components.
     *
     * @param className The class name
     * @param methodName The method name
     * @param paramTypes The parameter types
     * @return A standardized method signature string
     */
    public static String createSignature(String className, String methodName, String... paramTypes) {
        StringBuilder signature = new StringBuilder();
        if (className != null && !className.isEmpty()) {
            signature.append(className).append(".");
        }
        signature.append(methodName);
        signature.append("(");
        for (int i = 0; i < paramTypes.length; i++) {
            if (i > 0) {
                signature.append(",");
            }
            signature.append(paramTypes[i]);
        }
        signature.append(")");
        return signature.toString();
    }
}
