package com.jml.inferrer.analysis;

import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.Map;

/**
 * Cache for storing and retrieving method specifications.
 * Enables interprocedural analysis by allowing methods to use
 * specifications from methods they call.
 */
public class SpecificationCache {

    private static final Logger logger = LoggerFactory.getLogger(SpecificationCache.class);

    private final Map<String, MethodSpecification> cache = new HashMap<>();

    /**
     * Stores a method specification in the cache.
     *
     * @param methodSignature The method signature (e.g., "ClassName.methodName(ParamType1,ParamType2)")
     * @param specification The inferred specification
     */
    public void put(String methodSignature, MethodSpecification specification) {
        cache.put(methodSignature, specification);
        logger.debug("Cached specification for: {}", methodSignature);
    }

    /**
     * Retrieves a method specification from the cache.
     *
     * @param methodSignature The method signature
     * @return The cached specification, or null if not found
     */
    public MethodSpecification get(String methodSignature) {
        return cache.get(methodSignature);
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
        logger.debug("Cleared specification cache");
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
