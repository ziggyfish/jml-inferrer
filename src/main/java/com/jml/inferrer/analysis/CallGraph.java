package com.jml.inferrer.analysis;

import java.util.*;

/**
 * Represents a call graph for interprocedural analysis.
 * Stores method call relationships, class hierarchy, and interface implementations.
 *
 * This enables:
 * - Propagating specifications from called methods to callers
 * - Inheriting specifications from parent classes and interfaces
 * - Understanding the call structure for more precise analysis
 */
public class CallGraph {

    // Method call edges: caller -> set of callees
    private final Map<String, Set<String>> methodCalls = new HashMap<>();

    // Reverse call edges: callee -> set of callers
    private final Map<String, Set<String>> calledBy = new HashMap<>();

    // Class hierarchy: class -> parent class (single inheritance)
    private final Map<String, String> superclasses = new HashMap<>();

    // Interface implementations: class -> set of interfaces
    private final Map<String, Set<String>> implementedInterfaces = new HashMap<>();

    // Interface hierarchy: interface -> parent interfaces
    private final Map<String, Set<String>> extendedInterfaces = new HashMap<>();

    // Method to class mapping: method signature -> containing class
    private final Map<String, String> methodToClass = new HashMap<>();

    // Class to methods mapping: class -> set of method signatures
    private final Map<String, Set<String>> classToMethods = new HashMap<>();

    // Method override relationships: overriding method -> overridden method
    private final Map<String, String> overrides = new HashMap<>();

    /**
     * Records a method call from caller to callee.
     *
     * @param callerSignature The calling method's signature
     * @param calleeSignature The called method's signature
     */
    public void addCall(String callerSignature, String calleeSignature) {
        methodCalls.computeIfAbsent(callerSignature, k -> new HashSet<>()).add(calleeSignature);
        calledBy.computeIfAbsent(calleeSignature, k -> new HashSet<>()).add(callerSignature);
    }

    /**
     * Gets all methods called by a given method.
     *
     * @param methodSignature The method signature
     * @return Set of callee signatures, or empty set if none
     */
    public Set<String> getCallees(String methodSignature) {
        return methodCalls.getOrDefault(methodSignature, Collections.emptySet());
    }

    /**
     * Gets all methods that call a given method.
     *
     * @param methodSignature The method signature
     * @return Set of caller signatures, or empty set if none
     */
    public Set<String> getCallers(String methodSignature) {
        return calledBy.getOrDefault(methodSignature, Collections.emptySet());
    }

    /**
     * Records a class's superclass.
     *
     * @param className The class name
     * @param superclassName The superclass name
     */
    public void setSuperclass(String className, String superclassName) {
        if (superclassName != null && !superclassName.equals("Object") && !superclassName.equals("java.lang.Object")) {
            superclasses.put(className, superclassName);
        }
    }

    /**
     * Gets the superclass of a class.
     *
     * @param className The class name
     * @return The superclass name, or null if none (or Object)
     */
    public String getSuperclass(String className) {
        return superclasses.get(className);
    }

    /**
     * Gets the complete superclass chain for a class.
     *
     * @param className The starting class name
     * @return List of superclasses from immediate to most distant
     */
    public List<String> getSuperclassChain(String className) {
        List<String> chain = new ArrayList<>();
        String current = getSuperclass(className);

        while (current != null) {
            chain.add(current);
            current = getSuperclass(current);
        }

        return chain;
    }

    /**
     * Records that a class implements an interface.
     *
     * @param className The class name
     * @param interfaceName The interface name
     */
    public void addImplementedInterface(String className, String interfaceName) {
        implementedInterfaces.computeIfAbsent(className, k -> new HashSet<>()).add(interfaceName);
    }

    /**
     * Gets all interfaces directly implemented by a class.
     *
     * @param className The class name
     * @return Set of interface names, or empty set if none
     */
    public Set<String> getImplementedInterfaces(String className) {
        return implementedInterfaces.getOrDefault(className, Collections.emptySet());
    }

    /**
     * Gets all interfaces implemented by a class (including inherited).
     *
     * @param className The class name
     * @return Set of all interface names
     */
    public Set<String> getAllImplementedInterfaces(String className) {
        Set<String> allInterfaces = new HashSet<>();

        // Add directly implemented interfaces
        allInterfaces.addAll(getImplementedInterfaces(className));

        // Add interfaces from extended interfaces
        for (String iface : new HashSet<>(allInterfaces)) {
            allInterfaces.addAll(getExtendedInterfacesTransitive(iface));
        }

        // Add interfaces from superclasses
        for (String superclass : getSuperclassChain(className)) {
            allInterfaces.addAll(getImplementedInterfaces(superclass));
            for (String iface : getImplementedInterfaces(superclass)) {
                allInterfaces.addAll(getExtendedInterfacesTransitive(iface));
            }
        }

        return allInterfaces;
    }

    /**
     * Records that an interface extends another interface.
     *
     * @param interfaceName The interface name
     * @param parentInterfaceName The parent interface name
     */
    public void addExtendedInterface(String interfaceName, String parentInterfaceName) {
        extendedInterfaces.computeIfAbsent(interfaceName, k -> new HashSet<>()).add(parentInterfaceName);
    }

    /**
     * Gets all parent interfaces of an interface (transitive).
     */
    private Set<String> getExtendedInterfacesTransitive(String interfaceName) {
        Set<String> result = new HashSet<>();
        Set<String> direct = extendedInterfaces.getOrDefault(interfaceName, Collections.emptySet());
        result.addAll(direct);

        for (String parent : direct) {
            result.addAll(getExtendedInterfacesTransitive(parent));
        }

        return result;
    }

    /**
     * Records which class contains a method.
     *
     * @param methodSignature The method signature
     * @param className The containing class name
     */
    public void addMethodToClass(String methodSignature, String className) {
        methodToClass.put(methodSignature, className);
        classToMethods.computeIfAbsent(className, k -> new HashSet<>()).add(methodSignature);
    }

    /**
     * Gets the class containing a method.
     *
     * @param methodSignature The method signature
     * @return The class name, or null if not found
     */
    public String getMethodClass(String methodSignature) {
        return methodToClass.get(methodSignature);
    }

    /**
     * Gets all methods in a class.
     *
     * @param className The class name
     * @return Set of method signatures
     */
    public Set<String> getClassMethods(String className) {
        return classToMethods.getOrDefault(className, Collections.emptySet());
    }

    /**
     * Records that a method overrides another method.
     *
     * @param overridingMethod The overriding method signature
     * @param overriddenMethod The overridden method signature
     */
    public void addOverride(String overridingMethod, String overriddenMethod) {
        overrides.put(overridingMethod, overriddenMethod);
    }

    /**
     * Gets the method that a given method overrides.
     *
     * @param methodSignature The method signature
     * @return The overridden method signature, or null if none
     */
    public String getOverriddenMethod(String methodSignature) {
        return overrides.get(methodSignature);
    }

    /**
     * Finds a matching method in a parent class or interface.
     *
     * @param methodName The method name (without class prefix)
     * @param paramCount The number of parameters
     * @param className The class to search from
     * @return The matching parent method signature, or null if none found
     */
    public String findParentMethod(String methodName, int paramCount, String className) {
        // Search superclass chain
        for (String superclass : getSuperclassChain(className)) {
            String signature = superclass + "." + methodName;
            if (classToMethods.getOrDefault(superclass, Collections.emptySet())
                    .stream().anyMatch(s -> s.startsWith(signature))) {
                return signature;
            }
        }

        // Search interfaces
        for (String iface : getAllImplementedInterfaces(className)) {
            String signature = iface + "." + methodName;
            if (classToMethods.getOrDefault(iface, Collections.emptySet())
                    .stream().anyMatch(s -> s.startsWith(signature))) {
                return signature;
            }
        }

        return null;
    }

    /**
     * Gets statistics about the call graph.
     */
    public String getStatistics() {
        int totalMethods = methodToClass.size();
        int totalCalls = methodCalls.values().stream().mapToInt(Set::size).sum();
        int totalClasses = classToMethods.size();
        int totalInheritance = superclasses.size() + implementedInterfaces.values().stream().mapToInt(Set::size).sum();

        return String.format("CallGraph: %d methods, %d calls, %d classes, %d inheritance relationships",
                totalMethods, totalCalls, totalClasses, totalInheritance);
    }

    /**
     * Clears all data from the call graph.
     */
    public void clear() {
        methodCalls.clear();
        calledBy.clear();
        superclasses.clear();
        implementedInterfaces.clear();
        extendedInterfaces.clear();
        methodToClass.clear();
        classToMethods.clear();
        overrides.clear();
    }
}
