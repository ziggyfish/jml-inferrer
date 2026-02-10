package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.Statement;
import com.jml.inferrer.model.ClassSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Infers class-level invariants by analyzing fields across all methods.
 * Class invariants are properties that must hold for all instances at all observable states.
 */
public class ClassInvariantInferrer {

    private static final Logger logger = LoggerFactory.getLogger(ClassInvariantInferrer.class);

    /**
     * Infers class invariants from a class declaration.
     */
    public ClassSpecification inferClassSpecification(ClassOrInterfaceDeclaration classDecl) {
        ClassSpecification spec = new ClassSpecification();

        // Analyze field constraints
        analyzeFieldConstraints(classDecl, spec);

        // Analyze immutability
        analyzeImmutability(classDecl, spec);

        // Analyze thread safety at class level
        analyzeClassThreadSafety(classDecl, spec);

        // Analyze resource lifecycle
        analyzeResourceLifecycle(classDecl, spec);

        // Analyze field relationships
        analyzeFieldRelationships(classDecl, spec);

        return spec;
    }

    /**
     * Analyze constraints on individual fields that must always hold.
     */
    private void analyzeFieldConstraints(ClassOrInterfaceDeclaration classDecl, ClassSpecification spec) {
        List<FieldDeclaration> fields = classDecl.getFields();

        for (FieldDeclaration field : fields) {
            for (VariableDeclarator var : field.getVariables()) {
                String fieldName = var.getNameAsString();
                String fieldType = var.getType().asString();

                // Check if field is always non-null
                if (isReferenceType(fieldType)) {
                    boolean alwaysNonNull = checkFieldAlwaysNonNull(classDecl, fieldName);
                    if (alwaysNonNull) {
                        spec.addInvariant(fieldName + " != null");
                    }
                }

                // Check numeric constraints
                if (isNumericType(fieldType)) {
                    checkNumericFieldConstraints(classDecl, fieldName, spec);
                }

                // Check collection size constraints
                if (isCollectionType(fieldType)) {
                    checkCollectionConstraints(classDecl, fieldName, spec);
                }

                // Check initialization constraints
                var.getInitializer().ifPresent(init -> {
                    if (field.isFinal()) {
                        // Final field initialized to specific value
                        spec.addInvariant(fieldName + " == " + init.toString());
                    }
                });
            }
        }
    }

    /**
     * Check if a field is always non-null throughout the class.
     */
    private boolean checkFieldAlwaysNonNull(ClassOrInterfaceDeclaration classDecl, String fieldName) {
        // Check all constructors initialize it to non-null
        boolean initializedInConstructors = classDecl.getConstructors().stream()
                .allMatch(constructor -> {
                    // Check if field is assigned non-null value
                    return constructor.findAll(AssignExpr.class).stream()
                            .anyMatch(assign -> {
                                if (assign.getTarget() instanceof FieldAccessExpr) {
                                    FieldAccessExpr fae = (FieldAccessExpr) assign.getTarget();
                                    return fae.getNameAsString().equals(fieldName) &&
                                           !assign.getValue().isNullLiteralExpr();
                                } else if (assign.getTarget() instanceof NameExpr) {
                                    return assign.getTarget().toString().equals(fieldName) &&
                                           !assign.getValue().isNullLiteralExpr();
                                }
                                return false;
                            });
                });

        if (!initializedInConstructors) return false;

        // Check no method sets it to null
        boolean neverSetToNull = classDecl.getMethods().stream()
                .noneMatch(method -> {
                    return method.findAll(AssignExpr.class).stream()
                            .anyMatch(assign -> {
                                boolean isFieldAssign = (assign.getTarget() instanceof FieldAccessExpr &&
                                                        ((FieldAccessExpr) assign.getTarget()).getNameAsString().equals(fieldName)) ||
                                                       (assign.getTarget() instanceof NameExpr &&
                                                        assign.getTarget().toString().equals(fieldName));
                                return isFieldAssign && assign.getValue().isNullLiteralExpr();
                            });
                });

        return neverSetToNull;
    }

    /**
     * Check numeric field constraints (e.g., field >= 0).
     */
    private void checkNumericFieldConstraints(ClassOrInterfaceDeclaration classDecl, String fieldName, ClassSpecification spec) {
        // Check if field is always >= 0
        boolean alwaysNonNegative = true;

        // Check constructors
        for (var constructor : classDecl.getConstructors()) {
            for (AssignExpr assign : constructor.findAll(AssignExpr.class)) {
                if (isFieldAssignment(assign, fieldName)) {
                    if (!isNonNegativeValue(assign.getValue())) {
                        alwaysNonNegative = false;
                        break;
                    }
                }
            }
        }

        // Check all methods
        if (alwaysNonNegative) {
            for (MethodDeclaration method : classDecl.getMethods()) {
                for (AssignExpr assign : method.findAll(AssignExpr.class)) {
                    if (isFieldAssignment(assign, fieldName)) {
                        if (!isNonNegativeValue(assign.getValue())) {
                            alwaysNonNegative = false;
                            break;
                        }
                    }
                }
                if (!alwaysNonNegative) break;
            }
        }

        if (alwaysNonNegative) {
            spec.addInvariant(fieldName + " >= 0");
        }
    }

    private boolean isFieldAssignment(AssignExpr assign, String fieldName) {
        if (assign.getTarget() instanceof FieldAccessExpr) {
            return ((FieldAccessExpr) assign.getTarget()).getNameAsString().equals(fieldName);
        } else if (assign.getTarget() instanceof NameExpr) {
            return assign.getTarget().toString().equals(fieldName);
        }
        return false;
    }

    private boolean isNonNegativeValue(Expression expr) {
        if (expr.isIntegerLiteralExpr()) {
            return expr.asIntegerLiteralExpr().asInt() >= 0;
        }
        if (expr.isLongLiteralExpr()) {
            return expr.asLongLiteralExpr().asNumber().longValue() >= 0;
        }
        // Conservative: assume unknown expressions might be negative
        return false;
    }

    /**
     * Check collection size constraints.
     */
    private void checkCollectionConstraints(ClassOrInterfaceDeclaration classDecl, String fieldName, ClassSpecification spec) {
        // Check if collection size is always >= 0 (trivially true)
        // Check if collection is always non-empty after construction

        boolean initializedNonEmpty = classDecl.getConstructors().stream()
                .anyMatch(constructor -> {
                    // Look for collection.add() or new ArrayList(Arrays.asList(...))
                    return constructor.findAll(MethodCallExpr.class).stream()
                            .anyMatch(call -> call.getScope().map(s -> s.toString().equals(fieldName)).orElse(false) &&
                                             call.getNameAsString().equals("add"));
                });

        if (initializedNonEmpty) {
            spec.addInvariant(fieldName + ".size() > 0");
        }
    }

    /**
     * Analyze field relationships (e.g., field1 + field2 == constant).
     */
    private void analyzeFieldRelationships(ClassOrInterfaceDeclaration classDecl, ClassSpecification spec) {
        List<FieldDeclaration> fields = classDecl.getFields();
        List<String> numericFields = new ArrayList<>();

        // Collect numeric fields
        for (FieldDeclaration field : fields) {
            for (VariableDeclarator var : field.getVariables()) {
                if (isNumericType(var.getType().asString())) {
                    numericFields.add(var.getNameAsString());
                }
            }
        }

        // Check for sum/product relationships
        if (numericFields.size() >= 2) {
            // Look for patterns like: field3 = field1 + field2 in all setters
            // This is a simplified heuristic
            for (int i = 0; i < numericFields.size(); i++) {
                for (int j = i + 1; j < numericFields.size(); j++) {
                    String field1 = numericFields.get(i);
                    String field2 = numericFields.get(j);

                    // Check if there's a third field that's always their sum
                    for (int k = 0; k < numericFields.size(); k++) {
                        if (k != i && k != j) {
                            String field3 = numericFields.get(k);
                            if (isAlwaysSum(classDecl, field3, field1, field2)) {
                                spec.addInvariant(field3 + " == " + field1 + " + " + field2);
                            }
                        }
                    }
                }
            }
        }
    }

    private boolean isAlwaysSum(ClassOrInterfaceDeclaration classDecl, String target, String field1, String field2) {
        // Check all assignments to target field
        for (MethodDeclaration method : classDecl.getMethods()) {
            for (AssignExpr assign : method.findAll(AssignExpr.class)) {
                if (isFieldAssignment(assign, target)) {
                    Expression value = assign.getValue();
                    if (value instanceof BinaryExpr) {
                        BinaryExpr binExpr = (BinaryExpr) value;
                        if (binExpr.getOperator() == BinaryExpr.Operator.PLUS) {
                            String left = binExpr.getLeft().toString();
                            String right = binExpr.getRight().toString();
                            if ((left.equals(field1) && right.equals(field2)) ||
                                (left.equals(field2) && right.equals(field1))) {
                                continue; // This assignment maintains the invariant
                            } else {
                                return false; // Assignment doesn't maintain invariant
                            }
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Analyze immutability - class is immutable if:
     * 1. All fields are final
     * 2. Class is final
     * 3. No setters exist
     * 4. All field types are immutable
     */
    private void analyzeImmutability(ClassOrInterfaceDeclaration classDecl, ClassSpecification spec) {
        if (classDecl.isInterface()) return;

        boolean allFieldsFinal = !classDecl.getFields().isEmpty() &&
                                 classDecl.getFields().stream()
                                     .allMatch(FieldDeclaration::isFinal);

        boolean classFinal = classDecl.isFinal();

        boolean noSetters = classDecl.getMethods().stream()
                .noneMatch(method -> {
                    String name = method.getNameAsString();
                    boolean isSetter = name.startsWith("set") && name.length() > 3;

                    // Check if method modifies fields
                    boolean modifiesFields = method.findAll(AssignExpr.class).stream()
                            .anyMatch(assign -> assign.getTarget() instanceof FieldAccessExpr ||
                                               isFieldReference(method, assign.getTarget().toString()));

                    return isSetter || modifiesFields;
                });

        if (allFieldsFinal && classFinal && noSetters) {
            spec.setImmutable(true);
        }
    }

    private boolean isFieldReference(MethodDeclaration method, String name) {
        // Check if name is a field (not a parameter or local variable)
        boolean isParameter = method.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(name));
        if (isParameter) return false;

        boolean isLocalVar = method.findAll(VariableDeclarationExpr.class).stream()
                .flatMap(vd -> vd.getVariables().stream())
                .anyMatch(v -> v.getNameAsString().equals(name));

        return !isLocalVar;
    }

    /**
     * Analyze thread safety at class level.
     */
    private void analyzeClassThreadSafety(ClassOrInterfaceDeclaration classDecl, ClassSpecification spec) {
        // Class is thread-safe if:
        // 1. All fields are final (immutable), OR
        // 2. All field accesses are synchronized, OR
        // 3. All fields are volatile and operations are atomic

        boolean allFieldsFinal = !classDecl.getFields().isEmpty() &&
                                 classDecl.getFields().stream()
                                     .allMatch(FieldDeclaration::isFinal);

        boolean allMethodsSynchronized = !classDecl.getMethods().isEmpty() &&
                                         classDecl.getMethods().stream()
                                             .filter(m -> !m.isStatic() && !m.isPrivate())
                                             .allMatch(MethodDeclaration::isSynchronized);

        boolean usesVolatile = classDecl.getFields().stream()
                .anyMatch(f -> f.isVolatile());

        boolean usesConcurrentCollections = classDecl.getFields().stream()
                .anyMatch(f -> f.getVariables().stream()
                        .anyMatch(v -> v.getType().asString().contains("Concurrent") ||
                                      v.getType().asString().contains("Atomic")));

        if (allFieldsFinal || allMethodsSynchronized || usesConcurrentCollections) {
            spec.setThreadSafe(true);
        }
    }

    /**
     * Analyze resource lifecycle - detect resources that must be closed.
     */
    private void analyzeResourceLifecycle(ClassOrInterfaceDeclaration classDecl, ClassSpecification spec) {
        // Look for fields that are closeable resources
        List<String> closeableMethods = new ArrayList<>();

        for (FieldDeclaration field : classDecl.getFields()) {
            for (VariableDeclarator var : field.getVariables()) {
                String fieldType = var.getType().asString();

                // Check if field type is a known resource type
                if (isResourceType(fieldType)) {
                    // Check if there's a close() or dispose() method
                    boolean hasCloseMethod = classDecl.getMethods().stream()
                            .anyMatch(m -> m.getNameAsString().equals("close") ||
                                          m.getNameAsString().equals("dispose") ||
                                          m.getNameAsString().equals("shutdown"));

                    if (hasCloseMethod) {
                        if (!closeableMethods.contains("close")) {
                            closeableMethods.add("close");
                        }
                    }
                }
            }
        }

        // Add @MustCall annotation
        closeableMethods.forEach(spec::addMustCallMethod);
    }

    private boolean isResourceType(String typeName) {
        return typeName.contains("Stream") ||
               typeName.contains("Reader") ||
               typeName.contains("Writer") ||
               typeName.contains("Connection") ||
               typeName.contains("Socket") ||
               typeName.contains("Channel") ||
               typeName.contains("Resource") ||
               typeName.contains("Closeable") ||
               typeName.contains("AutoCloseable");
    }

    private boolean isReferenceType(String type) {
        return !type.equals("int") && !type.equals("long") && !type.equals("double") &&
               !type.equals("float") && !type.equals("boolean") && !type.equals("char") &&
               !type.equals("byte") && !type.equals("short");
    }

    private boolean isNumericType(String type) {
        return type.equals("int") || type.equals("long") || type.equals("double") ||
               type.equals("float") || type.equals("Integer") || type.equals("Long") ||
               type.equals("Double") || type.equals("Float");
    }

    private boolean isCollectionType(String type) {
        return type.contains("List") || type.contains("Set") || type.contains("Map") ||
               type.contains("Collection") || type.contains("Queue");
    }
}
