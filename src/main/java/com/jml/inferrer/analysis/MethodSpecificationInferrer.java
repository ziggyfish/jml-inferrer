package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Infers JML specifications (preconditions, postconditions, loop invariants) for methods.
 * Supports interprocedural analysis by using specifications from called methods.
 */
public class MethodSpecificationInferrer {

    private static final Logger logger = LoggerFactory.getLogger(MethodSpecificationInferrer.class);

    private final SpecificationCache cache;

    /**
     * Creates a new inferrer with a specification cache for interprocedural analysis.
     *
     * @param cache The specification cache
     */
    public MethodSpecificationInferrer(SpecificationCache cache) {
        this.cache = cache != null ? cache : new SpecificationCache();
    }

    /**
     * Creates a new inferrer without interprocedural analysis.
     */
    public MethodSpecificationInferrer() {
        this(new SpecificationCache());
    }

    /**
     * Infers specifications for a given method.
     *
     * @param methodDecl The method declaration to analyze
     * @return The inferred method specification
     */
    public MethodSpecification inferSpecification(MethodDeclaration methodDecl) {
        MethodSpecification spec = new MethodSpecification();

        // Basic JML specifications
        inferPreconditions(methodDecl, spec);
        inferPostconditions(methodDecl, spec);
        inferLoopInvariants(methodDecl, spec);

        // Phase 1: Method properties
        inferMethodPurity(methodDecl, spec);
        inferExceptionSpecifications(methodDecl, spec);

        // Phase 2: Frame conditions and advanced specifications
        inferAssignableClauses(methodDecl, spec);

        // Phase 3: Advanced properties
        inferComplexity(methodDecl, spec);
        inferThreadSafety(methodDecl, spec);

        return spec;
    }

    /**
     * Infers preconditions by analyzing parameter usage and early checks.
     */
    private void inferPreconditions(MethodDeclaration methodDecl, MethodSpecification spec) {
        Set<String> preconditions = new LinkedHashSet<>();

        for (Parameter param : methodDecl.getParameters()) {
            String paramName = param.getNameAsString();
            Type paramType = param.getType();

            // Reference type null checks
            if (paramType.isReferenceType() && !paramType.isPrimitiveType()) {
                if (hasNullCheckOrAccess(methodDecl, paramName)) {
                    preconditions.add(paramName + " != null");
                }
            }

            // String-specific preconditions
            if (paramType.asString().equals("String")) {
                analyzeStringParameterConstraints(methodDecl, paramName, preconditions);
            }

            // Numeric type constraints
            if (isNumericType(paramType)) {
                analyzeNumericConstraints(methodDecl, paramName, preconditions);
            }

            // Array and collection constraints
            if (paramType.asString().contains("[]")) {
                analyzeArrayParameterConstraints(methodDecl, paramName, preconditions);
            } else if (isCollectionType(paramType.asString())) {
                analyzeCollectionParameterConstraints(methodDecl, paramName, preconditions);
            }
        }

        // Analyze early validation patterns
        analyzeEarlyValidation(methodDecl, preconditions);

        // Analyze null checks in method body
        NullCheckVisitor nullCheckVisitor = new NullCheckVisitor();
        methodDecl.accept(nullCheckVisitor, null);
        preconditions.addAll(nullCheckVisitor.getNullChecks());

        // Analyze parameter relationships
        analyzeParameterRelationships(methodDecl, preconditions);

        // Interprocedural analysis: propagate preconditions from called methods
        analyzeMethodCallPreconditions(methodDecl, preconditions);

        preconditions.forEach(spec::addPrecondition);
    }

    /**
     * Infers postconditions by analyzing return statements and side effects.
     */
    private void inferPostconditions(MethodDeclaration methodDecl, MethodSpecification spec) {
        Set<String> postconditions = new LinkedHashSet<>();

        if (!methodDecl.getType().isVoidType()) {
            String returnType = methodDecl.getType().asString();

            // Reference type checks
            if (isReferenceType(returnType)) {
                if (alwaysReturnsNonNull(methodDecl)) {
                    postconditions.add("\\result != null");
                }
            }

            // Numeric type analysis
            if (isNumericType(methodDecl.getType())) {
                analyzeReturnValueConstraints(methodDecl, postconditions);
                analyzeNumericReturnBounds(methodDecl, postconditions);
                analyzeReturnRelationToParameters(methodDecl, postconditions);
            }

            // String return analysis
            if (returnType.equals("String")) {
                analyzeStringReturnProperties(methodDecl, postconditions);
            }

            // Collection/Array return analysis
            if (isCollectionType(returnType) || returnType.contains("[]")) {
                analyzeCollectionReturnProperties(methodDecl, postconditions);
            }

            // Builder pattern detection (returns 'this')
            if (returnsThis(methodDecl)) {
                postconditions.add("\\result == this");
            }

            // Factory/Constructor pattern
            if (returnType.equals(methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .map(c -> c.getNameAsString()).orElse(""))) {
                analyzeFactoryMethodPattern(methodDecl, postconditions);
            }

            // Comparison method patterns
            analyzeComparisonMethodPattern(methodDecl, postconditions);

            // Analyze return value identity/equality
            analyzeReturnValueIdentity(methodDecl, postconditions);

            // Interprocedural analysis: propagate postconditions from called methods
            analyzeMethodCallPostconditions(methodDecl, postconditions);
        }

        // Field and parameter modification analysis
        analyzeFieldModifications(methodDecl, postconditions);
        analyzeParameterModifications(methodDecl, postconditions);

        // Exception guarantees
        analyzeExceptionGuarantees(methodDecl, postconditions);

        postconditions.forEach(spec::addPostcondition);
    }

    /**
     * Infers loop invariants by analyzing loop structures.
     */
    private void inferLoopInvariants(MethodDeclaration methodDecl, MethodSpecification spec) {
        LoopInvariantVisitor loopVisitor = new LoopInvariantVisitor();
        methodDecl.accept(loopVisitor, null);
        loopVisitor.getInvariants().forEach(spec::addLoopInvariant);
    }

    private boolean isNumericType(Type type) {
        String typeStr = type.asString();
        return typeStr.equals("int") || typeStr.equals("long") || typeStr.equals("double") ||
               typeStr.equals("float") || typeStr.equals("Integer") || typeStr.equals("Long") ||
               typeStr.equals("Double") || typeStr.equals("Float");
    }

    private boolean isReferenceType(String type) {
        return !type.equals("int") && !type.equals("long") && !type.equals("double") &&
               !type.equals("float") && !type.equals("boolean") && !type.equals("char") &&
               !type.equals("byte") && !type.equals("short") && !type.equals("void");
    }

    /**
     * Checks if a parameter has null check or method/field access that requires it to be non-null.
     */
    private boolean hasNullCheckOrAccess(MethodDeclaration methodDecl, String paramName) {
        // Check for explicit null checks
        boolean hasNullCheck = methodDecl.findAll(BinaryExpr.class).stream()
            .anyMatch(binExpr -> {
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS ||
                    binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS) {
                    return (binExpr.getLeft().toString().equals(paramName) && binExpr.getRight().isNullLiteralExpr()) ||
                           (binExpr.getRight().toString().equals(paramName) && binExpr.getLeft().isNullLiteralExpr());
                }
                return false;
            });

        // Check for method calls on the parameter
        boolean hasMethodCall = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false));

        // Check for field access on the parameter
        boolean hasFieldAccess = methodDecl.findAll(FieldAccessExpr.class).stream()
            .anyMatch(field -> field.getScope().toString().equals(paramName));

        return hasNullCheck || hasMethodCall || hasFieldAccess;
    }

    /**
     * Analyzes String parameter constraints.
     */
    private void analyzeStringParameterConstraints(MethodDeclaration methodDecl, String paramName, Set<String> preconditions) {
        // Check for null requirement
        if (hasNullCheckOrAccess(methodDecl, paramName)) {
            preconditions.add(paramName + " != null");
        }

        // Check for isEmpty() calls
        boolean hasEmptyCheck = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("isEmpty"));

        // Check for length() calls with comparisons
        methodDecl.findAll(MethodCallExpr.class).stream()
            .filter(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("length"))
            .forEach(lengthCall -> {
                // Look for comparisons with this length call
                methodDecl.findAll(BinaryExpr.class).stream()
                    .filter(binExpr -> binExpr.getLeft().toString().contains(paramName + ".length()") ||
                                       binExpr.getRight().toString().contains(paramName + ".length()"))
                    .forEach(binExpr -> {
                        if (binExpr.getOperator() == BinaryExpr.Operator.GREATER &&
                            binExpr.getLeft().toString().contains(paramName + ".length()")) {
                            preconditions.add(paramName + ".length() > " + binExpr.getRight());
                        }
                    });
            });

        // If hasEmptyCheck, likely needs to be non-empty
        if (hasEmptyCheck) {
            preconditions.add("!" + paramName + ".isEmpty()");
        }

        // Check for charAt() calls - implies non-empty
        boolean hasCharAt = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("charAt"));

        if (hasCharAt) {
            preconditions.add(paramName + ".length() > 0");
        }
    }

    /**
     * Analyzes array parameter constraints.
     */
    private void analyzeArrayParameterConstraints(MethodDeclaration methodDecl, String paramName, Set<String> preconditions) {
        // Check for null requirement
        boolean hasArrayAccess = methodDecl.findAll(ArrayAccessExpr.class).stream()
            .anyMatch(access -> access.getName().toString().equals(paramName));

        boolean hasLengthAccess = methodDecl.findAll(FieldAccessExpr.class).stream()
            .anyMatch(field -> field.getScope().toString().equals(paramName) &&
                              field.getNameAsString().equals("length"));

        if (hasArrayAccess || hasLengthAccess) {
            preconditions.add(paramName + " != null");
        }

        // Check for array index access to infer non-empty requirement
        if (hasArrayAccess) {
            // Check if accessing specific indices
            methodDecl.findAll(ArrayAccessExpr.class).stream()
                .filter(access -> access.getName().toString().equals(paramName))
                .forEach(access -> {
                    Expression index = access.getIndex();
                    if (index instanceof IntegerLiteralExpr) {
                        int indexValue = ((IntegerLiteralExpr) index).asInt();
                        preconditions.add(paramName + ".length > " + indexValue);
                    } else {
                        // Generic index access requires non-empty
                        preconditions.add(paramName + ".length > 0");
                    }
                });
        }

        // Check for length comparisons in conditionals
        analyzeArrayLengthConstraints(methodDecl, paramName, preconditions);
    }

    /**
     * Analyzes collection parameter constraints.
     */
    private void analyzeCollectionParameterConstraints(MethodDeclaration methodDecl, String paramName, Set<String> preconditions) {
        // Check for null requirement
        boolean hasMethodCall = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false));

        if (hasMethodCall) {
            preconditions.add(paramName + " != null");
        }

        // Check for size() calls
        boolean hasSizeCheck = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("size"));

        // Check for isEmpty() calls
        boolean hasEmptyCheck = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("isEmpty"));

        // Check for iterator or get operations - implies non-empty
        boolean hasGet = methodDecl.findAll(MethodCallExpr.class).stream()
            .anyMatch(call -> call.getScope()
                .map(s -> s.toString().equals(paramName))
                .orElse(false) && call.getNameAsString().equals("get"));

        if (hasGet) {
            preconditions.add(paramName + ".size() > 0");
        }
    }

    /**
     * Analyzes early validation patterns (throw IllegalArgumentException, etc.).
     */
    private void analyzeEarlyValidation(MethodDeclaration methodDecl, Set<String> preconditions) {
        methodDecl.findAll(IfStmt.class).forEach(ifStmt -> {
            // Check if this if statement throws an exception
            boolean throwsException = ifStmt.getThenStmt().findAll(ThrowStmt.class).size() > 0;

            if (throwsException) {
                Expression condition = ifStmt.getCondition();

                // Invert the condition to get the precondition
                if (condition instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) condition;
                    String invertedCondition = invertCondition(binExpr);
                    if (invertedCondition != null && !invertedCondition.isEmpty()) {
                        preconditions.add(invertedCondition);
                    }
                } else if (condition instanceof UnaryExpr) {
                    UnaryExpr unaryExpr = (UnaryExpr) condition;
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
                        // !(condition) in if-throw means condition must be true
                        preconditions.add(unaryExpr.getExpression().toString());
                    }
                }
            }
        });
    }

    /**
     * Analyzes relationships between parameters.
     */
    private void analyzeParameterRelationships(MethodDeclaration methodDecl, Set<String> preconditions) {
        List<Parameter> params = methodDecl.getParameters();

        // Look for comparisons between parameters
        methodDecl.findAll(BinaryExpr.class).forEach(binExpr -> {
            String left = binExpr.getLeft().toString();
            String right = binExpr.getRight().toString();

            boolean leftIsParam = params.stream().anyMatch(p -> p.getNameAsString().equals(left));
            boolean rightIsParam = params.stream().anyMatch(p -> p.getNameAsString().equals(right));

            if (leftIsParam && rightIsParam) {
                // Both operands are parameters
                switch (binExpr.getOperator()) {
                    case LESS:
                        preconditions.add(left + " < " + right);
                        break;
                    case LESS_EQUALS:
                        preconditions.add(left + " <= " + right);
                        break;
                    case GREATER:
                        preconditions.add(left + " > " + right);
                        break;
                    case GREATER_EQUALS:
                        preconditions.add(left + " >= " + right);
                        break;
                }
            }
        });
    }

    /**
     * Analyzes array length constraints from conditionals.
     */
    private void analyzeArrayLengthConstraints(MethodDeclaration methodDecl, String paramName, Set<String> preconditions) {
        methodDecl.findAll(BinaryExpr.class).stream()
            .filter(binExpr -> binExpr.getLeft().toString().equals(paramName + ".length") ||
                               binExpr.getRight().toString().equals(paramName + ".length"))
            .forEach(binExpr -> {
                if (binExpr.getLeft().toString().equals(paramName + ".length")) {
                    switch (binExpr.getOperator()) {
                        case GREATER:
                            preconditions.add(paramName + ".length > " + binExpr.getRight());
                            break;
                        case GREATER_EQUALS:
                            preconditions.add(paramName + ".length >= " + binExpr.getRight());
                            break;
                        case EQUALS:
                            preconditions.add(paramName + ".length == " + binExpr.getRight());
                            break;
                    }
                } else if (binExpr.getRight().toString().equals(paramName + ".length")) {
                    switch (binExpr.getOperator()) {
                        case LESS:
                            preconditions.add(paramName + ".length > " + binExpr.getLeft());
                            break;
                        case LESS_EQUALS:
                            preconditions.add(paramName + ".length >= " + binExpr.getLeft());
                            break;
                        case EQUALS:
                            preconditions.add(paramName + ".length == " + binExpr.getLeft());
                            break;
                    }
                }
            });
    }

    /**
     * Inverts a condition (for if-throw patterns).
     */
    private String invertCondition(BinaryExpr binExpr) {
        String left = binExpr.getLeft().toString();
        String right = binExpr.getRight().toString();

        return switch (binExpr.getOperator()) {
            case LESS -> left + " >= " + right;
            case LESS_EQUALS -> left + " > " + right;
            case GREATER -> left + " <= " + right;
            case GREATER_EQUALS -> left + " < " + right;
            case EQUALS -> left + " != " + right;
            case NOT_EQUALS -> left + " == " + right;
            case OR -> {
                // !(a || b) means neither a nor b
                if (binExpr.getLeft() instanceof BinaryExpr && binExpr.getRight() instanceof BinaryExpr) {
                    String invertedLeft = invertCondition((BinaryExpr) binExpr.getLeft());
                    String invertedRight = invertCondition((BinaryExpr) binExpr.getRight());
                    yield invertedLeft + " && " + invertedRight;
                }
                yield null;
            }
            default -> null;
        };
    }

    private void analyzeNumericConstraints(MethodDeclaration methodDecl, String paramName, Set<String> preconditions) {
        methodDecl.findAll(BinaryExpr.class).stream()
            .filter(expr -> expr.getLeft().toString().equals(paramName) || expr.getRight().toString().equals(paramName))
            .forEach(expr -> {
                if (expr.getOperator() == BinaryExpr.Operator.GREATER && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " > " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.GREATER_EQUALS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " >= " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.LESS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " < " + expr.getRight());
                } else if (expr.getOperator() == BinaryExpr.Operator.LESS_EQUALS && expr.getLeft().toString().equals(paramName)) {
                    preconditions.add(paramName + " <= " + expr.getRight());
                }
            });
    }

    private boolean alwaysReturnsNonNull(MethodDeclaration methodDecl) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);
        if (returnStmts.isEmpty()) {
            return false;
        }

        return returnStmts.stream()
            .allMatch(ret -> ret.getExpression()
                .map(expr -> !expr.isNullLiteralExpr())
                .orElse(false));
    }

    private void analyzeReturnValueConstraints(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                if (expr instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) expr;
                    if (binExpr.getOperator() == BinaryExpr.Operator.PLUS ||
                        binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                        postconditions.add("\\result >= 0");
                    }
                } else if (expr instanceof MethodCallExpr) {
                    MethodCallExpr methodCall = (MethodCallExpr) expr;
                    if (methodCall.getNameAsString().equals("abs") || methodCall.getNameAsString().equals("length")) {
                        postconditions.add("\\result >= 0");
                    }
                }
            });
        }
    }

    private void analyzeFieldModifications(MethodDeclaration methodDecl, Set<String> postconditions) {
        // Handle unary expressions (++, --)
        methodDecl.findAll(UnaryExpr.class).forEach(unaryExpr -> {
            Expression expr = unaryExpr.getExpression();
            if (expr instanceof FieldAccessExpr) {
                FieldAccessExpr field = (FieldAccessExpr) expr;
                if (field.getScope().toString().equals("this")) {
                    String fieldName = field.getNameAsString();
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                        unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT) {
                        postconditions.add("this." + fieldName + " == \\old(this." + fieldName + ") + 1");
                    } else if (unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT ||
                               unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT) {
                        postconditions.add("this." + fieldName + " == \\old(this." + fieldName + ") - 1");
                    }
                }
            } else if (expr instanceof NameExpr) {
                // Handle direct field access (not through this.)
                String varName = expr.toString();
                methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .ifPresent(classDecl -> {
                        classDecl.getFields().forEach(field -> {
                            field.getVariables().forEach(var -> {
                                if (var.getNameAsString().equals(varName)) {
                                    if (unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT ||
                                        unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT) {
                                        postconditions.add("this." + varName + " == \\old(this." + varName + ") + 1");
                                    } else if (unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT ||
                                               unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT) {
                                        postconditions.add("this." + varName + " == \\old(this." + varName + ") - 1");
                                    }
                                }
                            });
                        });
                    });
            }
        });

        // Handle assignment expressions
        methodDecl.findAll(AssignExpr.class).stream()
            .filter(assign -> assign.getTarget() instanceof FieldAccessExpr)
            .forEach(assign -> {
                FieldAccessExpr field = (FieldAccessExpr) assign.getTarget();
                if (field.getScope().toString().equals("this")) {
                    String fieldName = field.getNameAsString();

                    // Try to infer the specific value assigned
                    Expression value = assign.getValue();
                    AssignExpr.Operator operator = assign.getOperator();

                    // Handle compound assignments (+=, -=, etc.) even when value is simple
                    if (operator != AssignExpr.Operator.ASSIGN) {
                        String operatorStr = getCompoundOperatorString(operator);
                        if (operatorStr != null) {
                            postconditions.add("this." + fieldName + " == \\old(this." + fieldName + ") " + operatorStr + " " + value);
                        } else {
                            postconditions.add("this." + fieldName + " is modified");
                        }
                    } else if (value instanceof NameExpr || value instanceof IntegerLiteralExpr ||
                        value instanceof DoubleLiteralExpr || value instanceof StringLiteralExpr) {
                        postconditions.add("this." + fieldName + " == " + value);
                    } else if (value instanceof BinaryExpr) {
                        // For expressions like: balance = balance + amount
                        // Generate: this.balance == \old(this.balance) + amount
                        String oldExpr = generateOldExpression(fieldName, (BinaryExpr) value, operator);
                        if (oldExpr != null) {
                            postconditions.add(oldExpr);
                        } else {
                            postconditions.add("this." + fieldName + " is modified");
                        }
                    } else {
                        postconditions.add("this." + fieldName + " is modified");
                    }
                }
            });

        // Also check for direct field assignments (not through 'this.')
        methodDecl.findAll(AssignExpr.class).stream()
            .filter(assign -> assign.getTarget() instanceof NameExpr)
            .forEach(assign -> {
                NameExpr nameExpr = (NameExpr) assign.getTarget();
                // Check if this is a field by seeing if it's used elsewhere
                methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                    .ifPresent(classDecl -> {
                        classDecl.getFields().forEach(field -> {
                            field.getVariables().forEach(var -> {
                                if (var.getNameAsString().equals(nameExpr.getNameAsString())) {
                                    Expression value = assign.getValue();
                                    String fieldName = nameExpr.getNameAsString();
                                    AssignExpr.Operator operator = assign.getOperator();

                                    // Handle compound assignments
                                    if (operator != AssignExpr.Operator.ASSIGN) {
                                        String operatorStr = getCompoundOperatorString(operator);
                                        if (operatorStr != null) {
                                            postconditions.add("this." + fieldName + " == \\old(this." + fieldName + ") " + operatorStr + " " + value);
                                        } else {
                                            postconditions.add("this." + fieldName + " is modified");
                                        }
                                    } else if (value instanceof NameExpr &&
                                        methodDecl.getParameters().stream()
                                            .anyMatch(p -> p.getNameAsString().equals(value.toString()))) {
                                        postconditions.add("this." + fieldName + " == " + value);
                                    } else if (value instanceof BinaryExpr) {
                                        // Handle binary expressions with \old()
                                        String oldExpr = generateOldExpression(fieldName, (BinaryExpr) value, operator);
                                        if (oldExpr != null) {
                                            postconditions.add(oldExpr);
                                        } else {
                                            postconditions.add("this." + fieldName + " is modified");
                                        }
                                    }
                                }
                            });
                        });
                    });
            });
    }

    /**
     * Generates a postcondition with \old() expression for field modifications.
     * Examples:
     * - balance = balance + amount  →  "this.balance == \\old(this.balance) + amount"
     * - count += 1                  →  "this.count == \\old(this.count) + 1"
     * - size = size * 2            →  "this.size == \\old(this.size) * 2"
     */
    private String generateOldExpression(String fieldName, BinaryExpr binaryExpr, AssignExpr.Operator assignOp) {
        String left = binaryExpr.getLeft().toString();
        String right = binaryExpr.getRight().toString();
        BinaryExpr.Operator operator = binaryExpr.getOperator();

        // Check if the binary expression references the field being assigned
        boolean leftIsField = left.equals(fieldName) || left.equals("this." + fieldName);
        boolean rightIsField = right.equals(fieldName) || right.equals("this." + fieldName);

        // Handle compound assignments (+=, -=, *=, /=)
        if (assignOp != AssignExpr.Operator.ASSIGN) {
            String operatorStr = switch (assignOp) {
                case PLUS -> "+";
                case MINUS -> "-";
                case MULTIPLY -> "*";
                case DIVIDE -> "/";
                case REMAINDER -> "%";
                default -> null;
            };

            if (operatorStr != null) {
                // field += expr  →  this.field == \old(this.field) + expr
                return "this." + fieldName + " == \\old(this." + fieldName + ") " + operatorStr + " " + binaryExpr;
            }
        }

        // Handle regular binary expressions: field = field op expr
        if (leftIsField && !rightIsField) {
            // balance = balance + amount  →  this.balance == \old(this.balance) + amount
            String operatorStr = getOperatorString(operator);
            if (operatorStr != null) {
                return "this." + fieldName + " == \\old(this." + fieldName + ") " + operatorStr + " " + right;
            }
        } else if (rightIsField && !leftIsField) {
            // count = 1 + count  →  this.count == 1 + \old(this.count)
            String operatorStr = getOperatorString(operator);
            if (operatorStr != null) {
                return "this." + fieldName + " == " + left + " " + operatorStr + " \\old(this." + fieldName + ")";
            }
        }

        // If we can't generate a meaningful \old() expression, return null
        return null;
    }

    /**
     * Converts a BinaryExpr.Operator to its string representation.
     */
    private String getOperatorString(BinaryExpr.Operator operator) {
        return switch (operator) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            case DIVIDE -> "/";
            case REMAINDER -> "%";
            case AND -> "&&";
            case OR -> "||";
            default -> null;
        };
    }

    /**
     * Converts a compound AssignExpr.Operator to its string representation.
     */
    private String getCompoundOperatorString(AssignExpr.Operator operator) {
        return switch (operator) {
            case PLUS -> "+";
            case MINUS -> "-";
            case MULTIPLY -> "*";
            case DIVIDE -> "/";
            case REMAINDER -> "%";
            case BINARY_AND -> "&";
            case BINARY_OR -> "|";
            case XOR -> "^";
            case LEFT_SHIFT -> "<<";
            case SIGNED_RIGHT_SHIFT -> ">>";
            case UNSIGNED_RIGHT_SHIFT -> ">>>";
            default -> null;
        };
    }

    private boolean isCollectionType(String type) {
        return type.contains("List") || type.contains("Set") || type.contains("Collection") ||
               type.contains("Map") || type.contains("ArrayList") || type.contains("HashSet") ||
               type.contains("HashMap") || type.contains("LinkedList");
    }

    /**
     * Analyzes numeric return value bounds and relationships.
     */
    private void analyzeNumericReturnBounds(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        if (returnStmts.isEmpty()) {
            return;
        }

        // Track minimum value across all returns
        boolean allReturnsPositive = true;
        boolean allReturnsNonNegative = true;
        boolean allReturnsGreaterThanOne = true;

        for (ReturnStmt returnStmt : returnStmts) {
            if (returnStmt.getExpression().isEmpty()) {
                allReturnsNonNegative = false;
                allReturnsPositive = false;
                allReturnsGreaterThanOne = false;
                continue;
            }

            Expression expr = returnStmt.getExpression().get();

            // Check for literal values
            if (expr instanceof IntegerLiteralExpr) {
                int value = ((IntegerLiteralExpr) expr).asInt();
                if (value < 0) allReturnsNonNegative = false;
                if (value <= 0) allReturnsPositive = false;
                if (value <= 1) allReturnsGreaterThanOne = false;
            } else if (expr instanceof DoubleLiteralExpr) {
                double value = ((DoubleLiteralExpr) expr).asDouble();
                if (value < 0) allReturnsNonNegative = false;
                if (value <= 0) allReturnsPositive = false;
                if (value <= 1) allReturnsGreaterThanOne = false;
            } else if (expr instanceof MethodCallExpr) {
                // Check for operations that guarantee non-negative results
                MethodCallExpr call = (MethodCallExpr) expr;
                String methodName = call.getNameAsString();
                if (!methodName.equals("abs") && !methodName.equals("length") &&
                    !methodName.equals("size") && !methodName.equals("count")) {
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                }
            } else if (expr instanceof BinaryExpr) {
                BinaryExpr binExpr = (BinaryExpr) expr;
                if (binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                    // Multiplication doesn't guarantee non-negative unless we know operands
                    allReturnsNonNegative = false;
                    allReturnsPositive = false;
                    allReturnsGreaterThanOne = false;
                }
            } else if (!expr.isLiteralExpr()) {
                allReturnsNonNegative = false;
                allReturnsPositive = false;
                allReturnsGreaterThanOne = false;
            }
        }

        if (allReturnsGreaterThanOne && !postconditions.contains("\\result >= 0")) {
            postconditions.add("\\result >= 1");
        } else if (allReturnsNonNegative && !postconditions.contains("\\result >= 1")) {
            postconditions.add("\\result >= 0");
        } else if (allReturnsPositive) {
            postconditions.add("\\result > 0");
        }
    }

    /**
     * Analyzes relationship between return value and parameters.
     */
    private void analyzeReturnRelationToParameters(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                // Check for direct parameter return
                if (expr instanceof NameExpr) {
                    String exprName = expr.toString();
                    if (methodDecl.getParameters().stream()
                            .anyMatch(p -> p.getNameAsString().equals(exprName))) {
                        postconditions.add("\\result == " + exprName);
                    }
                }

                // Check for arithmetic operations with parameters
                if (expr instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) expr;
                    String left = binExpr.getLeft().toString();
                    String right = binExpr.getRight().toString();

                    boolean leftIsParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(left));
                    boolean rightIsParam = methodDecl.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(right));

                    if (leftIsParam && rightIsParam) {
                        // Both are parameters
                        switch (binExpr.getOperator()) {
                            case PLUS:
                                postconditions.add("\\result == " + left + " + " + right);
                                postconditions.add("\\result >= " + left);
                                postconditions.add("\\result >= " + right);
                                break;
                            case MINUS:
                                postconditions.add("\\result == " + left + " - " + right);
                                break;
                            case MULTIPLY:
                                postconditions.add("\\result == " + left + " * " + right);
                                break;
                            case DIVIDE:
                                postconditions.add("\\result == " + left + " / " + right);
                                break;
                        }
                    } else if (leftIsParam) {
                        // Left is parameter
                        switch (binExpr.getOperator()) {
                            case PLUS:
                                if (isPositiveLiteral(binExpr.getRight())) {
                                    postconditions.add("\\result > " + left);
                                }
                                break;
                            case MINUS:
                                if (isPositiveLiteral(binExpr.getRight())) {
                                    postconditions.add("\\result < " + left);
                                }
                                break;
                        }
                    } else if (rightIsParam) {
                        // Right is parameter
                        switch (binExpr.getOperator()) {
                            case PLUS:
                                if (isPositiveLiteral(binExpr.getLeft())) {
                                    postconditions.add("\\result > " + right);
                                }
                                break;
                        }
                    }
                }

                // Check for method calls on parameters
                if (expr instanceof MethodCallExpr) {
                    MethodCallExpr call = (MethodCallExpr) expr;
                    call.getScope().ifPresent(scope -> {
                        if (methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(scope.toString()))) {
                            String methodName = call.getNameAsString();
                            if (methodName.equals("length") || methodName.equals("size")) {
                                postconditions.add("\\result >= 0");
                            }
                        }
                    });
                }
            });
        }
    }

    /**
     * Analyzes String return value properties.
     */
    private void analyzeStringReturnProperties(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        boolean allReturnsNonNull = alwaysReturnsNonNull(methodDecl);
        if (allReturnsNonNull) {
            postconditions.add("\\result != null");
        }

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                // Check for StringBuilder/StringBuffer usage
                if (expr instanceof MethodCallExpr) {
                    MethodCallExpr call = (MethodCallExpr) expr;
                    if (call.getNameAsString().equals("toString")) {
                        call.getScope().ifPresent(scope -> {
                            if (scope.toString().contains("StringBuilder") ||
                                scope.toString().contains("StringBuffer")) {
                                postconditions.add("\\result != null");
                            }
                        });
                    }

                    // String manipulation methods
                    String methodName = call.getNameAsString();
                    call.getScope().ifPresent(scope -> {
                        String scopeStr = scope.toString();
                        if (methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(scopeStr) &&
                                               p.getType().asString().equals("String"))) {
                            switch (methodName) {
                                case "toUpperCase":
                                case "toLowerCase":
                                    postconditions.add("\\result.length() == " + scopeStr + ".length()");
                                    break;
                                case "trim":
                                    postconditions.add("\\result.length() <= " + scopeStr + ".length()");
                                    break;
                                case "substring":
                                    postconditions.add("\\result.length() <= " + scopeStr + ".length()");
                                    break;
                                case "replace":
                                case "replaceAll":
                                case "replaceFirst":
                                    postconditions.add("\\result != null");
                                    break;
                            }
                        }
                    });
                }

                // Check for empty string returns
                if (expr instanceof StringLiteralExpr) {
                    String value = ((StringLiteralExpr) expr).asString();
                    if (value.isEmpty()) {
                        postconditions.add("\\result.isEmpty() || \\result.length() > 0");
                    }
                }
            });
        }
    }

    /**
     * Analyzes Collection/Array return value properties.
     */
    private void analyzeCollectionReturnProperties(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                // Check for new ArrayList(), new HashSet(), etc.
                if (expr instanceof ObjectCreationExpr) {
                    ObjectCreationExpr creation = (ObjectCreationExpr) expr;
                    String type = creation.getType().asString();
                    if (isCollectionType(type)) {
                        postconditions.add("\\result != null");

                        // Check if it's created empty or with initial capacity
                        if (creation.getArguments().isEmpty()) {
                            postconditions.add("\\result.size() >= 0");
                        }
                    }
                }

                // Check for array creation
                if (expr instanceof ArrayCreationExpr) {
                    postconditions.add("\\result != null");
                    ArrayCreationExpr arrayCreation = (ArrayCreationExpr) expr;
                    arrayCreation.getLevels().forEach(level -> {
                        level.getDimension().ifPresent(dim -> {
                            if (methodDecl.getParameters().stream()
                                    .anyMatch(p -> p.getNameAsString().equals(dim.toString()))) {
                                postconditions.add("\\result.length == " + dim);
                            }
                        });
                    });
                }

                // Analyze collection operations in method body
                analyzeCollectionOperations(methodDecl, expr, postconditions);
            });
        }
    }

    private void analyzeCollectionOperations(MethodDeclaration methodDecl, Expression returnExpr, Set<String> postconditions) {
        // Find all local variable declarations that might be the returned collection
        methodDecl.findAll(VariableDeclarationExpr.class).forEach(varDecl -> {
            varDecl.getVariables().forEach(var -> {
                if (returnExpr.toString().equals(var.getNameAsString())) {
                    // This variable is returned, analyze operations on it
                    String varName = var.getNameAsString();

                    // Check for add/remove operations
                    boolean hasAdd = methodDecl.findAll(MethodCallExpr.class).stream()
                        .anyMatch(call -> call.getScope()
                            .map(s -> s.toString().equals(varName))
                            .orElse(false) && call.getNameAsString().equals("add"));

                    boolean hasRemove = methodDecl.findAll(MethodCallExpr.class).stream()
                        .anyMatch(call -> call.getScope()
                            .map(s -> s.toString().equals(varName))
                            .orElse(false) && call.getNameAsString().equals("remove"));

                    // Check if filtering from a parameter
                    methodDecl.getParameters().forEach(param -> {
                        String paramName = param.getNameAsString();
                        if (isCollectionType(param.getType().asString()) || param.getType().asString().contains("[]")) {
                            // Check if we're iterating over the parameter
                            boolean iteratesOverParam = methodDecl.findAll(ForEachStmt.class).stream()
                                .anyMatch(forEach -> forEach.getIterable().toString().equals(paramName));

                            if (iteratesOverParam && hasAdd && !hasRemove) {
                                // Likely a filter operation
                                if (param.getType().asString().contains("[]")) {
                                    postconditions.add("\\result.size() <= " + paramName + ".length");
                                } else {
                                    postconditions.add("\\result.size() <= " + paramName + ".size()");
                                }
                            }
                        }
                    });
                }
            });
        });
    }

    /**
     * Checks if a method returns 'this' (builder pattern).
     */
    private boolean returnsThis(MethodDeclaration methodDecl) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);
        if (returnStmts.isEmpty()) {
            return false;
        }

        return returnStmts.stream()
            .allMatch(ret -> ret.getExpression()
                .map(expr -> expr.isThisExpr() || expr.toString().equals("this"))
                .orElse(false));
    }

    /**
     * Analyzes factory method patterns.
     */
    private void analyzeFactoryMethodPattern(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                if (expr instanceof ObjectCreationExpr) {
                    ObjectCreationExpr creation = (ObjectCreationExpr) expr;
                    postconditions.add("\\result != null");
                    postconditions.add("\\result instanceof " + creation.getType().asString());
                }
            });
        }
    }

    /**
     * Analyzes comparison method patterns (compareTo, equals, hashCode).
     */
    private void analyzeComparisonMethodPattern(MethodDeclaration methodDecl, Set<String> postconditions) {
        String methodName = methodDecl.getNameAsString();

        if (methodName.equals("compareTo")) {
            if (methodDecl.getType().asString().equals("int")) {
                postconditions.add("\\result >= -1 && \\result <= 1 || \\result < -1 || \\result > 1");
                // More specifically: result can be any int, but often -1, 0, or 1
            }
        } else if (methodName.equals("equals")) {
            if (methodDecl.getType().asString().equals("boolean")) {
                // Equals should be reflexive
                if (methodDecl.getParameters().size() == 1) {
                    String paramName = methodDecl.getParameters().get(0).getNameAsString();
                    postconditions.add("(this.equals(" + paramName + ") ==> " + paramName + ".equals(this))");
                }
            }
        } else if (methodName.equals("hashCode")) {
            if (methodDecl.getType().asString().equals("int")) {
                postconditions.add("\\result == \\result");  // hashCode is deterministic
            }
        }
    }

    /**
     * Analyzes return value identity (same object returned).
     */
    private void analyzeReturnValueIdentity(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);
        String methodName = methodDecl.getNameAsString();

        // Check for getter pattern
        if (methodName.startsWith("get") && returnStmts.size() == 1) {
            returnStmts.get(0).getExpression().ifPresent(expr -> {
                if (expr instanceof FieldAccessExpr) {
                    FieldAccessExpr fieldAccess = (FieldAccessExpr) expr;
                    if (fieldAccess.getScope().toString().equals("this")) {
                        // This is a simple getter
                        postconditions.add("\\result == this." + fieldAccess.getNameAsString());
                    }
                } else if (expr instanceof NameExpr) {
                    // Might be a field without 'this.'
                    methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                        .ifPresent(classDecl -> {
                            String exprName = expr.toString();
                            classDecl.getFields().forEach(field -> {
                                field.getVariables().forEach(var -> {
                                    if (var.getNameAsString().equals(exprName)) {
                                        postconditions.add("\\result == this." + exprName);
                                    }
                                });
                            });
                        });
                }
            });
        }
    }

    /**
     * Analyzes parameter modifications (for mutable objects).
     */
    private void analyzeParameterModifications(MethodDeclaration methodDecl, Set<String> postconditions) {
        for (Parameter param : methodDecl.getParameters()) {
            String paramName = param.getNameAsString();
            String paramType = param.getType().asString();

            // Check for collection modifications
            if (isCollectionType(paramType)) {
                boolean hasAdd = methodDecl.findAll(MethodCallExpr.class).stream()
                    .anyMatch(call -> call.getScope()
                        .map(s -> s.toString().equals(paramName))
                        .orElse(false) && call.getNameAsString().equals("add"));

                boolean hasRemove = methodDecl.findAll(MethodCallExpr.class).stream()
                    .anyMatch(call -> call.getScope()
                        .map(s -> s.toString().equals(paramName))
                        .orElse(false) && call.getNameAsString().equals("remove"));

                boolean hasClear = methodDecl.findAll(MethodCallExpr.class).stream()
                    .anyMatch(call -> call.getScope()
                        .map(s -> s.toString().equals(paramName))
                        .orElse(false) && call.getNameAsString().equals("clear"));

                if (hasAdd) {
                    postconditions.add(paramName + ".size() >= \\old(" + paramName + ".size())");
                }
                if (hasRemove) {
                    postconditions.add(paramName + " is modified");
                }
                if (hasClear) {
                    postconditions.add(paramName + ".isEmpty()");
                }
            }

            // Check for array modifications
            if (paramType.contains("[]")) {
                boolean hasArrayWrite = methodDecl.findAll(AssignExpr.class).stream()
                    .anyMatch(assign -> assign.getTarget() instanceof ArrayAccessExpr &&
                        ((ArrayAccessExpr) assign.getTarget()).getName().toString().equals(paramName));

                if (hasArrayWrite) {
                    postconditions.add(paramName + " is modified");
                }
            }
        }
    }

    /**
     * Analyzes exception guarantees.
     */
    private void analyzeExceptionGuarantees(MethodDeclaration methodDecl, Set<String> postconditions) {
        // Check for explicit throws in method signature
        methodDecl.getThrownExceptions().forEach(throwsType -> {
            postconditions.add("may throw " + throwsType.asString());
        });

        // Check for throw statements in method body
        Set<String> thrownExceptions = new LinkedHashSet<>();
        methodDecl.findAll(ThrowStmt.class).forEach(throwStmt -> {
            throwStmt.getExpression().ifObjectCreationExpr(creation -> {
                thrownExceptions.add(creation.getType().asString());
            });
        });

        thrownExceptions.forEach(exceptionType -> {
            // Don't add this as a postcondition, as it's exceptional behavior
            // Could be handled separately if needed
        });
    }

    private boolean isPositiveLiteral(Expression expr) {
        if (expr instanceof IntegerLiteralExpr) {
            return ((IntegerLiteralExpr) expr).asInt() > 0;
        } else if (expr instanceof DoubleLiteralExpr) {
            return ((DoubleLiteralExpr) expr).asDouble() > 0;
        }
        return false;
    }

    /**
     * Analyzes method calls and propagates preconditions from called methods.
     * If a method calls another method with preconditions, those become requirements
     * for the calling method's parameters.
     */
    private void analyzeMethodCallPreconditions(MethodDeclaration methodDecl, Set<String> preconditions) {
        List<MethodCallExpr> methodCalls = methodDecl.findAll(MethodCallExpr.class);

        for (MethodCallExpr call : methodCalls) {
            String methodName = call.getNameAsString();

            // Build potential signatures to look up
            List<String> signatures = buildMethodSignatures(call);

            for (String signature : signatures) {
                MethodSpecification calledSpec = cache.get(signature);
                if (calledSpec != null && !calledSpec.getPreconditions().isEmpty()) {
                    logger.debug("Found cached spec for {}: {} preconditions", signature,
                            calledSpec.getPreconditions().size());

                    // Propagate preconditions from called method
                    for (String calledPrecond : calledSpec.getPreconditions()) {
                        String propagated = propagatePrecondition(call, calledPrecond, methodDecl);
                        if (propagated != null && !propagated.isEmpty()) {
                            preconditions.add(propagated);
                        }
                    }
                    break; // Found a match, stop looking
                }
            }
        }
    }

    /**
     * Analyzes method calls in return statements and propagates postconditions.
     * If a method directly returns the result of another method call, it inherits
     * that method's postconditions.
     */
    private void analyzeMethodCallPostconditions(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                if (expr instanceof MethodCallExpr) {
                    MethodCallExpr call = (MethodCallExpr) expr;

                    // Build potential signatures
                    List<String> signatures = buildMethodSignatures(call);

                    for (String signature : signatures) {
                        MethodSpecification calledSpec = cache.get(signature);
                        if (calledSpec != null && !calledSpec.getPostconditions().isEmpty()) {
                            logger.debug("Found cached spec for {}: {} postconditions", signature,
                                    calledSpec.getPostconditions().size());

                            // Propagate postconditions from called method
                            for (String calledPostcond : calledSpec.getPostconditions()) {
                                // If the called method ensures something about \result,
                                // our method inherits that
                                if (calledPostcond.contains("\\result")) {
                                    postconditions.add(calledPostcond);
                                } else if (calledPostcond.contains("!= null") && !calledPostcond.contains("this.")) {
                                    // Non-null guarantees apply to our result
                                    postconditions.add("\\result != null");
                                }
                            }
                            break;
                        }
                    }
                }
            });
        }
    }

    /**
     * Builds possible method signatures for a method call.
     * Tries multiple variations to handle different naming conventions.
     */
    private List<String> buildMethodSignatures(MethodCallExpr call) {
        List<String> signatures = new ArrayList<>();
        String methodName = call.getNameAsString();

        // Get argument count for simple matching
        int argCount = call.getArguments().size();

        // Try with scope (ClassName.methodName)
        call.getScope().ifPresent(scope -> {
            String scopeStr = scope.toString();
            // Remove 'this.' prefix if present
            if (scopeStr.equals("this")) {
                scopeStr = "";
            }
            if (!scopeStr.isEmpty()) {
                // Try with fully qualified scope
                signatures.add(scopeStr + "." + methodName);

                // Try with just class name (last part of scope)
                String[] parts = scopeStr.split("\\.");
                if (parts.length > 0) {
                    signatures.add(parts[parts.length - 1] + "." + methodName);
                }
            }
        });

        // Try without scope (just methodName)
        signatures.add(methodName);

        // Try with simple argument count signature
        signatures.add(methodName + "(" + argCount + ")");

        return signatures;
    }

    /**
     * Propagates a precondition from a called method to the calling method.
     * Maps parameter names from the called method to the actual arguments.
     */
    private String propagatePrecondition(MethodCallExpr call, String precondition,
                                         MethodDeclaration callingMethod) {
        // For now, do simple propagation
        // TODO: Could map parameter names to actual argument names for more precision

        // If the precondition is about a parameter being non-null,
        // and we pass a parameter to that position, we need that parameter non-null
        List<Expression> args = call.getArguments();

        // Simple heuristic: if precondition says "param != null" and we pass a parameter,
        // we need that parameter to be non-null
        for (int i = 0; i < args.size(); i++) {
            Expression arg = args.get(i);
            if (arg instanceof NameExpr) {
                String argName = arg.toString();

                // Check if this argument is a parameter of the calling method
                boolean isParameter = callingMethod.getParameters().stream()
                        .anyMatch(p -> p.getNameAsString().equals(argName));

                if (isParameter) {
                    // Check if precondition mentions null check
                    if (precondition.contains("!= null") && !precondition.startsWith("!")) {
                        return argName + " != null";
                    }
                    // Check for numeric constraints
                    if (precondition.matches(".*[><=].*\\d+.*")) {
                        // Try to substitute parameter name
                        // This is a simple version - could be more sophisticated
                        String[] tokens = precondition.split(" ");
                        if (tokens.length >= 3) {
                            // Format: paramName op value
                            return argName + " " + tokens[1] + " " + tokens[2];
                        }
                    }
                }
            }
        }

        return null;
    }

    /**
     * Phase 1: Infer method purity (@pure, @observer, @mutator).
     * Pure methods have no side effects and are deterministic.
     * Observers read state but don't modify it.
     * Mutators modify object state.
     */
    private void inferMethodPurity(MethodDeclaration methodDecl, MethodSpecification spec) {
        boolean hasFieldWrites = hasFieldWrites(methodDecl);
        boolean hasFieldReads = hasFieldReads(methodDecl);
        boolean performsIO = performsIO(methodDecl);
        boolean callsNonPureMethods = callsNonPureMethods(methodDecl);

        if (!hasFieldWrites && !hasFieldReads && !performsIO && !callsNonPureMethods) {
            // Pure: no field access, no I/O, only local operations
            spec.setPure(true);
        } else if (hasFieldReads && !hasFieldWrites && !performsIO) {
            // Observer: reads fields but doesn't modify
            spec.setObserver(true);
        } else if (hasFieldWrites) {
            // Mutator: modifies fields
            spec.setMutator(true);
        }
    }

    private boolean hasFieldWrites(MethodDeclaration methodDecl) {
        // Check for field assignments
        return !methodDecl.findAll(AssignExpr.class).stream()
                .filter(assign -> assign.getTarget() instanceof FieldAccessExpr ||
                               (assign.getTarget() instanceof NameExpr &&
                                isFieldReference(methodDecl, assign.getTarget().toString())))
                .toList().isEmpty();
    }

    private boolean hasFieldReads(MethodDeclaration methodDecl) {
        // Check for field accesses
        return !methodDecl.findAll(FieldAccessExpr.class).isEmpty() ||
               methodDecl.findAll(NameExpr.class).stream()
                       .anyMatch(ne -> isFieldReference(methodDecl, ne.getNameAsString()));
    }

    private boolean isFieldReference(MethodDeclaration methodDecl, String name) {
        // Check if name refers to a field (not a parameter or local variable)
        boolean isParameter = methodDecl.getParameters().stream()
                .anyMatch(p -> p.getNameAsString().equals(name));
        if (isParameter) return false;

        // Check if it's a local variable
        boolean isLocalVar = methodDecl.findAll(VariableDeclarationExpr.class).stream()
                .flatMap(vd -> vd.getVariables().stream())
                .anyMatch(v -> v.getNameAsString().equals(name));
        if (isLocalVar) return false;

        // Assume it's a field if not param or local
        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(c -> c.getFields().stream()
                        .flatMap(f -> f.getVariables().stream())
                        .anyMatch(v -> v.getNameAsString().equals(name)))
                .orElse(false);
    }

    private boolean performsIO(MethodDeclaration methodDecl) {
        // Check for I/O operations
        return methodDecl.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    String scope = call.getScope().map(Object::toString).orElse("");

                    // Common I/O method names
                    return methodName.equals("println") || methodName.equals("print") ||
                           methodName.equals("printf") || methodName.equals("read") ||
                           methodName.equals("write") || methodName.equals("readLine") ||
                           scope.contains("System.out") || scope.contains("System.err") ||
                           scope.contains("System.in") || scope.contains("File") ||
                           scope.contains("Stream") || scope.contains("Reader") ||
                           scope.contains("Writer");
                });
    }

    private boolean callsNonPureMethods(MethodDeclaration methodDecl) {
        // Check for calls to known non-pure methods
        return methodDecl.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    // Random, time, etc.
                    return methodName.equals("random") || methodName.equals("currentTimeMillis") ||
                           methodName.equals("nanoTime") || methodName.equals("nextInt") ||
                           methodName.equals("nextDouble");
                });
    }

    /**
     * Phase 1: Infer exception specifications (@signals).
     * Determines which exceptions are thrown and under what conditions.
     */
    private void inferExceptionSpecifications(MethodDeclaration methodDecl, MethodSpecification spec) {
        // Find all throw statements
        methodDecl.findAll(ThrowStmt.class).forEach(throwStmt -> {
            Expression thrownExpr = throwStmt.getExpression();
            String exceptionType = getExceptionType(thrownExpr);

            // Try to find the condition under which this exception is thrown
            throwStmt.findAncestor(IfStmt.class).ifPresent(ifStmt -> {
                String condition = getThrowCondition(ifStmt, throwStmt);
                if (condition != null && !condition.isEmpty()) {
                    spec.addExceptionSpecification(exceptionType + " when " + condition);
                } else {
                    spec.addExceptionSpecification(exceptionType);
                }
            });

            // If not inside an if statement, just record the exception type
            if (throwStmt.findAncestor(IfStmt.class).isEmpty()) {
                spec.addExceptionSpecification(exceptionType);
            }
        });

        // Check method signature for declared exceptions
        methodDecl.getThrownExceptions().forEach(thrownType -> {
            spec.addExceptionSpecification(thrownType.asString());
        });
    }

    private String getExceptionType(Expression thrownExpr) {
        if (thrownExpr instanceof ObjectCreationExpr) {
            ObjectCreationExpr objExpr = (ObjectCreationExpr) thrownExpr;
            return objExpr.getType().asString();
        }
        return "Exception";
    }

    private String getThrowCondition(IfStmt ifStmt, ThrowStmt throwStmt) {
        Expression condition = ifStmt.getCondition();

        // Check if throw is in then branch or else branch
        boolean inThenBranch = ifStmt.getThenStmt().containsWithinRange(throwStmt);

        if (inThenBranch) {
            // Throw happens when condition is true
            return condition.toString();
        } else {
            // Throw happens when condition is false
            return negateCondition(condition);
        }
    }

    private String negateCondition(Expression condition) {
        if (condition instanceof BinaryExpr) {
            BinaryExpr binExpr = (BinaryExpr) condition;
            BinaryExpr.Operator op = binExpr.getOperator();
            String left = binExpr.getLeft().toString();
            String right = binExpr.getRight().toString();

            return switch (op) {
                case EQUALS -> left + " != " + right;
                case NOT_EQUALS -> left + " == " + right;
                case LESS -> left + " >= " + right;
                case LESS_EQUALS -> left + " > " + right;
                case GREATER -> left + " <= " + right;
                case GREATER_EQUALS -> left + " < " + right;
                default -> "!(" + condition + ")";
            };
        }
        return "!(" + condition + ")";
    }

    /**
     * Phase 2: Infer assignable clauses (frame conditions).
     * Determines which memory locations may be modified.
     */
    private void inferAssignableClauses(MethodDeclaration methodDecl, MethodSpecification spec) {
        Set<String> assignedLocations = new LinkedHashSet<>();

        // Find all assignments
        methodDecl.findAll(AssignExpr.class).forEach(assign -> {
            Expression target = assign.getTarget();

            if (target instanceof FieldAccessExpr) {
                FieldAccessExpr fieldAccess = (FieldAccessExpr) target;
                String scope = fieldAccess.getScope().toString();
                String field = fieldAccess.getNameAsString();

                if (scope.equals("this")) {
                    assignedLocations.add("this." + field);
                } else {
                    assignedLocations.add(scope + "." + field);
                }
            } else if (target instanceof NameExpr) {
                String varName = target.toString();
                // Check if this is a field
                if (isFieldReference(methodDecl, varName)) {
                    assignedLocations.add("this." + varName);
                }
                // Otherwise it's a local variable, not part of assignable clause
            } else if (target instanceof ArrayAccessExpr) {
                ArrayAccessExpr arrayAccess = (ArrayAccessExpr) target;
                String arrayName = arrayAccess.getName().toString();
                assignedLocations.add(arrayName + "[*]");
            }
        });

        if (assignedLocations.isEmpty()) {
            // Nothing modified
            spec.addAssignableClause("\\nothing");
        } else {
            assignedLocations.forEach(spec::addAssignableClause);
        }
    }

    /**
     * Phase 3: Infer computational complexity (Big-O).
     */
    private void inferComplexity(MethodDeclaration methodDecl, MethodSpecification spec) {
        int loopNesting = calculateMaxLoopNesting(methodDecl);
        boolean hasRecursion = hasRecursion(methodDecl);

        String complexity;
        if (loopNesting == 0 && !hasRecursion) {
            complexity = "O(1)";
        } else if (loopNesting == 1 && !hasRecursion) {
            complexity = "O(n)";
        } else if (loopNesting == 2) {
            complexity = "O(n^2)";
        } else if (loopNesting == 3) {
            complexity = "O(n^3)";
        } else if (loopNesting > 3) {
            complexity = "O(n^" + loopNesting + ")";
        } else if (hasRecursion && hasDivideAndConquer(methodDecl)) {
            complexity = "O(n log n)";
        } else if (hasRecursion) {
            complexity = "O(2^n)"; // Exponential as conservative estimate
        } else {
            complexity = "O(n)";
        }

        spec.setTimeComplexity(complexity);

        // Space complexity (simplified)
        boolean allocatesArray = methodDecl.findAll(ArrayCreationExpr.class).stream()
                .anyMatch(ace -> !ace.getLevels().isEmpty());
        boolean allocatesCollection = methodDecl.findAll(ObjectCreationExpr.class).stream()
                .anyMatch(oce -> oce.getType().asString().contains("List") ||
                                 oce.getType().asString().contains("Set") ||
                                 oce.getType().asString().contains("Map"));

        if (allocatesArray || allocatesCollection) {
            spec.setSpaceComplexity("O(n)");
        } else if (hasRecursion) {
            spec.setSpaceComplexity("O(log n)"); // Recursion depth
        } else {
            spec.setSpaceComplexity("O(1)");
        }
    }

    private int calculateMaxLoopNesting(MethodDeclaration methodDecl) {
        return calculateLoopNestingRecursive(methodDecl);
    }

    private int calculateLoopNestingRecursive(com.github.javaparser.ast.Node node) {
        int maxNesting = 0;

        // Check if this node is a loop
        boolean isLoop = node instanceof ForStmt || node instanceof WhileStmt ||
                        node instanceof ForEachStmt || node instanceof DoStmt;

        if (isLoop) {
            // Find max nesting of children and add 1
            for (com.github.javaparser.ast.Node child : node.getChildNodes()) {
                int childNesting = calculateLoopNestingRecursive(child);
                maxNesting = Math.max(maxNesting, childNesting);
            }
            return maxNesting + 1;
        } else {
            // Not a loop, just recurse
            for (com.github.javaparser.ast.Node child : node.getChildNodes()) {
                int childNesting = calculateLoopNestingRecursive(child);
                maxNesting = Math.max(maxNesting, childNesting);
            }
            return maxNesting;
        }
    }

    private boolean hasRecursion(MethodDeclaration methodDecl) {
        String methodName = methodDecl.getNameAsString();
        return methodDecl.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> call.getNameAsString().equals(methodName));
    }

    private boolean hasDivideAndConquer(MethodDeclaration methodDecl) {
        // Look for patterns like divide in half (binary search, merge sort, etc.)
        return methodDecl.findAll(BinaryExpr.class).stream()
                .anyMatch(binExpr -> {
                    if (binExpr.getOperator() == BinaryExpr.Operator.DIVIDE) {
                        String right = binExpr.getRight().toString();
                        return right.equals("2");
                    }
                    return false;
                });
    }

    /**
     * Phase 3: Infer thread safety.
     */
    private void inferThreadSafety(MethodDeclaration methodDecl, MethodSpecification spec) {
        boolean isSynchronized = methodDecl.isSynchronized();
        boolean usesSynchronizedBlock = !methodDecl.findAll(SynchronizedStmt.class).isEmpty();
        boolean usesLocks = methodDecl.findAll(MethodCallExpr.class).stream()
                .anyMatch(call -> call.getNameAsString().equals("lock") ||
                                 call.getNameAsString().equals("unlock"));
        boolean usesConcurrentCollections = methodDecl.findAll(ObjectCreationExpr.class).stream()
                .anyMatch(oce -> oce.getType().asString().contains("Concurrent") ||
                                 oce.getType().asString().contains("Atomic"));

        // Check if all fields accessed are final
        boolean onlyFinalFields = checkOnlyFinalFields(methodDecl);

        if (isSynchronized || usesSynchronizedBlock || usesLocks || usesConcurrentCollections || onlyFinalFields) {
            spec.setThreadSafe(true);
        }
    }

    private boolean checkOnlyFinalFields(MethodDeclaration methodDecl) {
        // Find the enclosing class
        return methodDecl.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .map(classDecl -> {
                    // Get all field accesses in method
                    List<String> accessedFields = new ArrayList<>();

                    methodDecl.findAll(FieldAccessExpr.class).forEach(fae -> {
                        if (fae.getScope().toString().equals("this")) {
                            accessedFields.add(fae.getNameAsString());
                        }
                    });

                    methodDecl.findAll(NameExpr.class).forEach(ne -> {
                        if (isFieldReference(methodDecl, ne.getNameAsString())) {
                            accessedFields.add(ne.getNameAsString());
                        }
                    });

                    // Check if all accessed fields are final
                    return accessedFields.stream().allMatch(fieldName ->
                        classDecl.getFieldByName(fieldName)
                                .map(field -> field.isFinal())
                                .orElse(false)
                    );
                }).orElse(false);
    }

    /**
     * Visitor to detect null checks in the method body.
     */
    private static class NullCheckVisitor extends VoidVisitorAdapter<Void> {
        private final Set<String> nullChecks = new LinkedHashSet<>();

        @Override
        public void visit(IfStmt ifStmt, Void arg) {
            ifStmt.getCondition().ifBinaryExpr(binExpr -> {
                if (binExpr.getOperator() == BinaryExpr.Operator.EQUALS &&
                    (binExpr.getRight().isNullLiteralExpr() || binExpr.getLeft().isNullLiteralExpr())) {
                    Expression nonNullExpr = binExpr.getRight().isNullLiteralExpr() ? binExpr.getLeft() : binExpr.getRight();
                    nullChecks.add(nonNullExpr.toString() + " != null");
                } else if (binExpr.getOperator() == BinaryExpr.Operator.NOT_EQUALS &&
                          (binExpr.getRight().isNullLiteralExpr() || binExpr.getLeft().isNullLiteralExpr())) {
                    Expression nonNullExpr = binExpr.getRight().isNullLiteralExpr() ? binExpr.getLeft() : binExpr.getRight();
                    nullChecks.add(nonNullExpr.toString() + " != null");
                }
            });
            super.visit(ifStmt, arg);
        }

        public Set<String> getNullChecks() {
            return nullChecks;
        }
    }

    /**
     * Visitor to analyze loops and infer loop invariants.
     */
    private static class LoopInvariantVisitor extends VoidVisitorAdapter<Void> {
        private final Set<String> invariants = new LinkedHashSet<>();

        @Override
        public void visit(ForStmt forStmt, Void arg) {
            analyzeForLoop(forStmt);
            super.visit(forStmt, arg);
        }

        @Override
        public void visit(WhileStmt whileStmt, Void arg) {
            analyzeWhileLoop(whileStmt);
            super.visit(whileStmt, arg);
        }

        @Override
        public void visit(ForEachStmt forEachStmt, Void arg) {
            analyzeForEachLoop(forEachStmt);
            super.visit(forEachStmt, arg);
        }

        private void analyzeForLoop(ForStmt forStmt) {
            // Enhanced counter tracking
            List<String> counterNames = new ArrayList<>();
            List<Expression> initValues = new ArrayList<>();

            forStmt.getInitialization().stream()
                .filter(expr -> expr instanceof VariableDeclarationExpr)
                .forEach(expr -> {
                    VariableDeclarationExpr varDecl = (VariableDeclarationExpr) expr;
                    varDecl.getVariables().forEach(var -> {
                        String varName = var.getNameAsString();
                        counterNames.add(varName);
                        var.getInitializer().ifPresent(initValues::add);

                        // Enhanced: Check initialization value
                        var.getInitializer().ifPresent(init -> {
                            if (init.isIntegerLiteralExpr()) {
                                int initVal = init.asIntegerLiteralExpr().asInt();
                                invariants.add(varName + " >= " + initVal);
                            } else {
                                invariants.add(varName + " >= 0");
                            }
                        });

                        // Add upper bound from loop condition
                        forStmt.getCompare().ifPresent(compare -> {
                            if (compare instanceof BinaryExpr) {
                                BinaryExpr binExpr = (BinaryExpr) compare;
                                if (binExpr.getLeft().toString().equals(varName)) {
                                    invariants.add(varName + " " + getOperatorSymbol(binExpr.getOperator()) + " " + binExpr.getRight());
                                }
                            }
                        });

                        // Enhanced: Check step size in update expression
                        forStmt.getUpdate().forEach(updateExpr -> {
                            int stepSize = getStepSize(updateExpr, varName);
                            if (stepSize > 1) {
                                invariants.add(varName + " % " + stepSize + " == 0");
                            } else if (stepSize < 0) {
                                // Backward loop
                                forStmt.getCompare().ifPresent(compare -> {
                                    if (compare instanceof BinaryExpr) {
                                        BinaryExpr binExpr = (BinaryExpr) compare;
                                        if (binExpr.getLeft().toString().equals(varName)) {
                                            String lowerBound = binExpr.getRight().toString();
                                            invariants.add(varName + " >= " + lowerBound);
                                        }
                                    }
                                });
                            }
                        });
                    });
                });

            // Enhanced: Dual counter relationships
            if (counterNames.size() == 2) {
                String counter1 = counterNames.get(0);
                String counter2 = counterNames.get(1);

                // Check for i + j == constant pattern
                if (initValues.size() == 2) {
                    try {
                        int init1 = getIntValue(initValues.get(0));
                        int init2 = getIntValue(initValues.get(1));
                        int sum = init1 + init2;

                        // Check if both counters are updated in opposite directions
                        boolean oppositeUpdates = checkOppositeUpdates(forStmt, counter1, counter2);
                        if (oppositeUpdates) {
                            invariants.add(counter1 + " + " + counter2 + " == " + sum);
                        }
                    } catch (Exception e) {
                        // Couldn't determine constant sum
                    }
                }
            }

            // Enhanced: Accumulator analysis
            analyzeAccumulators(forStmt.getBody(), invariants, counterNames);

            // Enhanced: Array segment properties
            analyzeArraySegments(forStmt, invariants, counterNames);

            // Enhanced: Quantified invariants
            analyzeQuantifiedInvariants(forStmt, invariants, counterNames);

            // Enhanced: Variable relationships (max, min tracking)
            analyzeVariableRelationships(forStmt.getBody(), invariants);

            // Basic analysis
            analyzeLoopBodyForInvariants(forStmt.getBody(), invariants);
        }

        private int getStepSize(Expression updateExpr, String varName) {
            // Check i++, i--, i+=n, i-=n
            if (updateExpr instanceof UnaryExpr) {
                UnaryExpr unaryExpr = (UnaryExpr) updateExpr;
                if (unaryExpr.getExpression().toString().equals(varName)) {
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                        unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT) {
                        return 1;
                    } else if (unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_DECREMENT ||
                              unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_DECREMENT) {
                        return -1;
                    }
                }
            } else if (updateExpr instanceof AssignExpr) {
                AssignExpr assignExpr = (AssignExpr) updateExpr;
                if (assignExpr.getTarget().toString().equals(varName)) {
                    Expression value = assignExpr.getValue();
                    if (value instanceof BinaryExpr) {
                        BinaryExpr binExpr = (BinaryExpr) value;
                        if (binExpr.getLeft().toString().equals(varName)) {
                            if (binExpr.getOperator() == BinaryExpr.Operator.PLUS) {
                                try {
                                    return getIntValue(binExpr.getRight());
                                } catch (Exception e) {
                                    return 1;
                                }
                            } else if (binExpr.getOperator() == BinaryExpr.Operator.MINUS) {
                                try {
                                    return -getIntValue(binExpr.getRight());
                                } catch (Exception e) {
                                    return -1;
                                }
                            }
                        }
                    }
                }
            }
            return 1;
        }

        private int getIntValue(Expression expr) {
            if (expr.isIntegerLiteralExpr()) {
                return expr.asIntegerLiteralExpr().asInt();
            }
            throw new IllegalArgumentException("Not an integer literal");
        }

        private boolean checkOppositeUpdates(ForStmt forStmt, String counter1, String counter2) {
            int[] steps = new int[2];
            int index = 0;

            for (Expression updateExpr : forStmt.getUpdate()) {
                if (index < 2) {
                    if (updateExpr.toString().contains(counter1)) {
                        steps[0] = getStepSize(updateExpr, counter1);
                    } else if (updateExpr.toString().contains(counter2)) {
                        steps[1] = getStepSize(updateExpr, counter2);
                    }
                    index++;
                }
            }

            // Opposite if one is positive and one is negative
            return (steps[0] > 0 && steps[1] < 0) || (steps[0] < 0 && steps[1] > 0);
        }

        private void analyzeAccumulators(Statement body, Set<String> invariants, List<String> counterNames) {
            body.findAll(AssignExpr.class).forEach(assign -> {
                if (assign.getTarget() instanceof NameExpr) {
                    String varName = assign.getTarget().toString();

                    // Check if it's an accumulator (not a loop counter)
                    if (!counterNames.contains(varName)) {
                        Expression value = assign.getValue();

                        if (value instanceof BinaryExpr) {
                            BinaryExpr binExpr = (BinaryExpr) value;

                            // sum += x pattern
                            if (binExpr.getLeft().toString().equals(varName) &&
                                binExpr.getOperator() == BinaryExpr.Operator.PLUS) {
                                invariants.add(varName + " >= 0");

                                // Enhanced: Try to infer upper bound
                                if (!counterNames.isEmpty()) {
                                    String counter = counterNames.get(0);
                                    // sum <= i * maxValue
                                    invariants.add(varName + " <= " + counter + " * Integer.MAX_VALUE");
                                }
                            }

                            // count++ pattern (conditional)
                            if (binExpr.getOperator() == BinaryExpr.Operator.PLUS &&
                                binExpr.getRight().isIntegerLiteralExpr() &&
                                binExpr.getRight().asIntegerLiteralExpr().asInt() == 1) {

                                if (!counterNames.isEmpty()) {
                                    String counter = counterNames.get(0);
                                    invariants.add(varName + " >= 0");
                                    invariants.add(varName + " <= " + counter);
                                }
                            }
                        }
                    }
                }
            });
        }

        private void analyzeArraySegments(ForStmt forStmt, Set<String> invariants, List<String> counterNames) {
            if (counterNames.isEmpty()) return;
            String counter = counterNames.get(0);

            Statement body = forStmt.getBody();

            // Check for uniform array writes (all elements set to same value)
            List<AssignExpr> arrayWrites = body.findAll(AssignExpr.class).stream()
                    .filter(assign -> assign.getTarget() instanceof ArrayAccessExpr)
                    .toList();

            if (!arrayWrites.isEmpty()) {
                ArrayAccessExpr firstWrite = (ArrayAccessExpr) arrayWrites.get(0).getTarget();
                String arrayName = firstWrite.getName().toString();
                String index = firstWrite.getIndex().toString();

                // Check if all writes are to arr[i] where i is the counter
                boolean allWritesToCounter = arrayWrites.stream()
                        .allMatch(assign -> {
                            if (assign.getTarget() instanceof ArrayAccessExpr) {
                                ArrayAccessExpr aae = (ArrayAccessExpr) assign.getTarget();
                                return aae.getIndex().toString().equals(counter);
                            }
                            return false;
                        });

                if (allWritesToCounter && index.equals(counter)) {
                    // Check if all writes are the same value
                    Expression firstValue = arrayWrites.get(0).getValue();
                    boolean allSameValue = arrayWrites.stream()
                            .allMatch(assign -> assign.getValue().toString().equals(firstValue.toString()));

                    if (allSameValue) {
                        // Uniform initialization: (\forall int k; 0 <= k < i; arr[k] == value)
                        invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                      arrayName + "[k] == " + firstValue + ")");
                    }
                }

                // Check for swap pattern (might indicate sorting/partitioning)
                boolean hasSwap = body.findAll(MethodCallExpr.class).stream()
                        .anyMatch(call -> call.getNameAsString().equals("swap"));

                if (hasSwap) {
                    // Likely sorting algorithm, add generic segment property
                    invariants.add(arrayName + "[0.." + counter + "-1] processed");
                }
            }
        }

        private void analyzeQuantifiedInvariants(ForStmt forStmt, Set<String> invariants, List<String> counterNames) {
            if (counterNames.isEmpty()) return;
            String counter = counterNames.get(0);

            Statement body = forStmt.getBody();

            // Check for array initialization to zero/null
            body.findAll(AssignExpr.class).forEach(assign -> {
                if (assign.getTarget() instanceof ArrayAccessExpr) {
                    ArrayAccessExpr arrayAccess = (ArrayAccessExpr) assign.getTarget();
                    String arrayName = arrayAccess.getName().toString();
                    String index = arrayAccess.getIndex().toString();

                    if (index.equals(counter)) {
                        Expression value = assign.getValue();

                        if (value.isIntegerLiteralExpr() && value.asIntegerLiteralExpr().asInt() == 0) {
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == 0)");
                        } else if (value.isNullLiteralExpr()) {
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == null)");
                        } else if (value.isBooleanLiteralExpr()) {
                            boolean boolVal = value.asBooleanLiteralExpr().getValue();
                            invariants.add("(\\forall int k; 0 <= k < " + counter + "; " +
                                          arrayName + "[k] == " + boolVal + ")");
                        }
                    }
                }
            });

            // Check for counting pattern: count number of elements satisfying condition
            body.findAll(IfStmt.class).forEach(ifStmt -> {
                // Look for count++ inside if
                ifStmt.getThenStmt().findAll(UnaryExpr.class).forEach(unaryExpr -> {
                    if (unaryExpr.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT ||
                        unaryExpr.getOperator() == UnaryExpr.Operator.PREFIX_INCREMENT) {

                        String countVar = unaryExpr.getExpression().toString();
                        if (!counterNames.contains(countVar)) {
                            // This is a counting variable
                            String condition = ifStmt.getCondition().toString();
                            invariants.add("(\\num_of int k; 0 <= k < " + counter + "; " +
                                          condition.replace(counter, "k") + ") == " + countVar);
                        }
                    }
                });
            });
        }

        private void analyzeVariableRelationships(Statement body, Set<String> invariants) {
            // Check for max/min tracking patterns
            body.findAll(IfStmt.class).forEach(ifStmt -> {
                Expression condition = ifStmt.getCondition();

                // max pattern: if (x > max) max = x
                if (condition instanceof BinaryExpr) {
                    BinaryExpr binExpr = (BinaryExpr) condition;

                    if (binExpr.getOperator() == BinaryExpr.Operator.GREATER) {
                        String leftVar = binExpr.getLeft().toString();
                        String rightVar = binExpr.getRight().toString();

                        // Check if then statement assigns left to right
                        ifStmt.getThenStmt().findAll(AssignExpr.class).forEach(assign -> {
                            if (assign.getTarget().toString().equals(rightVar) &&
                                assign.getValue().toString().equals(leftVar)) {
                                // This is max tracking
                                invariants.add(rightVar + " is maximum of elements seen so far");
                            }
                        });
                    } else if (binExpr.getOperator() == BinaryExpr.Operator.LESS) {
                        String leftVar = binExpr.getLeft().toString();
                        String rightVar = binExpr.getRight().toString();

                        // Check for min pattern
                        ifStmt.getThenStmt().findAll(AssignExpr.class).forEach(assign -> {
                            if (assign.getTarget().toString().equals(rightVar) &&
                                assign.getValue().toString().equals(leftVar)) {
                                // This is min tracking
                                invariants.add(rightVar + " is minimum of elements seen so far");
                            }
                        });
                    }
                }
            });
        }

        private void analyzeWhileLoop(WhileStmt whileStmt) {
            Expression condition = whileStmt.getCondition();
            if (condition instanceof BinaryExpr) {
                BinaryExpr binExpr = (BinaryExpr) condition;
                invariants.add(binExpr.toString());
            }

            analyzeLoopBodyForInvariants(whileStmt.getBody(), invariants);
        }

        private void analyzeForEachLoop(ForEachStmt forEachStmt) {
            String varName = forEachStmt.getVariable().getVariable(0).getNameAsString();
            String iterableName = forEachStmt.getIterable().toString();

            invariants.add(varName + " != null");
            invariants.add(varName + " is element of " + iterableName);

            analyzeLoopBodyForInvariants(forEachStmt.getBody(), invariants);
        }

        private void analyzeLoopBodyForInvariants(Statement body, Set<String> invariants) {
            body.findAll(AssignExpr.class).stream()
                .filter(assign -> assign.getTarget() instanceof NameExpr)
                .forEach(assign -> {
                    String varName = assign.getTarget().toString();
                    if (assign.getValue() instanceof BinaryExpr) {
                        BinaryExpr binExpr = (BinaryExpr) assign.getValue();
                        if (binExpr.getOperator() == BinaryExpr.Operator.PLUS ||
                            binExpr.getOperator() == BinaryExpr.Operator.MULTIPLY) {
                            invariants.add(varName + " >= 0");
                        }
                    }
                });
        }

        private String getOperatorSymbol(BinaryExpr.Operator operator) {
            return switch (operator) {
                case LESS -> "<";
                case LESS_EQUALS -> "<=";
                case GREATER -> ">";
                case GREATER_EQUALS -> ">=";
                case EQUALS -> "==";
                case NOT_EQUALS -> "!=";
                default -> operator.asString();
            };
        }

        public Set<String> getInvariants() {
            return invariants;
        }
    }
}
