package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.jml.inferrer.model.MethodSpecification;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;

/**
 * Handles interprocedural analysis: propagating pre/postconditions from called methods.
 */
class InterproceduralAnalyzer {

    private static final Logger logger = LoggerFactory.getLogger(InterproceduralAnalyzer.class);
    private final SpecificationCache cache;

    InterproceduralAnalyzer(SpecificationCache cache) {
        this.cache = cache;
    }

    void analyzeMethodCallPreconditions(MethodDeclaration methodDecl, Set<String> preconditions) {
        List<MethodCallExpr> methodCalls = methodDecl.findAll(MethodCallExpr.class);

        for (MethodCallExpr call : methodCalls) {
            String methodName = call.getNameAsString();
            int argCount = call.getArguments().size();

            List<String> signatures = buildMethodSignatures(call);

            boolean found = false;
            for (String signature : signatures) {
                MethodSpecification calledSpec = cache.get(signature);
                if (calledSpec != null && !calledSpec.getPreconditions().isEmpty()) {
                    logger.debug("Found cached spec for {}: {} preconditions", signature,
                            calledSpec.getPreconditions().size());

                    for (String calledPrecond : calledSpec.getPreconditions()) {
                        String propagated = propagatePrecondition(call, calledPrecond, methodDecl);
                        if (propagated != null && !propagated.isEmpty()) {
                            preconditions.add(propagated);
                        }
                    }
                    found = true;
                    break;
                }
            }

            if (!found) {
                List<String> stdLibKeys = new ArrayList<>();
                call.getScope().ifPresent(scope -> {
                    String scopeStr = scope.toString();
                    String[] parts = scopeStr.split("\\.");
                    stdLibKeys.add(parts[parts.length - 1] + "." + methodName);
                });
                stdLibKeys.add(methodName);

                for (String key : stdLibKeys) {
                    List<String> stdPreconditions = StandardLibrarySpecs.getPreconditions(key, argCount);
                    if (!stdPreconditions.isEmpty()) {
                        logger.debug("Found standard library spec for {}: {} preconditions", key,
                                stdPreconditions.size());
                        for (String stdPrecond : stdPreconditions) {
                            String propagated = propagateStdLibPrecondition(call, stdPrecond, methodDecl);
                            if (propagated != null && !propagated.isEmpty()) {
                                preconditions.add(propagated);
                            }
                        }
                        break;
                    }
                }
            }
        }
    }

    String propagateStdLibPrecondition(MethodCallExpr call, String precondition,
                                       MethodDeclaration callingMethod) {
        List<Expression> args = call.getArguments();
        List<Parameter> callingParams = callingMethod.getParameters();
        Set<String> paramNames = new HashSet<>();
        for (Parameter p : callingParams) {
            paramNames.add(p.getNameAsString());
        }

        String result = precondition;

        if (args.size() >= 2) {
            String secondArg = args.get(1).toString();
            result = result.replaceAll("\\bendIndex\\b", java.util.regex.Matcher.quoteReplacement(secondArg))
                           .replaceAll("\\bnewLength\\b", java.util.regex.Matcher.quoteReplacement(secondArg));
        }
        if (args.size() >= 1) {
            String firstArg = args.get(0).toString();
            String quoted = java.util.regex.Matcher.quoteReplacement(firstArg);
            result = result.replaceAll("\\bbeginIndex\\b", quoted)
                           .replaceAll("\\boriginal\\b", quoted)
                           .replaceAll("\\bindex\\b", quoted)
                           .replaceAll("\\blist\\b", quoted)
                           .replaceAll("\\bstr\\b", quoted)
                           .replaceAll("\\bobj\\b", quoted)
                           .replaceAll("(?<=\\W|^)s(?=\\W|$)", quoted);
        }

        call.getScope().ifPresent(scope -> {
            // Can't modify result in lambda directly, handled below
        });
        if (call.getScope().isPresent()) {
            String scopeStr = call.getScope().get().toString();
            result = result.replace("this.", scopeStr + ".");
        }

        for (Parameter p : callingParams) {
            if (result.contains(p.getNameAsString())) {
                return result;
            }
        }

        if (result.contains("this.") || result.contains(".size()") || result.contains(".length")) {
            return result;
        }

        return null;
    }

    void analyzeMethodCallPostconditions(MethodDeclaration methodDecl, Set<String> postconditions) {
        List<ReturnStmt> returnStmts = methodDecl.findAll(ReturnStmt.class);

        for (ReturnStmt returnStmt : returnStmts) {
            returnStmt.getExpression().ifPresent(expr -> {
                if (expr instanceof MethodCallExpr) {
                    MethodCallExpr call = (MethodCallExpr) expr;
                    String methodName = call.getNameAsString();
                    int argCount = call.getArguments().size();

                    List<String> signatures = buildMethodSignatures(call);

                    boolean found = false;
                    for (String signature : signatures) {
                        MethodSpecification calledSpec = cache.get(signature);
                        if (calledSpec != null && !calledSpec.getPostconditions().isEmpty()) {
                            logger.debug("Found cached spec for {}: {} postconditions", signature,
                                    calledSpec.getPostconditions().size());

                            for (String calledPostcond : calledSpec.getPostconditions()) {
                                if (calledPostcond.contains("\\result")) {
                                    postconditions.add(calledPostcond);
                                } else if (calledPostcond.contains("!= null") && !calledPostcond.contains("this.")) {
                                    postconditions.add("\\result != null");
                                }
                            }
                            found = true;
                            break;
                        }
                    }

                    if (!found) {
                        List<String> stdLibKeys = new ArrayList<>();
                        call.getScope().ifPresent(scope -> {
                            String scopeStr = scope.toString();
                            String[] parts = scopeStr.split("\\.");
                            stdLibKeys.add(parts[parts.length - 1] + "." + methodName);
                        });
                        stdLibKeys.add(methodName);

                        for (String key : stdLibKeys) {
                            List<String> stdPostconditions = StandardLibrarySpecs.getPostconditions(key, argCount);
                            if (!stdPostconditions.isEmpty()) {
                                logger.debug("Found standard library spec for {}: {} postconditions", key,
                                        stdPostconditions.size());
                                for (String stdPostcond : stdPostconditions) {
                                    if (stdPostcond.contains("\\result")) {
                                        postconditions.add(stdPostcond);
                                    } else if (stdPostcond.contains("!= null") && !stdPostcond.contains("this.")) {
                                        postconditions.add("\\result != null");
                                    }
                                }
                                break;
                            }
                        }
                    }
                }
            });
        }
    }

    List<String> buildMethodSignatures(MethodCallExpr call) {
        List<String> signatures = new ArrayList<>();
        String methodName = call.getNameAsString();
        int argCount = call.getArguments().size();

        call.getScope().ifPresent(scope -> {
            String scopeStr = scope.toString();
            if (scopeStr.equals("this")) {
                scopeStr = "";
            }
            if (!scopeStr.isEmpty()) {
                signatures.add(scopeStr + "." + methodName);
                String[] parts = scopeStr.split("\\.");
                if (parts.length > 0) {
                    signatures.add(parts[parts.length - 1] + "." + methodName);
                }
            }
        });

        signatures.add(methodName);
        signatures.add(methodName + "(" + argCount + ")");

        return signatures;
    }

    String propagatePrecondition(MethodCallExpr call, String precondition,
                                 MethodDeclaration callingMethod) {
        List<Expression> args = call.getArguments();
        List<Parameter> callingParams = callingMethod.getParameters();

        String calleeSignature = buildCalleeSignatureForLookup(call);
        MethodSpecification calledSpec = cache.get(calleeSignature);

        String paramInPrecondition = extractParameterName(precondition);
        if (paramInPrecondition == null) {
            return null;
        }

        // Strategy 1: Direct positional mapping
        for (int i = 0; i < args.size(); i++) {
            Expression arg = args.get(i);

            if (arg instanceof NameExpr) {
                String argName = arg.toString();

                boolean isParameter = callingParams.stream()
                        .anyMatch(p -> p.getNameAsString().equals(argName));

                if (isParameter) {
                    String substituted = substituteParameterInPrecondition(precondition, paramInPrecondition, argName);
                    if (substituted != null) {
                        return substituted;
                    }
                }
            }
        }

        // Strategy 2: Match by type similarity
        for (int i = 0; i < args.size(); i++) {
            Expression arg = args.get(i);

            if (arg instanceof NameExpr) {
                String argName = arg.toString();

                Optional<Parameter> callingParam = callingParams.stream()
                        .filter(p -> p.getNameAsString().equals(argName))
                        .findFirst();

                if (callingParam.isPresent()) {
                    String argType = callingParam.get().getType().asString();

                    if (preconditionMatchesType(precondition, argType)) {
                        String substituted = substituteParameterInPrecondition(precondition, paramInPrecondition, argName);
                        if (substituted != null) {
                            return substituted;
                        }
                    }
                }
            }
        }

        return null;
    }

    String extractParameterName(String precondition) {
        String[] tokens = precondition.split("\\s+|\\.");
        if (tokens.length > 0) {
            String first = tokens[0];
            if (first.equals("!") && tokens.length > 1) {
                first = tokens[1];
            }
            if (first.matches("[a-zA-Z_][a-zA-Z0-9_]*")) {
                return first;
            }
        }
        return null;
    }

    String substituteParameterInPrecondition(String precondition, String oldParam, String newParam) {
        String result = precondition.replaceAll("\\b" + oldParam + "\\b", newParam);
        return result.equals(precondition) ? null : result;
    }

    boolean preconditionMatchesType(String precondition, String type) {
        boolean isReferenceType = AnalysisUtils.isReferenceType(type);
        boolean isNumericType = type.equals("int") || type.equals("long") || type.equals("double") ||
                type.equals("float") || type.equals("Integer") || type.equals("Long") ||
                type.equals("Double") || type.equals("Float") || type.equals("short") || type.equals("byte");
        boolean isStringType = type.equals("String");
        boolean isArrayType = type.contains("[]");
        boolean isCollectionType = AnalysisUtils.isCollectionType(type);

        if (precondition.contains("!= null") || precondition.contains("== null")) {
            return isReferenceType;
        }

        if (precondition.matches(".*[<>]=?\\s*\\d+.*") || precondition.matches(".*\\d+\\s*[<>]=?.*")) {
            return isNumericType;
        }

        if (precondition.contains(".isEmpty()") || precondition.contains(".length()")) {
            return isStringType || isCollectionType || isArrayType;
        }

        if (precondition.contains(".size()")) {
            return isCollectionType;
        }

        return false;
    }

    String buildCalleeSignatureForLookup(MethodCallExpr call) {
        StringBuilder signature = new StringBuilder();

        call.getScope().ifPresent(scope -> {
            String scopeStr = scope.toString();
            if (!scopeStr.equals("this") && !scopeStr.equals("super")) {
                signature.append(scopeStr).append(".");
            }
        });

        signature.append(call.getNameAsString());
        return signature.toString();
    }
}
