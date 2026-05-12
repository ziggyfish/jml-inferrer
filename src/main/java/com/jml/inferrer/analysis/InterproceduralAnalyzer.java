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

    void analyzeMethodCallPreconditions(MethodDeclaration methodDecl, Set<String> preconditions,
                                         ASTCollector collector) {
        List<MethodCallExpr> methodCalls = collector.methodCallExprs;

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

                    // Look up the callee's parameter names so we can substitute them with the
                    // actual call arguments. The older propagatePrecondition() path infers the
                    // parameter name from the precondition string itself, which fails for
                    // forms like `((\bigint) x * (\bigint) x) <= Integer.MAX_VALUE` where the
                    // identifier x is not the first token. Mirroring the postcondition path
                    // (line ~254) gives us the parameter names directly from the AST.
                    MethodDeclaration calleeDecl = findCalleeDecl(methodDecl, signature);
                    List<String> calleeParamNames = new ArrayList<>();
                    if (calleeDecl != null) {
                        calleeDecl.getParameters().forEach(p ->
                                calleeParamNames.add(p.getNameAsString()));
                    }

                    Set<String> callerParamNames = new HashSet<>();
                    methodDecl.getParameters().forEach(p ->
                            callerParamNames.add(p.getNameAsString()));

                    for (String calledPrecond : calledSpec.getPreconditions()) {
                        String propagated = null;
                        if (!calleeParamNames.isEmpty()
                                && call.getArguments().size() == calleeParamNames.size()) {
                            String rewritten = substituteNamedParams(calledPrecond, calleeParamNames,
                                    call.getArguments());
                            // Only keep the propagated precondition if it remains pre-state
                            // expressible from the caller's perspective (caller parameters or
                            // class fields). This mirrors the scope-safety guard in
                            // propagateStdLibPrecondition.
                            SymbolicExecutor scopeCheck = new SymbolicExecutor();
                            if (scopeCheck.isMethodScopeSafe(rewritten, methodDecl, callerParamNames)) {
                                propagated = rewritten;
                            }
                        }
                        if (propagated == null) {
                            // Fall back to the legacy heuristic when the callee's parameter
                            // names are not available (e.g. for callees discovered via the
                            // signature-only path).
                            propagated = propagatePrecondition(call, calledPrecond, methodDecl);
                        }
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

    /**
     * Substitutes the canonical placeholder parameter names used in
     * {@link StandardLibrarySpecs} (e.g. {@code a}, {@code b}, {@code index}) with the
     * actual argument expressions at the call site. The names below match the set used
     * when defining stdlib specs in that class.
     */
    /**
     * Substitutes each name in {@code paramNames} with the corresponding stringified
     * argument from {@code args}. Uses word-boundary regex so nested occurrences
     * (e.g. {@code abs(a)} within a larger expression) don't double-substitute.
     * JML keyword references like {@code \result} are left untouched.
     */
    private String substituteNamedParams(String spec, List<String> paramNames,
                                          List<Expression> args) {
        String result = spec;
        for (int i = 0; i < paramNames.size() && i < args.size(); i++) {
            String quoted = java.util.regex.Matcher.quoteReplacement(args.get(i).toString());
            result = result.replaceAll("\\b" + java.util.regex.Pattern.quote(paramNames.get(i)) + "\\b",
                    quoted);
        }
        return result;
    }

    /**
     * Finds the callee's MethodDeclaration in the same CompilationUnit as
     * {@code caller}, by method signature {@code signature}. Matches on name and
     * enclosing class when the signature is of the form {@code ClassName.method},
     * or just method name otherwise. Returns null if not found.
     */
    private MethodDeclaration findCalleeDecl(MethodDeclaration caller, String signature) {
        if (caller.findCompilationUnit().isEmpty()) return null;
        String[] parts = signature.split("\\.");
        String methodName = parts[parts.length - 1];
        String className = parts.length > 1 ? parts[parts.length - 2] : null;
        for (MethodDeclaration md : caller.findCompilationUnit().get()
                .findAll(MethodDeclaration.class)) {
            if (!md.getNameAsString().equals(methodName)) continue;
            if (className != null) {
                var owner = md.findAncestor(
                        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class);
                if (owner.isEmpty() || !owner.get().getNameAsString().equals(className)) continue;
            }
            return md;
        }
        return null;
    }

    private String substitutePlaceholderArgs(String spec, List<Expression> args) {
        String result = spec;
        if (args.size() >= 1) {
            String q = java.util.regex.Matcher.quoteReplacement(args.get(0).toString());
            result = result.replaceAll("\\ba\\b", q)
                           .replaceAll("\\bindex\\b", q)
                           .replaceAll("\\bbeginIndex\\b", q)
                           .replaceAll("\\boriginal\\b", q)
                           .replaceAll("\\blist\\b", q)
                           .replaceAll("\\bstr\\b", q)
                           .replaceAll("\\bobj\\b", q);
        }
        if (args.size() >= 2) {
            String q = java.util.regex.Matcher.quoteReplacement(args.get(1).toString());
            result = result.replaceAll("\\bb\\b", q)
                           .replaceAll("\\bendIndex\\b", q)
                           .replaceAll("\\bnewLength\\b", q);
        }
        return result;
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
            String quoted2 = java.util.regex.Matcher.quoteReplacement(secondArg);
            result = result.replaceAll("\\bendIndex\\b", quoted2)
                           .replaceAll("\\bnewLength\\b", quoted2)
                           .replaceAll("\\bb\\b", quoted2);
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
                           .replaceAll("\\ba\\b", quoted);
            // Note: a bare `s` substitution was previously here but it also matched the
            // parameter `s` inside an argument like `s.length() - 1`, producing nonsense
            // like `s.length() - 1.length() - 1`. If a stdlib spec needs to refer to the
            // first arg by the name `s`, add `\\bs\\b` — but most don't.
        }

        call.getScope().ifPresent(scope -> {
            // Can't modify result in lambda directly, handled below
        });
        if (call.getScope().isPresent()) {
            String scopeStr = call.getScope().get().toString();
            result = result.replace("this.", scopeStr + ".");
        }

        // Reject the propagated precondition if any identifier in it isn't pre-state-
        // expressible (e.g., loop variable `i` from inside a method body). We'd produce
        // a "cannot find symbol" parse error in OpenJML otherwise.
        SymbolicExecutor scopeCheck = new SymbolicExecutor();
        if (!scopeCheck.isMethodScopeSafe(result, callingMethod, paramNames)) {
            return null;
        }

        // Reject `<primitive> != null` produced by substituting a primitive argument into
        // a stdlib spec written for the reference-type overload. Example: `String.indexOf`
        // has both `(int)` and `(String)` overloads but only the latter is in the spec
        // table; calling `s.indexOf(c)` with `char c` produces `c != null`, an invalid JML
        // type comparison that errors out in OpenJML.
        if (result.contains("!= null")) {
            for (Parameter p : callingParams) {
                if (p.getType().isPrimitiveType()) {
                    String primitiveName = p.getNameAsString();
                    if (result.matches(".*\\b" + java.util.regex.Pattern.quote(primitiveName)
                            + "\\s*!=\\s*null.*")) {
                        return null;
                    }
                }
            }
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

    void analyzeMethodCallPostconditions(MethodDeclaration methodDecl, Set<String> postconditions,
                                          ASTCollector collector) {
        List<ReturnStmt> returnStmts = collector.returnStmts;

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

                            // Look up the callee's parameter names so we can substitute them
                            // with the actual call arguments. Without this the cached
                            // postcondition `a >= b ==> \result == a` from the callee `max(a, b)`
                            // gets propagated into `maxAbs(a, b) { return max(abs(a), abs(b)); }`
                            // verbatim — but `a` in the caller is not `max`'s `a` (which is
                            // actually `abs(caller_a)`). The result is a false postcondition.
                            MethodDeclaration calleeDecl = findCalleeDecl(methodDecl, signature);
                            List<String> calleeParamNames = new ArrayList<>();
                            if (calleeDecl != null) {
                                calleeDecl.getParameters().forEach(p ->
                                        calleeParamNames.add(p.getNameAsString()));
                            }

                            for (String calledPostcond : calledSpec.getPostconditions()) {
                                String rewritten = calledPostcond;
                                if (!calleeParamNames.isEmpty()
                                        && call.getArguments().size() == calleeParamNames.size()) {
                                    rewritten = substituteNamedParams(rewritten, calleeParamNames,
                                            call.getArguments());
                                }
                                if (rewritten.contains("\\result")) {
                                    postconditions.add(rewritten);
                                } else if (rewritten.contains("!= null") && !rewritten.contains("this.")) {
                                    postconditions.add("\\result != null");
                                }
                            }
                            found = true;
                            break;
                        }
                    }

                    if (!found) {
                        List<String> stdLibKeys = new ArrayList<>();
                        String[] scopeRef = new String[]{null};
                        call.getScope().ifPresent(scope -> {
                            String scopeStr = scope.toString();
                            scopeRef[0] = scopeStr;
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
                                    String rewritten = stdPostcond;
                                    // Substitute placeholder parameter names (a, b, obj, ...) with the
                                    // actual argument expressions at the call site. Standard library
                                    // specs are written with canonical names like `a`, `b` that must
                                    // resolve to the caller's scope.
                                    rewritten = substitutePlaceholderArgs(rewritten, call.getArguments());
                                    // `this` in a stdlib spec refers to the receiver of the call,
                                    // not the enclosing class. For `s.trim()`, rewrite `this.length()`
                                    // as `s.length()` so the spec resolves correctly.
                                    if (scopeRef[0] != null && !scopeRef[0].equals("this")
                                            && rewritten.contains("this.")) {
                                        rewritten = rewritten.replace("this.", scopeRef[0] + ".");
                                    }
                                    Set<String> callerParams = new HashSet<>();
                                    methodDecl.getParameters().forEach(p -> callerParams.add(p.getNameAsString()));
                                    SymbolicExecutor scopeCheck = new SymbolicExecutor();
                                    if (!scopeCheck.isMethodScopeSafe(rewritten, methodDecl, callerParams)) {
                                        continue;
                                    }
                                    if (rewritten.contains("\\result")) {
                                        postconditions.add(rewritten);
                                    } else if (rewritten.contains("!= null") && !rewritten.contains("this.")) {
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

        // For unqualified calls (square(a) inside the same class), the cache key
        // is `EnclosingClass.methodName`. Find the enclosing class via the call's
        // ancestry so we hit the cache that JMLInferenceVisitor populated.
        call.findAncestor(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class)
                .ifPresent(cls -> signatures.add(cls.getNameAsString() + "." + methodName));

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
