package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.jml.inferrer.model.MethodSpecification;

/**
 * Infers method purity (@pure, @observer, @mutator).
 */
class PurityAnalyzer {

    void inferMethodPurity(MethodDeclaration methodDecl, MethodSpecification spec, ASTCollector collector) {
        boolean hasFieldWrites = hasFieldWrites(methodDecl, collector);
        boolean hasFieldReads = hasFieldReads(methodDecl, collector);
        boolean performsIO = performsIO(collector);
        boolean callsNonPureMethods = callsNonPureMethods(collector);

        if (!hasFieldWrites && !hasFieldReads && !performsIO && !callsNonPureMethods) {
            spec.setPure(true);
        } else if (hasFieldReads && !hasFieldWrites && !performsIO) {
            spec.setObserver(true);
        } else if (hasFieldWrites) {
            spec.setMutator(true);
        }
    }

    boolean hasFieldWrites(MethodDeclaration methodDecl, ASTCollector collector) {
        // Writes to fields OR to elements of any externally-visible array (instance
        // field or parameter) are both non-pure: the caller can observe the mutation.
        // Writes through a local variable (e.g. `c.field = 5` where c is a fresh/local
        // reference) are NOT observable externally, so they stay pure.
        java.util.Set<String> localVarNames = new java.util.HashSet<>();
        collector.varDeclExprs.forEach(vde -> vde.getVariables()
                .forEach(v -> localVarNames.add(v.getNameAsString())));

        boolean directWrite = collector.assignExprs.stream().anyMatch(assign -> {
            Expression target = assign.getTarget();
            if (target instanceof FieldAccessExpr fae) {
                String scope = fae.getScope().toString();
                if (localVarNames.contains(scope)) return false;
                return true;
            }
            if (target instanceof NameExpr) {
                return AnalysisUtils.isFieldReference(methodDecl, target.toString());
            }
            if (target instanceof ArrayAccessExpr aa) {
                return AssignableAnalyzer.extractArrayBase(aa, methodDecl) != null;
            }
            return false;
        });
        if (directWrite) return true;

        return collector.unaryExprs.stream().anyMatch(u -> {
            switch (u.getOperator()) {
                case POSTFIX_INCREMENT:
                case POSTFIX_DECREMENT:
                case PREFIX_INCREMENT:
                case PREFIX_DECREMENT:
                    Expression e = u.getExpression();
                    if (e instanceof FieldAccessExpr fae) {
                        String scope = fae.getScope().toString();
                        if (localVarNames.contains(scope)) return false;
                        return true;
                    }
                    if (e instanceof NameExpr) {
                        return AnalysisUtils.isFieldReference(methodDecl, e.toString());
                    }
                    if (e instanceof ArrayAccessExpr aae) {
                        // Writing to an array element — always a side effect on the array
                        return AssignableAnalyzer.extractArrayBase(aae, methodDecl) != null;
                    }
                    return false;
                default:
                    return false;
            }
        });
    }

    private boolean isParameterArray(ArrayAccessExpr access, MethodDeclaration methodDecl) {
        Expression name = access.getName();
        while (name instanceof ArrayAccessExpr inner) {
            name = inner.getName();
        }
        if (name instanceof NameExpr ne) {
            String varName = ne.getNameAsString();
            return methodDecl.getParameters().stream()
                    .anyMatch(p -> p.getNameAsString().equals(varName));
        }
        return false;
    }

    boolean hasFieldReads(MethodDeclaration methodDecl, ASTCollector collector) {
        // A FieldAccessExpr whose scope is a parameter or local (e.g. arr.length on a parameter)
        // is NOT a read of an instance field — don't let it block @pure.
        boolean realFieldAccess = collector.fieldAccessExprs.stream()
                .anyMatch(fa -> {
                    String scope = fa.getScope().toString();
                    if (scope.equals("this")) return true;
                    // scope is some name — only treat as field read if it isn't a param/local
                    if (fa.getScope() instanceof NameExpr ne) {
                        String varName = ne.getNameAsString();
                        boolean isParam = methodDecl.getParameters().stream()
                                .anyMatch(p -> p.getNameAsString().equals(varName));
                        if (isParam) return false;
                        boolean isLocal = methodDecl.findAll(VariableDeclarationExpr.class).stream()
                                .flatMap(vd -> vd.getVariables().stream())
                                .anyMatch(v -> v.getNameAsString().equals(varName));
                        if (isLocal) return false;
                    }
                    return true;
                });
        if (realFieldAccess) return true;

        return collector.nameExprs.stream()
                .anyMatch(ne -> AnalysisUtils.isFieldReference(methodDecl, ne.getNameAsString()));
    }

    boolean performsIO(ASTCollector collector) {
        return collector.methodCallExprs.stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    String scope = call.getScope().map(Object::toString).orElse("");

                    return methodName.equals("println") || methodName.equals("print") ||
                           methodName.equals("printf") || methodName.equals("read") ||
                           methodName.equals("write") || methodName.equals("readLine") ||
                           scope.contains("System.out") || scope.contains("System.err") ||
                           scope.contains("System.in") || scope.contains("File") ||
                           scope.contains("Stream") || scope.contains("Reader") ||
                           scope.contains("Writer");
                });
    }

    boolean callsNonPureMethods(ASTCollector collector) {
        return collector.methodCallExprs.stream()
                .anyMatch(call -> {
                    String methodName = call.getNameAsString();
                    return methodName.equals("random") || methodName.equals("currentTimeMillis") ||
                           methodName.equals("nanoTime") || methodName.equals("nextInt") ||
                           methodName.equals("nextDouble");
                });
    }
}
