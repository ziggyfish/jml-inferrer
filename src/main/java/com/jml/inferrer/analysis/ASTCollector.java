package com.jml.inferrer.analysis;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.ArrayList;
import java.util.List;

/**
 * Single-pass AST collector that visits a method body once and categorizes
 * all nodes into typed lists. This replaces redundant {@code findAll()} calls
 * across all analyzers with a single DFS traversal.
 *
 * <p>The visitor traverses in DFS order, matching the order produced by
 * {@code Node.findAll()}, so collected lists are drop-in replacements.</p>
 *
 * <p>Usage: create one instance via {@link #collect(MethodDeclaration)} in the facade
 * ({@link MethodSpecificationInferrer#inferSpecification}), then pass it to all sub-analyzers.</p>
 */
class ASTCollector extends VoidVisitorAdapter<Void> {

    // Expressions
    final List<BinaryExpr> binaryExprs = new ArrayList<>();
    final List<MethodCallExpr> methodCallExprs = new ArrayList<>();
    final List<FieldAccessExpr> fieldAccessExprs = new ArrayList<>();
    final List<NameExpr> nameExprs = new ArrayList<>();
    final List<AssignExpr> assignExprs = new ArrayList<>();
    final List<UnaryExpr> unaryExprs = new ArrayList<>();
    final List<ArrayAccessExpr> arrayAccessExprs = new ArrayList<>();
    final List<VariableDeclarationExpr> varDeclExprs = new ArrayList<>();
    final List<ObjectCreationExpr> objectCreationExprs = new ArrayList<>();
    final List<ArrayCreationExpr> arrayCreationExprs = new ArrayList<>();

    // Statements
    final List<ReturnStmt> returnStmts = new ArrayList<>();
    final List<IfStmt> ifStmts = new ArrayList<>();
    final List<ForEachStmt> forEachStmts = new ArrayList<>();
    final List<ThrowStmt> throwStmts = new ArrayList<>();
    final List<TryStmt> tryStmts = new ArrayList<>();
    final List<SynchronizedStmt> synchronizedStmts = new ArrayList<>();
    final List<SwitchExpr> switchExprs = new ArrayList<>();
    final List<SwitchStmt> switchStmts = new ArrayList<>();

    /**
     * Collects all AST nodes from the given method declaration in a single DFS pass.
     */
    static ASTCollector collect(MethodDeclaration methodDecl) {
        ASTCollector c = new ASTCollector();
        methodDecl.accept(c, null);
        return c;
    }

    @Override public void visit(BinaryExpr n, Void arg) { binaryExprs.add(n); super.visit(n, arg); }
    @Override public void visit(MethodCallExpr n, Void arg) { methodCallExprs.add(n); super.visit(n, arg); }
    @Override public void visit(FieldAccessExpr n, Void arg) { fieldAccessExprs.add(n); super.visit(n, arg); }
    @Override public void visit(NameExpr n, Void arg) { nameExprs.add(n); super.visit(n, arg); }
    @Override public void visit(AssignExpr n, Void arg) { assignExprs.add(n); super.visit(n, arg); }
    @Override public void visit(UnaryExpr n, Void arg) { unaryExprs.add(n); super.visit(n, arg); }
    @Override public void visit(ArrayAccessExpr n, Void arg) { arrayAccessExprs.add(n); super.visit(n, arg); }
    @Override public void visit(VariableDeclarationExpr n, Void arg) { varDeclExprs.add(n); super.visit(n, arg); }
    @Override public void visit(ObjectCreationExpr n, Void arg) { objectCreationExprs.add(n); super.visit(n, arg); }
    @Override public void visit(ArrayCreationExpr n, Void arg) { arrayCreationExprs.add(n); super.visit(n, arg); }
    @Override public void visit(ReturnStmt n, Void arg) { returnStmts.add(n); super.visit(n, arg); }
    @Override public void visit(IfStmt n, Void arg) { ifStmts.add(n); super.visit(n, arg); }
    @Override public void visit(ForEachStmt n, Void arg) { forEachStmts.add(n); super.visit(n, arg); }
    @Override public void visit(ThrowStmt n, Void arg) { throwStmts.add(n); super.visit(n, arg); }
    @Override public void visit(TryStmt n, Void arg) { tryStmts.add(n); super.visit(n, arg); }
    @Override public void visit(SynchronizedStmt n, Void arg) { synchronizedStmts.add(n); super.visit(n, arg); }
    @Override public void visit(SwitchExpr n, Void arg) { switchExprs.add(n); super.visit(n, arg); }
    @Override public void visit(SwitchStmt n, Void arg) { switchStmts.add(n); super.visit(n, arg); }
}
