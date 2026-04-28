package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.sexpr.Printer;
import org.smtlib.IVisitor;

/**
 * SMTLIB {@code define-fun-rec} command. Emits the same form as
 * {@link C_define_fun} but with the recursive keyword so Z3 and CVC5 allow
 * self-reference in the body -- necessary for bounded {@code \sum},
 * {@code \product}, and {@code \num_of} encodings.
 *
 * <p>Adapted from the OpenJML-SeniorDesign quantifier project
 * (<a href="https://github.com/OpenJML-SeniorDesign/OpenJML-Quantifiers">OpenJML-Quantifiers</a>),
 * under the same GPLv2 license as the enclosing OpenJML tree.</p>
 */
public class C_define_fun_rec extends C_define_fun {

    public static final String commandName = "define-fun-rec";

    @Override
    public String commandName() { return commandName; }

    public C_define_fun_rec(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expr) {
        super(id, declarations, resultSort, expr);
    }

    /** Writes the command in the syntax of the given printer. */
    @Override
    public void write(Printer p) throws IOException, IVisitor.VisitorException {
        p.writer().append("(" + commandName + " ");
        symbol().accept(p);
        p.writer().append(" (");
        for (IDeclaration d: parameters()) {
            d.accept(p);
        }
        p.writer().append(") ");
        resultSort().accept(p);
        p.writer().append(" ");
        expression().accept(p);
        p.writer().append(")");
    }
}
