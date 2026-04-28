#!/usr/bin/env python3
"""
Patches OpenJML's SMTTranslator.java to add \\sum, \\product, \\num_of support.

The upstream OpenJML SMTTranslator handles only \\forall and \\exists. For the
other JML generalized quantifiers it falls through to a "default" branch that
creates a fresh uninterpreted constant, which is why the solver can't reason
about the value. This patch wires the three numeric quantifiers through a new
constructSmtQuantifier() method that emits a (define-fun-rec ...) per
occurrence — the SMTLIB idiom that lets Z3/CVC5 unfold the recursion.

Idempotent: running twice is safe; the script checks for an already-patched
marker line before touching the file.

Adapted from the OpenJML-SeniorDesign quantifier project (GPLv2).
"""
import re
import sys
from pathlib import Path

PATCH_MARKER = "int uniqueQuantCount = 0; // jml-sum-patch"

SMT_TRANSLATOR = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
    "OpenJMLsrc/src/jdk.compiler/share/classes/org/jmlspecs/openjml/esc/SMTTranslator.java")


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


IMPORTS = """import org.smtlib.command.C_define_fun_rec;
import com.sun.tools.javac.code.TypeTag;
"""


def add_imports(src: str) -> str:
    # Find the last "import" line in the file, append ours after it.
    import_pattern = re.compile(r"^(import [^\n]+;\n)+", re.MULTILINE)
    matches = list(import_pattern.finditer(src))
    if not matches:
        raise SystemExit("No imports found — file format unexpected")
    last_block = matches[-1]
    insert_pos = last_block.end()
    return src[:insert_pos] + IMPORTS + src[insert_pos:]


FIELDS = """
    // --- JML sum/product/num_of support -----------------------------------------
    int uniqueQuantCount = 0; // jml-sum-patch
    java.util.List<IExpr.IDeclaration> quantifierScope = new java.util.LinkedList<>();
    // ----------------------------------------------------------------------------
"""


def add_fields(src: str) -> str:
    # Insert after the `protected Context context;` line so the fields live
    # near the other SMTTranslator state.
    anchor = "    protected Context context;"
    idx = src.index(anchor)
    end_of_line = src.index("\n", idx) + 1
    return src[:end_of_line] + FIELDS + src[end_of_line:]


CONSTRUCT_METHOD = '''
    /**
     * Strips OpenJML overflow-check ternaries to recover the underlying value
     * expression. BasicBlocker wraps int expressions in patterns like
     * {@code (x > MAX_INT_LONG) ? overflow_max : ((x < MIN_INT_LONG) ? overflow_min : x)}
     * and the synthetic sub-nodes of those ternaries lack type annotations,
     * so scanning them NPEs in visitBinary. We peel any JCConditional layers
     * until we reach a leaf (JCIdent, JCLiteral, JCFieldAccess, JCParens).
     */
    private JCExpression stripOverflowChecks(JCExpression bound) {
        int guard = 0;
        while (guard++ < 16 && bound instanceof JCConditional) {
            JCConditional cond = (JCConditional) bound;
            JCExpression fp = cond.falsepart;
            JCExpression tp = cond.truepart;
            if (fp instanceof JCIdent || fp instanceof JCLiteral
                    || fp instanceof JCFieldAccess || fp instanceof JCParens) {
                bound = fp;
            } else if (tp instanceof JCIdent || tp instanceof JCLiteral
                    || tp instanceof JCFieldAccess || tp instanceof JCParens) {
                bound = tp;
            } else {
                // Fall through the nested ternary structure via falsepart (the
                // non-overflow case in OpenJML's encoding).
                bound = fp;
            }
        }
        return bound;
    }

    /**
     * Converts a simple range-bound expression (quantifier low or high) into
     * SMTLIB form without re-scanning the AST where possible. Scanning
     * sub-expressions of an already-rewritten range can hit overflow-check
     * ternaries whose synthetic sub-nodes lack type annotations, which NPEs
     * in visitBinary.  Returns null if the bound cannot be converted.
     */
    private IExpr convertBoundSafely(JCExpression bound) {
        if (bound == null) return null;
        bound = stripOverflowChecks(bound);
        if (bound instanceof JCParens) bound = ((JCParens) bound).getExpression();
        bound = stripOverflowChecks(bound);
        if (bound instanceof JCIdent) {
            return F.symbol(makeBarEnclosedString(((JCIdent) bound).name.toString()));
        }
        if (bound instanceof JCLiteral) {
            Object v = ((JCLiteral) bound).value;
            if (v instanceof Integer) return F.numeral(((Integer) v).longValue());
            if (v instanceof Long)    return F.numeral((Long) v);
            if (v instanceof Short)   return F.numeral(((Short) v).longValue());
            if (v instanceof Byte)    return F.numeral(((Byte) v).longValue());
            return null;
        }
        // For other shapes (arithmetic, field access, method calls), attempt
        // scan but fall back to null on any exception -- safer than crashing.
        try {
            scan(bound);
            return result;
        } catch (Throwable t) {
            return null;
        }
    }

    /**
     * Emits a (define-fun-rec ...) SMTLIB function that realises the value of
     * a JML \\\\sum / \\\\product / \\\\num_of quantifier for a bounded range,
     * and returns a call to that function. The recursion iterates from the
     * quantified variable down to the low bound and accumulates the value at
     * each step that satisfies the range predicate.
     *
     * Adapted from OpenJML-SeniorDesign quantifier project (GPLv2).
     */
    private IExpr constructSmtQuantifier(JmlQuantifiedExpr that, IExpr range, IExpr value,
                                          java.util.List<IDeclaration> params) {
        TypeTag quantifierVarType = that.decls.head.type.getTag();
        if (quantifierVarType != TypeTag.INT && quantifierVarType != TypeTag.LONG
                && quantifierVarType != TypeTag.SHORT) {
            notImplWarn(that, "JML quantified expression with non-integral quantifier type");
            return null;
        }
        if (params.size() != 1) {
            notImplWarn(that, "JML quantified expression with multiple or zero parameters");
            return null;
        }

        JmlBoundsExtractor.Bounds bounds = JmlBoundsExtractor.extract(that.decls, that.range, true, this);
        if (bounds == null) return null;
        if (bounds.lo == null || bounds.hi == null) {
            notImplWarn(that.range, "JML quantified expression range is not a recognised pattern");
            return null;
        }
        IExpr loExpr = convertBoundSafely(bounds.lo);
        IExpr hiExpr = convertBoundSafely(bounds.hi);
        if (loExpr == null || hiExpr == null) {
            notImplWarn(that, "JML quantified expression bound could not be converted to SMTLIB");
            return null;
        }

        boolean isProduct = that.kind.keyword() == QuantifiedExpressions.qproductID;

        ISymbol hi = F.symbol("|`hi|");
        ISymbol quantN = F.symbol("|`quant_" + (uniqueQuantCount++) + "|");
        ISort returnType = convertSort(that.type);

        int javaBaseCase = isProduct ? 1 : 0;
        IExpr baseCase;
        if (that.type.getTag() == TypeTag.FLOAT || that.type.getTag() == TypeTag.DOUBLE) {
            baseCase = F.decimal(Double.toString(javaBaseCase));
        } else {
            baseCase = F.numeral(javaBaseCase);
        }

        // \\num_of(range, pred) is \\sum(range && pred, 1) -- rewrite before emitting.
        if (that.kind.keyword() == QuantifiedExpressions.qnumofID) {
            range = F.fcn(andSym, range, value);
            value = F.numeral(1);
        }

        IDeclaration quantifiedVar = params.get(0);
        ISymbol lo = quantifiedVar.parameter();

        java.util.List<IExpr> callParameters = new java.util.LinkedList<>();
        java.util.List<IDeclaration> functionParameters = new java.util.LinkedList<>();

        functionParameters.add(quantifiedVar);
        functionParameters.add(F.declaration(hi, quantifiedVar.sort()));

        callParameters.add(F.fcn(F.symbol("+"), lo, F.numeral(1)));
        callParameters.add(hi);

        // Propagate any outer quantifier's bound variables so the recursion can refer to them.
        for (IExpr.IDeclaration decl : quantifierScope) {
            callParameters.add(decl.parameter());
            functionParameters.add(decl);
        }

        commands.add(new C_define_fun_rec(
            quantN, functionParameters, returnType,
            F.fcn(F.symbol("ite"), F.fcn(F.symbol("<"), hi, lo),
                baseCase,
                F.fcn(isProduct ? F.symbol("*") : F.symbol("+"),
                    F.fcn(quantN, callParameters),
                    F.fcn(F.symbol("ite"), range,
                        value,
                        baseCase
                    )
                )
            )
        ));

        // Invoke the freshly-defined function with the actual low/high extracted above.
        callParameters.remove(0);
        callParameters.remove(0);
        callParameters.add(0, loExpr);
        callParameters.add(1, hiExpr);

        return F.fcn(quantN, callParameters);
    }

'''


def add_construct_method(src: str) -> str:
    # Insert right before the @Override that annotates visitJmlQuantifiedExpr.
    # Inserting between @Override and the method body would orphan the annotation.
    anchor = "    @Override\n    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {"
    idx = src.index(anchor)
    return src[:idx] + CONSTRUCT_METHOD + src[idx:]


def patch_visit_method(src: str) -> str:
    # 1. Inject scope push/pop around the scan of range/value.
    # Upstream:
    #     scan(that.range);
    #     IExpr range = result;
    #     scan(that.value);
    #     IExpr value = result;
    # We add: quantifierScope.addAll(params) before, removeAll(params) after.
    old_scan = """            scan(that.range);
            IExpr range = result;
            scan(that.value);
            IExpr value = result;"""
    new_scan = """            quantifierScope.addAll(params);
            scan(that.range);
            IExpr range = result;
            scan(that.value);
            IExpr value = result;
            quantifierScope.removeAll(params);"""
    if old_scan not in src:
        raise SystemExit("Couldn't find scan block in visitJmlQuantifiedExpr")
    src = src.replace(old_scan, new_scan, 1)

    # 2. Insert cases for qsumID / qproductID / qnumofID before the default.
    # The new block uses its own scope ({ }) so the ISymbol declaration doesn't
    # collide with the one in `default:`, and falls through is avoided with an
    # explicit break -- OpenJDK's javac build enforces -Werror on [fallthrough].
    old_default = """            default:
                notImplWarn(that, "JML Quantified expression using " + that.kind.keyword());"""
    new_default = """            case QuantifiedExpressions.qsumID:
            case QuantifiedExpressions.qproductID:
            case QuantifiedExpressions.qnumofID: {
                result = constructSmtQuantifier(that, range, value, params);
                if (result != null) break;
                notImplWarn(that, "JML Quantified expression using " + that.kind.keyword());
                ISymbol sym = F.symbol(makeBarEnclosedString(that));
                addConstant(sym, convertSort(that.type), null);
                result = sym;
                break;
            }
            default:
                notImplWarn(that, "JML Quantified expression using " + that.kind.keyword());"""
    if old_default not in src:
        raise SystemExit("Couldn't find default branch in visitJmlQuantifiedExpr")
    src = src.replace(old_default, new_default, 1)
    return src


def main():
    if not SMT_TRANSLATOR.exists():
        raise SystemExit(f"File not found: {SMT_TRANSLATOR}")

    src = SMT_TRANSLATOR.read_text()
    if already_patched(src):
        print("Already patched, skipping")
        return

    src = add_imports(src)
    src = add_fields(src)
    src = add_construct_method(src)
    src = patch_visit_method(src)

    SMT_TRANSLATOR.write_text(src)
    print(f"Patched {SMT_TRANSLATOR}")


if __name__ == "__main__":
    main()
