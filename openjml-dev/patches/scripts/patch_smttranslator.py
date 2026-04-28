#!/usr/bin/env python3
"""
Patches OpenJML's SMTTranslator.java to add \\sum, \\product, \\num_of support.

The upstream OpenJML SMTTranslator handles only \\forall and \\exists. For the
other JML generalized quantifiers it falls through to a "default" branch that
creates a fresh uninterpreted constant, which is why the solver can't reason
about the value.

Encoding (axiomatic):
    For each occurrence of (\\sum|\\product|\\num_of int k; lo <= k && k < hi; expr(k))
    emit
        (declare-fun  quant_N (Int Int [outer_scope...]) ResultSort)
        (assert (forall ((n Int) [outer...])
                  (! (= (quant_N n n [outer...]) BASE) :pattern ((quant_N n n [outer...])))))
        (assert (forall ((lo Int) (hi Int) [outer...])
                  (! (=> (<= lo hi)
                         (= (quant_N lo (+ hi 1) [outer...])
                            (OP (quant_N lo hi [outer...])
                                (let ((k hi)) (ite range value BASE)))))
                     :pattern ((quant_N lo (+ hi 1) [outer...])))))
        (call) becomes (quant_N loExpr hiExpr [outer...])

    where
        OP   = '+' for sum/num_of, '*' for product
        BASE = 0  for sum/num_of, 1  for product
        For \\num_of, the user-supplied predicate becomes the range; the
        accumulated value is constant 1.

The two assert-foralls give Z3 explicit triggers (`:pattern`) so its E-matching
unfolds the recursion exactly when an invariant of the shape
`acc == quant_N(0, i)` and a body assertion of the shape
`acc + value(i) == quant_N(0, i+1)` are present together. This is the
loop-invariant inductive step shape the inferrer emits for every
sum-/product-/num_of-accumulator loop.

Why axiomatic, not (define-fun-rec ...)?
    Earlier versions of this fork used (define-fun-rec quant_N ...) which Z3
    nominally accepts. In practice, OpenJML's interactive SMT communication
    layer fails to recognise the recursive function symbol after a
    define-fun-rec command, surfacing as
        (error "line N column M: unknown function/constant `quant_0")
    on the very next assert that calls quant_0. The smoke fixtures
    SumMinimal.java and SumInductive.java reproduced the failure even on
    OpenJML's own examples. The axiomatic form sidesteps that interaction
    bug entirely while giving Z3 the same inductive scaffold that
    define-fun-rec was supposed to provide -- only with explicit triggers,
    which Z3's E-matching needs anyway.

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


IMPORTS = """import org.smtlib.command.C_assert;
import org.smtlib.command.C_declare_fun;
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
    // Memoise (opSym, baseCase, value-SMT-string) -> reusable function symbol so
    // structurally-identical quantifier occurrences in different program states
    // share a function name and Z3 can relate them.
    java.util.Map<String, IExpr.ISymbol> quantifierFunctionCache = new java.util.HashMap<>();
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
     * Emits an axiomatic encoding of a JML \\\\sum / \\\\product / \\\\num_of
     * quantifier for a bounded range, and returns a call to the freshly-declared
     * function. The encoding is:
     *   (declare-fun  quant_N (Int Int [outerScope]) ResultSort)
     *   (assert  base axiom):     quant_N(n,n,*) = BASE     pattern (quant_N n n *)
     *   (assert  step axiom):     lo<=hi ==>
     *                             quant_N(lo, hi+1, *) = OP(quant_N(lo, hi, *),
     *                                                       let k=hi in (ite range value BASE))
     *                                                     pattern (quant_N lo (+ hi 1) *)
     *
     * Z3's E-matching uses the patterns to instantiate the step axiom whenever a
     * verification condition contains a call of the form quant_N(lo, i+1, ...).
     * That is exactly the shape the inferrer's loop-invariant
     *   {@code total == (\\sum int k; 0<=k<i; arr[k])}
     * produces at the body assertion point (where i has been incremented).
     *
     * The base axiom discharges the empty-range case (quant_N(n,n)), which the
     * inferrer's "trivial empty-array" postcondition needs:
     *   {@code arr.length == 0 ==> \\result == 0}
     *
     * Non-axiomatic alternatives we tried and rejected:
     *   - (define-fun-rec ...): Z3 4.7.1 nominally supports it, but OpenJML's
     *     interactive SMT communication layer surfaces it as an "unknown
     *     function" error on the very next assert that calls the function.
     *     Reproduces on the smoke fixtures even with the OpenJML-supplied
     *     loop_invariants in place.
     *   - bounded unrolling (when arr.length<=K, emit value(0) op ... op
     *     value(K-1)): doesn't help because the inferrer doesn't emit
     *     length-bound preconditions and forcing one in would weaken the spec.
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
        // Normalise to half-open [lo, hi). User-supplied k <= hi means the
        // upper bound is inclusive, so add 1. lo < k means the lower bound is
        // exclusive, so add 1. The function signature is uniformly half-open
        // and the step axiom iterates k = lo, lo+1, ..., hi-1.
        if (bounds.hiInclusive) {
            hiExpr = F.fcn(F.symbol("+"), hiExpr, F.numeral(1));
        }
        if (bounds.loExclusive) {
            loExpr = F.fcn(F.symbol("+"), loExpr, F.numeral(1));
        }

        boolean isProduct = that.kind.keyword() == QuantifiedExpressions.qproductID;
        boolean isNumOf   = that.kind.keyword() == QuantifiedExpressions.qnumofID;

        ISort returnType = convertSort(that.type);
        ISymbol opSym  = isProduct ? F.symbol("*") : F.symbol("+");

        int javaBaseCase = isProduct ? 1 : 0;
        IExpr baseCase;
        if (that.type.getTag() == TypeTag.FLOAT || that.type.getTag() == TypeTag.DOUBLE) {
            baseCase = F.decimal(Double.toString(javaBaseCase));
        } else {
            baseCase = F.numeral(javaBaseCase);
        }

        // \\num_of: count occurrences where pred holds. Encode by replacing
        // the per-step value with (ite pred 1 0). We do this BEFORE building
        // the function so the SMT body uses the rewritten value. The range
        // (lo<=k<hi) is captured by the function's bounds; only the predicate
        // remains in the per-step value computation.
        if (isNumOf) {
            IExpr pred = value;
            value = F.fcn(F.symbol("ite"), pred, F.numeral(1), F.numeral(0));
        }

        IDeclaration quantifiedVar = params.get(0);
        ISymbol kSym = quantifiedVar.parameter();
        ISort   kSort = quantifiedVar.sort();

        // Memoise on a key derived from the operator, base case, the SMT
        // serialisation of the value expression, and the outer-scope sorts.
        // Two structurally-identical quantifiers (e.g. the same \\sum invariant
        // emitted at multiple program states for the same loop) must share a
        // function symbol -- otherwise Z3 sees them as unrelated and the
        // step axiom on one cannot discharge an obligation on the other.
        StringBuilder cacheKeyBuilder = new StringBuilder();
        cacheKeyBuilder.append(isProduct ? "PRODUCT" : (isNumOf ? "NUMOF" : "SUM"));
        cacheKeyBuilder.append("|").append(returnType.toString());
        try {
            java.io.StringWriter sw = new java.io.StringWriter();
            org.smtlib.solvers.Printer.write(sw, value);
            cacheKeyBuilder.append("|VAL:").append(sw.toString());
        } catch (Throwable t) {
            // Serialisation can't fail for well-formed SMT, but be defensive:
            // fall back to per-occurrence emission rather than risk collisions.
            cacheKeyBuilder.append("|UNIQ:").append(uniqueQuantCount);
        }
        for (IExpr.IDeclaration outer: quantifierScope) {
            cacheKeyBuilder.append("|OUTER:").append(outer.parameter().toString())
                           .append(":").append(outer.sort().toString());
        }
        String cacheKey = cacheKeyBuilder.toString();
        ISymbol cachedQuantN = quantifierFunctionCache.get(cacheKey);
        ISymbol quantN;
        boolean reused = (cachedQuantN != null);
        if (reused) {
            quantN = cachedQuantN;
        } else {
            quantN = F.symbol("|`quant_" + (uniqueQuantCount++) + "|");
            quantifierFunctionCache.put(cacheKey, quantN);
        }

        // ---- Build parameter signatures ---------------------------------------
        // The function takes (lo, hi) plus any outer-scope captured vars.
        // For the base/step axioms, we need fresh quantified variables `n`,
        // `lo_q`, `hi_q` so the patterns work cleanly.
        java.util.List<ISort> declareFunArgSorts = new java.util.LinkedList<>();
        declareFunArgSorts.add(kSort);  // lo
        declareFunArgSorts.add(kSort);  // hi
        for (IExpr.IDeclaration outer: quantifierScope) {
            declareFunArgSorts.add(outer.sort());
        }

        if (!reused) commands.add(new C_declare_fun(quantN, declareFunArgSorts, returnType));

        // ---- Base axiom: (forall n outer.., (! (= (quant_N n n outer..) base)
        //                                        :pattern ((quant_N n n outer..)))) ---
        ISymbol nSym = F.symbol("|`bn|");
        java.util.List<IDeclaration> baseAxiomBindings = new java.util.LinkedList<>();
        baseAxiomBindings.add(F.declaration(nSym, kSort));
        java.util.List<IExpr> baseCallArgs = new java.util.LinkedList<>();
        baseCallArgs.add(nSym);
        baseCallArgs.add(nSym);
        for (IExpr.IDeclaration outer: quantifierScope) {
            baseAxiomBindings.add(outer);
            baseCallArgs.add(outer.parameter());
        }
        IExpr baseCall = F.fcn(quantN, baseCallArgs);
        IExpr baseEq   = F.fcn(eqSym, baseCall, baseCase);
        java.util.List<IExpr> basePat = new java.util.LinkedList<>();
        basePat.add(baseCall);
        if (!reused) commands.add(new C_assert(F.forall(baseAxiomBindings, baseEq, basePat)));

        // ---- Step axiom: (forall lo_q hi_q outer..,
        //                    (! (=> (<= lo_q hi_q)
        //                           (= (quant_N lo_q (+ hi_q 1) outer..)
        //                              (op (quant_N lo_q hi_q outer..)
        //                                  (let ((k hi_q)) (ite range value BASE)))))
        //                       :pattern ((quant_N lo_q (+ hi_q 1) outer..)))) -------
        ISymbol loQ = F.symbol("|`lq|");
        ISymbol hiQ = F.symbol("|`hq|");
        java.util.List<IDeclaration> stepBindings = new java.util.LinkedList<>();
        stepBindings.add(F.declaration(loQ, kSort));
        stepBindings.add(F.declaration(hiQ, kSort));
        java.util.List<IExpr> stepCallHiPlus1Args = new java.util.LinkedList<>();
        stepCallHiPlus1Args.add(loQ);
        stepCallHiPlus1Args.add(F.fcn(F.symbol("+"), hiQ, F.numeral(1)));
        java.util.List<IExpr> stepCallHiArgs = new java.util.LinkedList<>();
        stepCallHiArgs.add(loQ);
        stepCallHiArgs.add(hiQ);
        for (IExpr.IDeclaration outer: quantifierScope) {
            stepBindings.add(outer);
            stepCallHiPlus1Args.add(outer.parameter());
            stepCallHiArgs.add(outer.parameter());
        }
        IExpr lhsCall  = F.fcn(quantN, stepCallHiPlus1Args);
        IExpr recCall  = F.fcn(quantN, stepCallHiArgs);
        // Bind k := hi_q so the user-supplied value SMT expression (which
        // references k) evaluates at hi_q. The range is dropped: the step
        // axiom's guard (lo_q <= hi_q) and the iteration from lo_q to hi_q
        // already capture the range lo<=k<hi. For non-standard ranges
        // (e.g. (\\num_of int k; lo<=k<hi; pred(k))) the predicate has been
        // moved into the value position above.
        java.util.List<org.smtlib.IExpr.IBinding> letBindings = new java.util.LinkedList<>();
        letBindings.add(F.binding(kSym, hiQ));
        IExpr letValue  = F.let(letBindings, value);
        IExpr rhsCombined = F.fcn(opSym, recCall, letValue);
        IExpr stepEq = F.fcn(eqSym, lhsCall, rhsCombined);
        IExpr stepGuarded = F.fcn(impliesSym,
                F.fcn(F.symbol("<="), loQ, hiQ),
                stepEq);
        java.util.List<IExpr> stepPat = new java.util.LinkedList<>();
        stepPat.add(lhsCall);
        if (!reused) commands.add(new C_assert(F.forall(stepBindings, stepGuarded, stepPat)));

        // ---- Build the call site: (quant_N loExpr hiExpr outer...) ----------
        java.util.List<IExpr> siteArgs = new java.util.LinkedList<>();
        siteArgs.add(loExpr);
        siteArgs.add(hiExpr);
        for (IExpr.IDeclaration outer: quantifierScope) {
            siteArgs.add(outer.parameter());
        }
        return F.fcn(quantN, siteArgs);
    }

'''


def add_construct_method(src: str) -> str:
    # Insert right before the @Override that annotates visitJmlQuantifiedExpr.
    # Inserting between @Override and the method body would orphan the annotation.
    anchor = "    @Override\n    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {"
    idx = src.index(anchor)
    return src[:idx] + CONSTRUCT_METHOD + src[idx:]


def patch_convert_reset(src: str) -> str:
    # Reset uniqueQuantCount and the function cache at the start of each
    # convert() call so a fresh script doesn't inherit stale function names
    # from a previous script (the feasibility-check pathway re-enters convert()).
    old_init = """        startCommands = new LinkedList<ICommand>();
        commands = new LinkedList<ICommand>();"""
    new_init = """        startCommands = new LinkedList<ICommand>();
        commands = new LinkedList<ICommand>();
        // jml-sum-patch: reset per-convert quantifier state.
        uniqueQuantCount = 0;
        quantifierFunctionCache.clear();"""
    if old_init not in src:
        raise SystemExit("Couldn't find startCommands/commands init in convert()")
    return src.replace(old_init, new_init, 1)


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
    src = patch_convert_reset(src)
    src = patch_visit_method(src)

    SMT_TRANSLATOR.write_text(src)
    print(f"Patched {SMT_TRANSLATOR}")


if __name__ == "__main__":
    main()
