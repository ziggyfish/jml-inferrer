package com.z3x.theory;

import com.z3x.term.Sort;
import com.z3x.term.Term;
import com.z3x.term.TermFactory;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Concrete-arithmetic evaluation for IEEE-754 floating-point operations applied to FP
 * literals, plus symbolic axioms (identity / sign / NaN / infinity propagation) for
 * operations applied to variable terms.
 *
 * Strategy:
 *  - Float32 (eb=8, sb=24) and Float64 (eb=11, sb=53) can be decoded into Java {@code float}
 *    / {@code double} bit-for-bit via {@link Float#intBitsToFloat(int)} /
 *    {@link Double#longBitsToDouble(long)}. For the common RNE rounding mode this gives
 *    exact IEEE-754 results.
 *  - Other rounding modes are realised by performing the computation in {@link BigDecimal}
 *    with very high working precision, then rounding the exact value down to the nearest
 *    representable FP value per the requested mode.
 *  - Other widths (Float16, Float128, custom) follow the BigDecimal path with width-specific
 *    encoding helpers.
 *
 * Operations handled:
 *  - fp.add, fp.sub, fp.mul, fp.div, fp.rem, fp.fma, fp.sqrt — ternary first arg is the rounding mode
 *  - fp.abs, fp.neg, fp.min, fp.max — no rounding mode
 *  - fp.lt, fp.leq, fp.gt, fp.geq — Bool, no rounding mode
 *  - fp.to_real on literals (numerical conversion)
 *  - Symbolic axioms for arithmetic where one or both args are non-literal:
 *      fp.add(x, +0) = x;  fp.add(+0, x) = x;
 *      fp.mul(x, +1) = x;  fp.mul(+1, x) = x;  fp.mul(x, NaN) = NaN; fp.mul(NaN, x) = NaN;
 *      fp.add(x, NaN) = NaN; fp.add(NaN, x) = NaN;
 *      fp.neg(fp.neg(x)) = x;
 *      fp.abs(x) >=0 (i.e. fp.isNegative(fp.abs(x)) = false)
 */
public final class FpArith {

    private final TermFactory tf;
    private final List<Term> axioms = new ArrayList<>();
    private final Set<Integer> seen = new HashSet<>();
    /** Map from arithmetic-app term id → its resolved literal value. Used so callers can
     *  substitute these literals before later passes (so e.g. fp.eq(fp.add(...), lit) reduces). */
    private final java.util.Map<Integer, Term> substitutions = new java.util.HashMap<>();

    public FpArith(TermFactory tf) { this.tf = tf; }

    public List<Term> axioms() { return axioms; }
    public java.util.Map<Integer, Term> substitutions() { return substitutions; }

    public void collectFrom(Term t) { walk(t); }

    /** Apply the resolved-literal substitutions to {@code t}, recursively. */
    public Term substitute(Term t) {
        Term sub = substitutions.get(t.id);
        if (sub != null) return sub;
        if (t instanceof Term.App app) {
            java.util.List<Term> newArgs = null;
            for (int i = 0; i < app.args.size(); i++) {
                Term orig = app.args.get(i);
                Term repl = substitute(orig);
                if (repl != orig) {
                    if (newArgs == null) {
                        newArgs = new java.util.ArrayList<>(app.args);
                    }
                    newArgs.set(i, repl);
                }
            }
            if (newArgs != null) return tf.mkAppRaw(app.symbol, newArgs, app.sort);
        }
        return t;
    }

    private void walk(Term t) {
        if (!seen.add(t.id)) return;
        for (Term c : t.children()) walk(c);
        if (t instanceof Term.App app) handleApp(app);
    }

    // ---------- top-level dispatch ----------

    private void handleApp(Term.App app) {
        switch (app.symbol) {
            case "fp.add":
            case "fp.sub":
            case "fp.mul":
            case "fp.div":
            case "fp.rem":
            case "fp.sqrt":
            case "fp.fma":
                handleArith(app);
                break;
            case "fp.abs":
            case "fp.neg":
                handleUnaryNoRm(app);
                break;
            case "fp.min":
            case "fp.max":
                handleMinMax(app);
                break;
            case "fp.lt":
            case "fp.leq":
            case "fp.gt":
            case "fp.geq":
                handleCmp(app);
                break;
            case "fp.to_real":
                handleToReal(app);
                break;
            default:
                // Indexed: (_ to_fp eb sb) ... ; (_ to_fp_unsigned eb sb) ...
                if (app.symbol.startsWith("(_ to_fp ") || app.symbol.startsWith("(_ to_fp_unsigned ")
                        || app.symbol.startsWith("(_ fp.to_sbv ") || app.symbol.startsWith("(_ fp.to_ubv ")) {
                    handleConversion(app);
                }
                break;
        }
    }

    // ---------- arithmetic with rounding mode ----------

    private void handleArith(Term.App app) {
        // First arg is rounding mode for fp.add/sub/mul/div/rem/sqrt/fma. fp.rem ignores RM.
        if (app.args.isEmpty()) return;
        Term rmTerm = app.args.get(0);
        // sqrt: (fp.sqrt RM x). add/sub/mul/div: (op RM x y). fma: (op RM x y z). rem: (fp.rem x y).
        boolean hasRm = !"fp.rem".equals(app.symbol);
        if (hasRm && !(rmTerm instanceof Term.RmConst)) {
            emitArithSymbolicAxioms(app);
            return;
        }
        int firstOp = hasRm ? 1 : 0;
        // Pull operand FpConsts.
        FpView[] ops = new FpView[app.args.size() - firstOp];
        boolean allLiteral = true;
        for (int i = firstOp; i < app.args.size(); i++) {
            Term a = app.args.get(i);
            if (!(a instanceof Term.FpConst lit)) { allLiteral = false; break; }
            ops[i - firstOp] = new FpView(lit);
        }
        if (!allLiteral) {
            emitArithSymbolicAxioms(app);
            return;
        }
        Term.RmConst.Mode mode = hasRm ? ((Term.RmConst) rmTerm).mode : Term.RmConst.Mode.RNE;
        int eb = ops[0].eb, sb = ops[0].sb;
        FpResult result = switch (app.symbol) {
            case "fp.add"  -> evalArith(ops[0], ops[1], mode, eb, sb, ArithOp.ADD);
            case "fp.sub"  -> evalArith(ops[0], ops[1], mode, eb, sb, ArithOp.SUB);
            case "fp.mul"  -> evalArith(ops[0], ops[1], mode, eb, sb, ArithOp.MUL);
            case "fp.div"  -> evalArith(ops[0], ops[1], mode, eb, sb, ArithOp.DIV);
            case "fp.rem"  -> evalRem(ops[0], ops[1], eb, sb);
            case "fp.sqrt" -> evalSqrt(ops[0], mode, eb, sb);
            case "fp.fma"  -> evalFma(ops[0], ops[1], ops[2], mode, eb, sb);
            default -> null;
        };
        if (result != null) {
            Term lit = encodeFp(result, eb, sb);
            recordResolved(app, lit);
        }
    }

    private void recordResolved(Term.App app, Term lit) {
        axioms.add(tf.mkEq((Term) app, lit));
        substitutions.put(app.id, lit);
    }

    private void emitArithSymbolicAxioms(Term.App app) {
        // Identity rules:
        //   fp.add(x, +0) = x ;  fp.add(+0, x) = x   (RNE; correct for any mode when y is +0 finite)
        //   fp.mul(x, 1)  = x ;  fp.mul(1, x)  = x
        //   fp.add(x, NaN) = NaN ; fp.mul(x, NaN) = NaN
        if (!app.symbol.equals("fp.add") && !app.symbol.equals("fp.mul")
                && !app.symbol.equals("fp.sub") && !app.symbol.equals("fp.div")) return;
        if (app.args.size() < 3) return;
        Term x = app.args.get(1);
        Term y = app.args.get(2);
        // NaN propagation.
        if (x instanceof Term.FpConst fc && fc.kind == Term.FpConst.Kind.NAN) {
            recordResolved(app, x);
            return;
        }
        if (y instanceof Term.FpConst fc && fc.kind == Term.FpConst.Kind.NAN) {
            recordResolved(app, y);
            return;
        }
        Term rmTerm = app.args.get(0);
        if (!(rmTerm instanceof Term.RmConst rm)) return;
        if (rm.mode != Term.RmConst.Mode.RNE && rm.mode != Term.RmConst.Mode.RNA) return; // identity rules
        // fp.add x +0 = x ; fp.add +0 x = x.
        if (app.symbol.equals("fp.add")) {
            if (isPosZero(y)) recordResolved(app, x);
            else if (isPosZero(x)) recordResolved(app, y);
        }
        if (app.symbol.equals("fp.sub")) {
            if (isPosZero(y)) recordResolved(app, x);
        }
        if (app.symbol.equals("fp.mul")) {
            if (isOne(y)) recordResolved(app, x);
            else if (isOne(x)) recordResolved(app, y);
        }
        if (app.symbol.equals("fp.div")) {
            if (isOne(y)) recordResolved(app, x);
        }
    }

    private static boolean isPosZero(Term t) {
        return t instanceof Term.FpConst f && f.kind == Term.FpConst.Kind.PLUS_ZERO;
    }
    private static boolean isOne(Term t) {
        if (!(t instanceof Term.FpConst f)) return false;
        if (f.kind != Term.FpConst.Kind.NORMAL || f.sign) return false;
        // exp = bias, sig = 0 → value 1.0
        BigInteger bias = BigInteger.ONE.shiftLeft(f.eb - 1).subtract(BigInteger.ONE);
        return f.exp.equals(bias) && f.sig.signum() == 0;
    }

    // ---------- unary (no RM): fp.abs, fp.neg ----------

    private void handleUnaryNoRm(Term.App app) {
        if (app.args.size() != 1) return;
        Term a = app.args.get(0);
        if (a instanceof Term.FpConst lit) {
            Term.FpConst out;
            if (app.symbol.equals("fp.abs")) {
                out = tf.mkFp(false, lit.exp, lit.sig, lit.eb, lit.sb, lit.kind);
            } else { // fp.neg
                Term.FpConst.Kind k = switch (lit.kind) {
                    case PLUS_ZERO -> Term.FpConst.Kind.MINUS_ZERO;
                    case MINUS_ZERO -> Term.FpConst.Kind.PLUS_ZERO;
                    case PLUS_INF -> Term.FpConst.Kind.MINUS_INF;
                    case MINUS_INF -> Term.FpConst.Kind.PLUS_INF;
                    default -> lit.kind;
                };
                out = tf.mkFp(!lit.sign, lit.exp, lit.sig, lit.eb, lit.sb, k);
            }
            recordResolved(app, out);
            return;
        }
        // Symbolic: fp.neg(fp.neg(x)) = x ; fp.abs(fp.abs(x)) = fp.abs(x); fp.abs(fp.neg(x)) = fp.abs(x).
        if (a instanceof Term.App inner) {
            if (app.symbol.equals("fp.neg") && inner.symbol.equals("fp.neg") && inner.args.size() == 1) {
                recordResolved(app, inner.args.get(0));
            }
            if (app.symbol.equals("fp.abs") && (inner.symbol.equals("fp.abs") || inner.symbol.equals("fp.neg"))
                    && inner.args.size() == 1) {
                Term simplified = inner.symbol.equals("fp.abs") ? a : tf.mkAppRaw("fp.abs", List.of(inner.args.get(0)), a.sort);
                recordResolved(app, simplified);
            }
        }
    }

    // ---------- min/max ----------

    private void handleMinMax(Term.App app) {
        if (app.args.size() != 2) return;
        Term a = app.args.get(0), b = app.args.get(1);
        // Literal-eval if both literals. SMT-LIB: fp.min/max(NaN, x) = x; fp.min/max(x, NaN) = x.
        // fp.min(+0, -0) is unspecified — pick -0; fp.max(+0, -0) is unspecified — pick +0.
        if (a instanceof Term.FpConst fa && b instanceof Term.FpConst fb) {
            if (fa.kind == Term.FpConst.Kind.NAN) { recordResolved(app, b); return; }
            if (fb.kind == Term.FpConst.Kind.NAN) { recordResolved(app, a); return; }
            FpView va = new FpView(fa), vb = new FpView(fb);
            int cmp = compareFp(va, vb);
            // Special: zero of differing sign.
            if (cmp == 0 && (fa.kind == Term.FpConst.Kind.PLUS_ZERO || fa.kind == Term.FpConst.Kind.MINUS_ZERO)
                    && (fb.kind == Term.FpConst.Kind.PLUS_ZERO || fb.kind == Term.FpConst.Kind.MINUS_ZERO)
                    && fa.sign != fb.sign) {
                if (app.symbol.equals("fp.min")) {
                    recordResolved(app, fa.sign ? a : b);
                } else {
                    recordResolved(app, fa.sign ? b : a);
                }
                return;
            }
            boolean pickA = app.symbol.equals("fp.min") ? cmp <= 0 : cmp >= 0;
            recordResolved(app, pickA ? a : b);
        }
    }

    // ---------- comparisons ----------

    private void handleCmp(Term.App app) {
        if (app.args.size() != 2) return;
        Term a = app.args.get(0), b = app.args.get(1);
        if (!(a instanceof Term.FpConst fa) || !(b instanceof Term.FpConst fb)) return;
        // Per IEEE-754: any comparison involving NaN returns false.
        if (fa.kind == Term.FpConst.Kind.NAN || fb.kind == Term.FpConst.Kind.NAN) {
            recordResolved(app, tf.mkBool(false));
            return;
        }
        FpView va = new FpView(fa), vb = new FpView(fb);
        int cmp = compareFp(va, vb);
        boolean res = switch (app.symbol) {
            case "fp.lt"  -> cmp < 0;
            case "fp.leq" -> cmp <= 0;
            case "fp.gt"  -> cmp > 0;
            case "fp.geq" -> cmp >= 0;
            default -> false;
        };
        recordResolved(app, tf.mkBool(res));
    }

    private static int compareFp(FpView a, FpView b) {
        BigDecimal va = a.toBigDecimal();
        BigDecimal vb = b.toBigDecimal();
        if (va == null || vb == null) {
            // Infinities.
            int aRank = signedInfRank(a);
            int bRank = signedInfRank(b);
            return Integer.compare(aRank, bRank);
        }
        return va.compareTo(vb);
    }

    private static int signedInfRank(FpView v) {
        if (v.kind == Term.FpConst.Kind.MINUS_INF) return -1;
        if (v.kind == Term.FpConst.Kind.PLUS_INF) return 1;
        // Finite: signum based on its decimal value, but treat as 0 (will fall back to magnitude).
        BigDecimal bd = v.toBigDecimal();
        return bd == null ? 0 : bd.signum();
    }

    // ---------- conversions ----------

    private void handleToReal(Term.App app) {
        if (app.args.size() != 1) return;
        if (!(app.args.get(0) instanceof Term.FpConst lit)) return;
        FpView v = new FpView(lit);
        BigDecimal bd = v.toBigDecimal();
        if (bd == null) return; // NaN/Inf → undefined; leave opaque.
        BigInteger num = bd.unscaledValue();
        int scale = bd.scale();
        if (scale <= 0) {
            BigInteger nval = num.multiply(BigInteger.TEN.pow(-scale));
            recordResolved(app, tf.mkRat(nval, BigInteger.ONE));
        } else {
            BigInteger den = BigInteger.TEN.pow(scale);
            recordResolved(app, tf.mkRat(num, den));
        }
    }

    private void handleConversion(Term.App app) {
        // (_ to_fp eb sb) RM x. Here app.symbol contains the indexed prefix.
        // Parse "(_ to_fp eb sb)" or "(_ to_fp_unsigned eb sb)".
        String sym = app.symbol;
        int spaceIdx = sym.indexOf(' ');
        // Strip "(_ "
        String body = sym.substring(3, sym.length() - 1);
        String[] parts = body.split(" ");
        if (parts.length < 3) return;
        int eb = Integer.parseInt(parts[1]);
        int sb = Integer.parseInt(parts[2]);
        if (parts[0].equals("to_fp") || parts[0].equals("to_fp_unsigned")) {
            if (app.args.size() < 1) return;
            // First arg is RM (if 2 args), second is the value. Or one-arg from BV.
            Term rmTerm = null;
            Term valTerm;
            if (app.args.size() == 2 && app.args.get(0) instanceof Term.RmConst) {
                rmTerm = app.args.get(0);
                valTerm = app.args.get(1);
            } else {
                valTerm = app.args.get(app.args.size() - 1);
            }
            Term.RmConst.Mode mode = rmTerm == null ? Term.RmConst.Mode.RNE : ((Term.RmConst) rmTerm).mode;
            BigDecimal val = null;
            if (valTerm instanceof Term.IntConst ic) {
                val = new BigDecimal(ic.value);
            } else if (valTerm instanceof Term.RatConst rc) {
                val = new BigDecimal(rc.num).divide(new BigDecimal(rc.den), new MathContext(80, RoundingMode.HALF_EVEN));
            } else if (valTerm instanceof Term.BvConst bc) {
                BigInteger v = parts[0].equals("to_fp_unsigned") ? bc.value : signedFromBv(bc);
                val = new BigDecimal(v);
            } else if (valTerm instanceof Term.FpConst fp) {
                FpView fpv = new FpView(fp);
                if (fpv.kind == Term.FpConst.Kind.NAN) {
                    recordResolved(app, tf.mkFp(false, BigInteger.ZERO, BigInteger.ONE, eb, sb, Term.FpConst.Kind.NAN));
                    return;
                }
                if (fpv.kind == Term.FpConst.Kind.PLUS_INF || fpv.kind == Term.FpConst.Kind.MINUS_INF) {
                    Term.FpConst.Kind k = fp.sign ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF;
                    recordResolved(app, tf.mkFp(fp.sign, BigInteger.ONE.shiftLeft(eb).subtract(BigInteger.ONE),
                            BigInteger.ZERO, eb, sb, k));
                    return;
                }
                val = fpv.toBigDecimal();
            }
            if (val == null) return;
            FpResult result = roundDecimalToFp(val, mode, eb, sb);
            Term lit = encodeFp(result, eb, sb);
            recordResolved(app, lit);
        }
        if (parts[0].equals("fp.to_sbv") || parts[0].equals("fp.to_ubv")) {
            // (_ fp.to_sbv W) RM x ; (_ fp.to_ubv W) RM x  →  bitvector of width W.
            int w = Integer.parseInt(parts[1]);
            if (app.args.size() != 2) return;
            if (!(app.args.get(0) instanceof Term.RmConst rmc)) return;
            if (!(app.args.get(1) instanceof Term.FpConst fp)) return;
            FpView v = new FpView(fp);
            BigDecimal bd = v.toBigDecimal();
            if (bd == null) return; // NaN/Inf — undefined per SMT-LIB; leave opaque.
            BigInteger asInt = roundToInteger(bd, rmc.mode);
            // For sbv: take low W bits (two's complement). For ubv: same low W bits, but if input negative, leave opaque.
            BigInteger mod = BigInteger.ONE.shiftLeft(w);
            if (parts[0].equals("fp.to_ubv") && asInt.signum() < 0) return;
            Term lit = tf.mkBv(asInt.mod(mod), w);
            recordResolved(app, lit);
        }
    }

    private static BigInteger signedFromBv(Term.BvConst bc) {
        BigInteger top = BigInteger.ONE.shiftLeft(bc.width - 1);
        if (bc.value.compareTo(top) >= 0) return bc.value.subtract(BigInteger.ONE.shiftLeft(bc.width));
        return bc.value;
    }

    private static BigInteger roundToInteger(BigDecimal bd, Term.RmConst.Mode mode) {
        RoundingMode jm = switch (mode) {
            case RNE -> RoundingMode.HALF_EVEN;
            case RNA -> RoundingMode.HALF_UP;
            case RTP -> RoundingMode.CEILING;
            case RTN -> RoundingMode.FLOOR;
            case RTZ -> RoundingMode.DOWN;
        };
        return bd.setScale(0, jm).toBigIntegerExact();
    }

    // ---------- evaluation kernels ----------

    private enum ArithOp { ADD, SUB, MUL, DIV }

    private FpResult evalArith(FpView a, FpView b, Term.RmConst.Mode mode, int eb, int sb, ArithOp op) {
        // Fast path: Float32/Float64 with Java native arithmetic for RNE.
        if (mode == Term.RmConst.Mode.RNE && (matches(eb, sb, 8, 24) || matches(eb, sb, 11, 53))) {
            if (matches(eb, sb, 8, 24)) {
                float fa = a.toJavaFloat();
                float fb = b.toJavaFloat();
                float r = switch (op) {
                    case ADD -> fa + fb;
                    case SUB -> fa - fb;
                    case MUL -> fa * fb;
                    case DIV -> fa / fb;
                };
                return FpResult.fromFloat(r);
            } else {
                double da = a.toJavaDouble();
                double db = b.toJavaDouble();
                double r = switch (op) {
                    case ADD -> da + db;
                    case SUB -> da - db;
                    case MUL -> da * db;
                    case DIV -> da / db;
                };
                return FpResult.fromDouble(r);
            }
        }
        // Slow path: BigDecimal arithmetic with target rounding mode.
        // First handle special values.
        FpResult sp = arithSpecial(a, b, op);
        if (sp != null) return sp;
        BigDecimal va = a.toBigDecimal();
        BigDecimal vb = b.toBigDecimal();
        if (va == null || vb == null) return null;
        MathContext mc = new MathContext(64, RoundingMode.HALF_EVEN);
        BigDecimal r;
        switch (op) {
            case ADD: r = va.add(vb, mc); break;
            case SUB: r = va.subtract(vb, mc); break;
            case MUL: r = va.multiply(vb, mc); break;
            case DIV:
                if (vb.signum() == 0) {
                    boolean negSign = (va.signum() < 0) ^ b.sign;
                    if (va.signum() == 0) return new FpResult(negSign, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
                    return new FpResult(negSign, BigInteger.ZERO, BigInteger.ZERO,
                            negSign ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF);
                }
                r = va.divide(vb, mc);
                break;
            default: return null;
        }
        return roundDecimalToFp(r, mode, eb, sb);
    }

    private FpResult arithSpecial(FpView a, FpView b, ArithOp op) {
        // NaN propagation.
        if (a.kind == Term.FpConst.Kind.NAN || b.kind == Term.FpConst.Kind.NAN) {
            return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
        }
        boolean aInf = a.kind == Term.FpConst.Kind.PLUS_INF || a.kind == Term.FpConst.Kind.MINUS_INF;
        boolean bInf = b.kind == Term.FpConst.Kind.PLUS_INF || b.kind == Term.FpConst.Kind.MINUS_INF;
        boolean aZero = a.kind == Term.FpConst.Kind.PLUS_ZERO || a.kind == Term.FpConst.Kind.MINUS_ZERO;
        boolean bZero = b.kind == Term.FpConst.Kind.PLUS_ZERO || b.kind == Term.FpConst.Kind.MINUS_ZERO;
        if (op == ArithOp.ADD || op == ArithOp.SUB) {
            // ±inf ± ∓inf = NaN.
            if (aInf && bInf) {
                boolean asign = a.sign;
                boolean bsign = (op == ArithOp.SUB) ^ b.sign;
                if (asign != bsign) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
                return new FpResult(asign, BigInteger.ZERO, BigInteger.ZERO,
                        asign ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF);
            }
            if (aInf) return new FpResult(a.sign, BigInteger.ZERO, BigInteger.ZERO, a.kind);
            if (bInf) {
                boolean negB = (op == ArithOp.SUB) ^ b.sign;
                return new FpResult(negB, BigInteger.ZERO, BigInteger.ZERO,
                        negB ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF);
            }
        }
        if (op == ArithOp.MUL) {
            if ((aInf && bZero) || (aZero && bInf)) {
                return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
            }
            if (aInf || bInf) {
                boolean sign = a.sign ^ b.sign;
                return new FpResult(sign, BigInteger.ZERO, BigInteger.ZERO,
                        sign ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF);
            }
        }
        if (op == ArithOp.DIV) {
            if (aInf && bInf) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
            if (aZero && bZero) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
            if (aInf) {
                boolean sign = a.sign ^ b.sign;
                return new FpResult(sign, BigInteger.ZERO, BigInteger.ZERO,
                        sign ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF);
            }
            if (bInf) {
                boolean sign = a.sign ^ b.sign;
                return new FpResult(sign, BigInteger.ZERO, BigInteger.ZERO,
                        sign ? Term.FpConst.Kind.MINUS_ZERO : Term.FpConst.Kind.PLUS_ZERO);
            }
        }
        return null;
    }

    private FpResult evalRem(FpView a, FpView b, int eb, int sb) {
        // fp.rem(x, y) = x - n*y where n is the nearest integer to x/y, ties to even.
        if (a.kind == Term.FpConst.Kind.NAN || b.kind == Term.FpConst.Kind.NAN
                || a.kind == Term.FpConst.Kind.PLUS_INF || a.kind == Term.FpConst.Kind.MINUS_INF
                || b.kind == Term.FpConst.Kind.PLUS_ZERO || b.kind == Term.FpConst.Kind.MINUS_ZERO) {
            return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
        }
        BigDecimal va = a.toBigDecimal();
        BigDecimal vb = b.toBigDecimal();
        if (va == null || vb == null) return null;
        BigDecimal q = va.divide(vb, 0, RoundingMode.HALF_EVEN);
        BigDecimal r = va.subtract(q.multiply(vb));
        return roundDecimalToFp(r, Term.RmConst.Mode.RNE, eb, sb);
    }

    private FpResult evalSqrt(FpView a, Term.RmConst.Mode mode, int eb, int sb) {
        if (a.kind == Term.FpConst.Kind.NAN) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
        if (a.kind == Term.FpConst.Kind.PLUS_ZERO) return new FpResult(false, BigInteger.ZERO, BigInteger.ZERO, Term.FpConst.Kind.PLUS_ZERO);
        if (a.kind == Term.FpConst.Kind.MINUS_ZERO) return new FpResult(true, BigInteger.ZERO, BigInteger.ZERO, Term.FpConst.Kind.MINUS_ZERO);
        if (a.kind == Term.FpConst.Kind.PLUS_INF) return new FpResult(false, BigInteger.ZERO, BigInteger.ZERO, Term.FpConst.Kind.PLUS_INF);
        if (a.sign) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
        BigDecimal v = a.toBigDecimal();
        if (v == null) return null;
        BigDecimal s = v.sqrt(new MathContext(64, RoundingMode.HALF_EVEN));
        return roundDecimalToFp(s, mode, eb, sb);
    }

    private FpResult evalFma(FpView a, FpView b, FpView c, Term.RmConst.Mode mode, int eb, int sb) {
        // fp.fma(x, y, z) = x*y + z, single rounding at the end.
        // Special: (NaN, _, _) etc.
        if (a.kind == Term.FpConst.Kind.NAN || b.kind == Term.FpConst.Kind.NAN || c.kind == Term.FpConst.Kind.NAN) {
            return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
        }
        BigDecimal va = a.toBigDecimal();
        BigDecimal vb = b.toBigDecimal();
        BigDecimal vc = c.toBigDecimal();
        if (va == null || vb == null || vc == null) {
            // Some operand is infinite — fallback to multi-step eval (not ideal but conservative).
            FpResult mul = evalArith(a, b, mode, eb, sb, ArithOp.MUL);
            if (mul == null) return null;
            FpView mulView = new FpView(mul, eb, sb);
            return evalArith(mulView, c, mode, eb, sb, ArithOp.ADD);
        }
        BigDecimal r = va.multiply(vb).add(vc);
        return roundDecimalToFp(r, mode, eb, sb);
    }

    // ---------- BigDecimal → FpResult (rounded to representable value of (eb, sb)) ----------

    /**
     * Round an exact BigDecimal value to the nearest representable FP of width (eb, sb), per the
     * given rounding mode. Handles overflow → infinity and underflow → subnormal/zero.
     */
    private FpResult roundDecimalToFp(BigDecimal val, Term.RmConst.Mode mode, int eb, int sb) {
        if (val.signum() == 0) return new FpResult(false, BigInteger.ZERO, BigInteger.ZERO, Term.FpConst.Kind.PLUS_ZERO);
        boolean negative = val.signum() < 0;
        BigDecimal abs = val.abs();
        // Find the unbiased exponent E such that 2^E <= abs < 2^(E+1).
        // log2(abs) ≈ log10(abs) * log2(10). Use BigDecimal.precision() + scale to get range.
        // We'll find E by scanning.
        int E = approxLog2(abs);
        // Refine E: ensure 2^E <= abs < 2^(E+1).
        BigDecimal twoE = pow2(E);
        while (abs.compareTo(twoE) < 0) { E--; twoE = pow2(E); }
        while (abs.compareTo(twoE.multiply(BigDecimal.valueOf(2))) >= 0) { E++; twoE = pow2(E); }
        int bias = (1 << (eb - 1)) - 1;
        int eMax = (1 << eb) - 1 - 1 - bias; // unbiased max exponent for normal
        int eMin = 1 - bias; // unbiased min exponent for normal
        // Significand precision = sb (including hidden bit).
        // We compute m = abs / 2^E, scaled by 2^(sb-1), rounded per mode → integer in [2^(sb-1), 2^sb).
        if (E > eMax) {
            // Overflow.
            return overflowResult(negative, mode, eb, sb);
        }
        int effectiveExp;
        BigInteger sig;
        if (E < eMin) {
            // Subnormal: use exponent eMin, scale m differently.
            effectiveExp = eMin;
            BigDecimal scale = pow2(eMin - (sb - 1));
            BigDecimal m = abs.divide(scale, 0, javaRounding(mode, negative));
            BigInteger mi = m.toBigInteger();
            if (mi.signum() == 0) {
                return new FpResult(negative, BigInteger.ZERO, BigInteger.ZERO,
                        negative ? Term.FpConst.Kind.MINUS_ZERO : Term.FpConst.Kind.PLUS_ZERO);
            }
            // If mi >= 2^(sb-1), promote to normal with exp = eMin.
            if (mi.compareTo(BigInteger.ONE.shiftLeft(sb - 1)) >= 0) {
                BigInteger sigBits = mi.subtract(BigInteger.ONE.shiftLeft(sb - 1));
                BigInteger expBits = BigInteger.valueOf(eMin + bias);
                return new FpResult(negative, expBits, sigBits, Term.FpConst.Kind.NORMAL);
            }
            // Subnormal: stored exponent = 0, sig = mi.
            return new FpResult(negative, BigInteger.ZERO, mi, Term.FpConst.Kind.NORMAL);
        } else {
            effectiveExp = E;
            BigDecimal scale = pow2(E - (sb - 1));
            BigDecimal m = abs.divide(scale, 0, javaRounding(mode, negative));
            BigInteger mi = m.toBigInteger();
            // Possibly mi == 2^sb due to rounding-up — then exponent goes up by one.
            if (mi.compareTo(BigInteger.ONE.shiftLeft(sb)) >= 0) {
                effectiveExp++;
                if (effectiveExp > eMax) return overflowResult(negative, mode, eb, sb);
                // mi /= 2.
                mi = mi.shiftRight(1);
            }
            BigInteger sigBits = mi.subtract(BigInteger.ONE.shiftLeft(sb - 1));
            BigInteger expBits = BigInteger.valueOf(effectiveExp + bias);
            return new FpResult(negative, expBits, sigBits, Term.FpConst.Kind.NORMAL);
        }
    }

    private static int approxLog2(BigDecimal abs) {
        // log2(x) = ln(x)/ln(2); use BigDecimal precision to bracket.
        // Use Java double for approximation; refined later.
        double d = abs.doubleValue();
        if (Double.isInfinite(d)) {
            // Way larger than double — return a big positive estimate via precision.
            return abs.precision() * 4;
        }
        if (d == 0.0) {
            // Way smaller than double — large negative estimate.
            return -(abs.scale() * 4);
        }
        return (int) Math.floor(Math.log(d) / Math.log(2));
    }

    private static BigDecimal pow2(int e) {
        if (e >= 0) return new BigDecimal(BigInteger.ONE.shiftLeft(e));
        // 2^-e in decimal: 1 / 2^|e|. We need exact representation; use BigDecimal divide with scale.
        BigInteger denom = BigInteger.ONE.shiftLeft(-e);
        return BigDecimal.ONE.divide(new BigDecimal(denom), -e + 8, RoundingMode.HALF_EVEN);
    }

    private static RoundingMode javaRounding(Term.RmConst.Mode mode, boolean negative) {
        return switch (mode) {
            case RNE -> RoundingMode.HALF_EVEN;
            case RNA -> RoundingMode.HALF_UP;
            case RTP -> negative ? RoundingMode.DOWN : RoundingMode.UP;
            case RTN -> negative ? RoundingMode.UP : RoundingMode.DOWN;
            case RTZ -> RoundingMode.DOWN;
        };
    }

    private FpResult overflowResult(boolean negative, Term.RmConst.Mode mode, int eb, int sb) {
        // RTZ: clamps to max-finite. RTP for negative + RTN for positive: clamp to max-finite.
        // Otherwise: overflow to infinity.
        boolean clamp = mode == Term.RmConst.Mode.RTZ
                || (mode == Term.RmConst.Mode.RTP && negative)
                || (mode == Term.RmConst.Mode.RTN && !negative);
        if (clamp) {
            // Max finite: exp = (2^eb - 2), sig = 2^(sb-1) - 1.
            BigInteger expBits = BigInteger.ONE.shiftLeft(eb).subtract(BigInteger.TWO);
            BigInteger sigBits = BigInteger.ONE.shiftLeft(sb - 1).subtract(BigInteger.ONE);
            return new FpResult(negative, expBits, sigBits, Term.FpConst.Kind.NORMAL);
        }
        return new FpResult(negative, BigInteger.ZERO, BigInteger.ZERO,
                negative ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF);
    }

    // ---------- encode FpResult → FpConst ----------

    private Term encodeFp(FpResult r, int eb, int sb) {
        return tf.mkFp(r.sign, r.exp, r.sig, eb, sb, r.kind);
    }

    // ---------- helpers ----------

    private static boolean matches(int eb, int sb, int targetEb, int targetSb) {
        return eb == targetEb && sb == targetSb;
    }

    /** A view over an Fp literal that can decode it to BigDecimal / Java float / Java double. */
    static final class FpView {
        final boolean sign;
        final BigInteger exp, sig;
        final int eb, sb;
        final Term.FpConst.Kind kind;
        FpView(Term.FpConst f) { this(f.sign, f.exp, f.sig, f.eb, f.sb, f.kind); }
        FpView(FpResult r, int eb, int sb) { this(r.sign, r.exp, r.sig, eb, sb, r.kind); }
        FpView(boolean sign, BigInteger exp, BigInteger sig, int eb, int sb, Term.FpConst.Kind kind) {
            this.sign = sign; this.exp = exp; this.sig = sig; this.eb = eb; this.sb = sb; this.kind = kind;
        }

        /** Returns the exact rational value as BigDecimal, or null for NaN/Inf. */
        BigDecimal toBigDecimal() {
            if (kind == Term.FpConst.Kind.NAN || kind == Term.FpConst.Kind.PLUS_INF
                    || kind == Term.FpConst.Kind.MINUS_INF) return null;
            if (kind == Term.FpConst.Kind.PLUS_ZERO || kind == Term.FpConst.Kind.MINUS_ZERO) return BigDecimal.ZERO;
            int bias = (1 << (eb - 1)) - 1;
            BigInteger m;
            int E;
            if (exp.signum() == 0) {
                // Subnormal: value = sig * 2^(1 - bias - (sb-1))
                m = sig;
                E = 1 - bias - (sb - 1);
            } else {
                m = BigInteger.ONE.shiftLeft(sb - 1).add(sig); // hidden 1 + sig
                E = exp.intValue() - bias - (sb - 1);
            }
            BigDecimal val;
            if (E >= 0) val = new BigDecimal(m.shiftLeft(E));
            else {
                BigDecimal denom = new BigDecimal(BigInteger.ONE.shiftLeft(-E));
                val = new BigDecimal(m).divide(denom, -E + 8, RoundingMode.HALF_EVEN);
            }
            return sign ? val.negate() : val;
        }

        float toJavaFloat() {
            if (kind == Term.FpConst.Kind.NAN) return Float.NaN;
            if (kind == Term.FpConst.Kind.PLUS_INF) return Float.POSITIVE_INFINITY;
            if (kind == Term.FpConst.Kind.MINUS_INF) return Float.NEGATIVE_INFINITY;
            if (kind == Term.FpConst.Kind.PLUS_ZERO) return 0.0f;
            if (kind == Term.FpConst.Kind.MINUS_ZERO) return -0.0f;
            int bits = (sign ? 0x80000000 : 0) | (exp.intValue() << 23) | sig.intValue();
            return Float.intBitsToFloat(bits);
        }

        double toJavaDouble() {
            if (kind == Term.FpConst.Kind.NAN) return Double.NaN;
            if (kind == Term.FpConst.Kind.PLUS_INF) return Double.POSITIVE_INFINITY;
            if (kind == Term.FpConst.Kind.MINUS_INF) return Double.NEGATIVE_INFINITY;
            if (kind == Term.FpConst.Kind.PLUS_ZERO) return 0.0;
            if (kind == Term.FpConst.Kind.MINUS_ZERO) return -0.0;
            long bits = (sign ? Long.MIN_VALUE : 0L) | (exp.longValue() << 52) | sig.longValue();
            return Double.longBitsToDouble(bits);
        }
    }

    /** Result of an FP operation: ready-to-encode bits + classification kind. */
    static final class FpResult {
        final boolean sign;
        final BigInteger exp, sig;
        final Term.FpConst.Kind kind;
        FpResult(boolean sign, BigInteger exp, BigInteger sig, Term.FpConst.Kind kind) {
            this.sign = sign; this.exp = exp; this.sig = sig; this.kind = kind;
        }

        static FpResult fromFloat(float f) {
            if (Float.isNaN(f)) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
            if (f == Float.POSITIVE_INFINITY) {
                BigInteger e = BigInteger.ONE.shiftLeft(8).subtract(BigInteger.ONE);
                return new FpResult(false, e, BigInteger.ZERO, Term.FpConst.Kind.PLUS_INF);
            }
            if (f == Float.NEGATIVE_INFINITY) {
                BigInteger e = BigInteger.ONE.shiftLeft(8).subtract(BigInteger.ONE);
                return new FpResult(true, e, BigInteger.ZERO, Term.FpConst.Kind.MINUS_INF);
            }
            int bits = Float.floatToRawIntBits(f);
            boolean sign = (bits & 0x80000000) != 0;
            int expBits = (bits >> 23) & 0xff;
            int sigBits = bits & 0x7fffff;
            if (expBits == 0 && sigBits == 0) {
                return new FpResult(sign, BigInteger.ZERO, BigInteger.ZERO,
                        sign ? Term.FpConst.Kind.MINUS_ZERO : Term.FpConst.Kind.PLUS_ZERO);
            }
            return new FpResult(sign, BigInteger.valueOf(expBits & 0xffL),
                    BigInteger.valueOf(sigBits & 0xffffffL), Term.FpConst.Kind.NORMAL);
        }

        static FpResult fromDouble(double d) {
            if (Double.isNaN(d)) return new FpResult(false, BigInteger.ZERO, BigInteger.ONE, Term.FpConst.Kind.NAN);
            if (d == Double.POSITIVE_INFINITY) {
                BigInteger e = BigInteger.ONE.shiftLeft(11).subtract(BigInteger.ONE);
                return new FpResult(false, e, BigInteger.ZERO, Term.FpConst.Kind.PLUS_INF);
            }
            if (d == Double.NEGATIVE_INFINITY) {
                BigInteger e = BigInteger.ONE.shiftLeft(11).subtract(BigInteger.ONE);
                return new FpResult(true, e, BigInteger.ZERO, Term.FpConst.Kind.MINUS_INF);
            }
            long bits = Double.doubleToRawLongBits(d);
            boolean sign = (bits & Long.MIN_VALUE) != 0;
            long expBits = (bits >>> 52) & 0x7ffL;
            long sigBits = bits & 0xfffffffffffffL;
            if (expBits == 0 && sigBits == 0) {
                return new FpResult(sign, BigInteger.ZERO, BigInteger.ZERO,
                        sign ? Term.FpConst.Kind.MINUS_ZERO : Term.FpConst.Kind.PLUS_ZERO);
            }
            return new FpResult(sign, BigInteger.valueOf(expBits), BigInteger.valueOf(sigBits), Term.FpConst.Kind.NORMAL);
        }
    }
}
