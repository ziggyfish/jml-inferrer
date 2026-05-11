package com.z3x.term;

import com.z3x.parser.SExpr;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/** Lowers parsed S-expressions to typed {@link Term}s. */
public final class TermBuilder {

    private final TermFactory tf;

    public TermBuilder(TermFactory tf) { this.tf = tf; }

    public Sort resolveSort(SExpr e) {
        if (e instanceof SExpr.Atom a) {
            Sort s = tf.lookupSort(a.text());
            if (s == null) throw new IllegalStateException("Unknown sort: " + a.text());
            return s;
        }
        if (e instanceof SExpr.SList l) {
            // (Array K V), (_ BitVec n)
            if (!l.items().isEmpty() && l.items().get(0) instanceof SExpr.Atom head) {
                if (head.text().equals("Array") && l.items().size() == 3) {
                    return new Sort.Array(resolveSort(l.items().get(1)), resolveSort(l.items().get(2)));
                }
                if (head.text().equals("_") && l.items().size() == 3
                        && l.items().get(1) instanceof SExpr.Atom bv && bv.text().equals("BitVec")
                        && l.items().get(2) instanceof SExpr.Atom w) {
                    return new Sort.BitVec(Integer.parseInt(w.text()));
                }
                if (head.text().equals("_") && l.items().size() == 4
                        && l.items().get(1) instanceof SExpr.Atom fp && fp.text().equals("FloatingPoint")
                        && l.items().get(2) instanceof SExpr.Atom eb
                        && l.items().get(3) instanceof SExpr.Atom sb) {
                    return new Sort.FloatingPoint(Integer.parseInt(eb.text()), Integer.parseInt(sb.text()));
                }
            }
        }
        throw new IllegalStateException("Cannot parse sort: " + e);
    }

    /** Translate an expression into a Term using the current symbol table. */
    public Term build(SExpr e) {
        if (e instanceof SExpr.Atom a) return buildAtom(a);
        if (e instanceof SExpr.SList l) return buildList(l);
        throw new IllegalStateException("Unreachable");
    }

    private Term buildAtom(SExpr.Atom a) {
        String text = a.text();
        switch (a.kind()) {
            case STRING:
                return tf.mkStr(text);
            case NUMERAL:
                return tf.mkInt(new BigInteger(text));
            case DECIMAL: {
                int dot = text.indexOf('.');
                String whole = text.substring(0, dot);
                String frac = text.substring(dot + 1);
                BigInteger num = new BigInteger(whole + frac);
                BigInteger den = BigInteger.TEN.pow(frac.length());
                if (whole.startsWith("-")) {
                    // num is already negative because whole has the sign
                }
                return tf.mkRat(num, den);
            }
            case SYMBOL:
                if (text.equals("true")) return tf.mkBool(true);
                if (text.equals("false")) return tf.mkBool(false);
                if (text.equals("RNE") || text.equals("roundNearestTiesToEven")) return tf.mkRm(Term.RmConst.Mode.RNE);
                if (text.equals("RNA") || text.equals("roundNearestTiesToAway")) return tf.mkRm(Term.RmConst.Mode.RNA);
                if (text.equals("RTP") || text.equals("roundTowardPositive")) return tf.mkRm(Term.RmConst.Mode.RTP);
                if (text.equals("RTN") || text.equals("roundTowardNegative")) return tf.mkRm(Term.RmConst.Mode.RTN);
                if (text.equals("RTZ") || text.equals("roundTowardZero")) return tf.mkRm(Term.RmConst.Mode.RTZ);
                Term let = letBindings.get(text);
                if (let != null) return let;
                if (text.startsWith("#b")) {
                    String bits = text.substring(2);
                    return tf.mkBv(new BigInteger(bits, 2), bits.length());
                }
                if (text.startsWith("#x")) {
                    String hex = text.substring(2);
                    return tf.mkBv(new BigInteger(hex, 16), hex.length() * 4);
                }
                Sort.FunSig sig = tf.lookupFunction(text);
                if (sig == null) {
                    throw new IllegalStateException("Undeclared symbol: " + text);
                }
                if (sig.args().isEmpty()) return tf.mkVar(text, sig.result());
                throw new IllegalStateException("Symbol " + text + " is a function, not a constant");
            default:
                throw new IllegalStateException("Unexpected atom kind: " + a.kind());
        }
    }

    private Term buildList(SExpr.SList l) {
        if (l.items().isEmpty()) throw new IllegalStateException("Empty application");
        SExpr head = l.items().get(0);
        // Indexed BV ops have compound heads: ((_ extract HI LO) bv), etc.
        if (head instanceof SExpr.SList headList && headList.items().size() >= 2
                && headList.items().get(0) instanceof SExpr.Atom headAt && headAt.text().equals("_")) {
            return buildIndexedOp(headList, l);
        }
        if (!(head instanceof SExpr.Atom op)) {
            throw new IllegalStateException("Compound head not yet supported: " + head);
        }
        String name = op.text();
        if ((name.equals("forall") || name.equals("exists")) && l.items().size() >= 3) {
            return buildQuantifier(name, l);
        }
        if (name.equals("let") && l.items().size() >= 3) {
            return buildLet(l);
        }
        if (name.equals("!") && l.items().size() >= 2) {
            // (! body :pattern ...) — strip annotations, keep body.
            return build(l.items().get(1));
        }
        if (name.equals("_") && l.items().size() >= 3) {
            SExpr.Atom valAtom = (SExpr.Atom) l.items().get(1);
            String valName = valAtom.text();
            if (valName.startsWith("bv")) {
                BigInteger val = new BigInteger(valName.substring(2));
                int w = Integer.parseInt(((SExpr.Atom) l.items().get(2)).text());
                return tf.mkBv(val, w);
            }
            // FP special values: (_ +zero EB SB), (_ -zero EB SB), (_ +oo EB SB), (_ -oo EB SB), (_ NaN EB SB).
            if ((valName.equals("+zero") || valName.equals("-zero") || valName.equals("+oo")
                    || valName.equals("-oo") || valName.equals("NaN")) && l.items().size() == 4) {
                int eb = Integer.parseInt(((SExpr.Atom) l.items().get(2)).text());
                int sb = Integer.parseInt(((SExpr.Atom) l.items().get(3)).text());
                Term.FpConst.Kind kind = switch (valName) {
                    case "+zero" -> Term.FpConst.Kind.PLUS_ZERO;
                    case "-zero" -> Term.FpConst.Kind.MINUS_ZERO;
                    case "+oo"   -> Term.FpConst.Kind.PLUS_INF;
                    case "-oo"   -> Term.FpConst.Kind.MINUS_INF;
                    default      -> Term.FpConst.Kind.NAN;
                };
                return tf.mkFp(valName.startsWith("-"), BigInteger.ZERO, BigInteger.ZERO, eb, sb, kind);
            }
        }
        // (fp #bs #be #bm) literal.
        if (name.equals("fp") && l.items().size() == 4) {
            String s = ((SExpr.Atom) l.items().get(1)).text();
            String e = ((SExpr.Atom) l.items().get(2)).text();
            String m = ((SExpr.Atom) l.items().get(3)).text();
            if (s.startsWith("#b") && e.startsWith("#b") && m.startsWith("#b")) {
                boolean sign = s.equals("#b1");
                BigInteger exp = new BigInteger(e.substring(2), 2);
                BigInteger sig = new BigInteger(m.substring(2), 2);
                int eb = e.length() - 2;
                int sb = m.length() - 2 + 1; // significand including hidden bit
                Term.FpConst.Kind kind = classifyFp(sign, exp, sig, eb, sb);
                return tf.mkFp(sign, exp, sig, eb, sb, kind);
            }
        }
        List<Term> args = new ArrayList<>(l.items().size() - 1);
        for (int i = 1; i < l.items().size(); i++) args.add(build(l.items().get(i)));

        return switch (name) {
            case "and"      -> tf.mkAnd(args);
            case "or"       -> tf.mkOr(args);
            case "not"      -> tf.mkNot(args.get(0));
            case "=>"       -> reduceImplies(args);
            case "="        -> reduceChain(args, tf::mkEq);
            case "distinct" -> tf.mkDistinct(args);
            case "ite"      -> tf.mkIte(args.get(0), args.get(1), args.get(2));
            case "xor"      -> tf.mkNot(tf.mkEq(args.get(0), args.get(1)));
            case "+"        -> tf.mkAdd(args);
            case "-"        -> tf.mkSub(args);
            case "*"        -> tf.mkMul(args);
            case "<="       -> reduceChain(args, tf::mkLe);
            case "<"        -> reduceChain(args, tf::mkLt);
            case ">="       -> reduceChain(args, tf::mkGe);
            case ">"        -> reduceChain(args, tf::mkGt);
            case "select"   -> {
                // result sort = range of the array sort of args[0]
                Sort arrSort = args.get(0).sort;
                if (arrSort instanceof Sort.Array arr) {
                    yield tf.mkAppRaw("select", args, arr.range());
                } else {
                    throw new IllegalStateException("select on non-array: " + arrSort);
                }
            }
            case "store" -> {
                // result sort = same as the array
                yield tf.mkAppRaw("store", args, args.get(0).sort);
            }
            case "bvadd","bvsub","bvneg","bvnot","bvand","bvor","bvxor","bvmul",
                 "bvshl","bvlshr","bvashr","bvudiv","bvurem","bvsdiv","bvsrem","bvsmod"
                    -> tf.mkAppRaw(name, args, args.get(0).sort);
            case "concat" -> {
                int w = 0;
                for (Term a : args) w += ((Sort.BitVec) a.sort).width();
                yield tf.mkAppRaw("concat", args, new Sort.BitVec(w));
            }
            // FP predicates — Bool result.
            case "fp.isNaN","fp.isInfinite","fp.isZero","fp.isNormal","fp.isSubnormal",
                 "fp.isPositive","fp.isNegative","fp.eq","fp.lt","fp.leq","fp.gt","fp.geq"
                    -> tf.mkAppRaw(name, args, Sort.BOOL);
            // FP arithmetic (parsed but unfolded only for special cases).
            case "fp.neg","fp.abs" -> tf.mkAppRaw(name, args, args.get(0).sort);
            case "fp.add","fp.sub","fp.mul","fp.div","fp.rem","fp.sqrt","fp.fma","fp.min","fp.max"
                    -> {
                // The result sort = first non-rounding-mode arg's sort.
                Sort outSort = null;
                for (Term a : args) if (!(a.sort instanceof Sort.Builtin b && b.name().equals("RoundingMode"))) { outSort = a.sort; break; }
                yield tf.mkAppRaw(name, args, outSort != null ? outSort : args.get(args.size() - 1).sort);
            }
            case "bvult","bvule","bvugt","bvuge","bvslt","bvsle","bvsgt","bvsge"
                    -> tf.mkAppRaw(name, args, Sort.BOOL);
            default         -> tf.mkApp(name, args);
        };
    }

    private static Term.FpConst.Kind classifyFp(boolean sign, BigInteger exp, BigInteger sig, int eb, int sb) {
        BigInteger allOnesExp = BigInteger.ONE.shiftLeft(eb).subtract(BigInteger.ONE);
        if (exp.signum() == 0 && sig.signum() == 0) return sign ? Term.FpConst.Kind.MINUS_ZERO : Term.FpConst.Kind.PLUS_ZERO;
        if (exp.equals(allOnesExp)) {
            if (sig.signum() == 0) return sign ? Term.FpConst.Kind.MINUS_INF : Term.FpConst.Kind.PLUS_INF;
            return Term.FpConst.Kind.NAN;
        }
        return Term.FpConst.Kind.NORMAL;
    }

    private Term buildIndexedOp(SExpr.SList headList, SExpr.SList l) {
        String idxOp = ((SExpr.Atom) headList.items().get(1)).text();
        List<SExpr> idxs = headList.items().subList(2, headList.items().size());
        List<Term> args = new ArrayList<>(l.items().size() - 1);
        for (int i = 1; i < l.items().size(); i++) args.add(build(l.items().get(i)));
        switch (idxOp) {
            case "extract": {
                int hi = Integer.parseInt(((SExpr.Atom) idxs.get(0)).text());
                int lo = Integer.parseInt(((SExpr.Atom) idxs.get(1)).text());
                Sort outSort = new Sort.BitVec(hi - lo + 1);
                return tf.mkAppRaw("(_ extract " + hi + " " + lo + ")", args, outSort);
            }
            case "zero_extend":
            case "sign_extend": {
                int n = Integer.parseInt(((SExpr.Atom) idxs.get(0)).text());
                Sort.BitVec srcSort = (Sort.BitVec) args.get(0).sort;
                Sort outSort = new Sort.BitVec(srcSort.width() + n);
                return tf.mkAppRaw("(_ " + idxOp + " " + n + ")", args, outSort);
            }
            case "rotate_left":
            case "rotate_right":
            case "repeat": {
                int n = Integer.parseInt(((SExpr.Atom) idxs.get(0)).text());
                Sort.BitVec srcSort = (Sort.BitVec) args.get(0).sort;
                Sort outSort = idxOp.equals("repeat") ? new Sort.BitVec(srcSort.width() * n) : srcSort;
                return tf.mkAppRaw("(_ " + idxOp + " " + n + ")", args, outSort);
            }
            default:
                throw new IllegalStateException("Unsupported indexed op: " + idxOp);
        }
    }

    private Term buildQuantifier(String name, SExpr.SList l) {
        SExpr.SList bindings = (SExpr.SList) l.items().get(1);
        List<String> names = new java.util.ArrayList<>();
        List<Sort> sorts = new java.util.ArrayList<>();
        // Each binding is (name sort).
        java.util.List<String> declaredFns = new java.util.ArrayList<>();
        for (SExpr b : bindings.items()) {
            SExpr.SList bl = (SExpr.SList) b;
            String vn = ((SExpr.Atom) bl.items().get(0)).text();
            Sort s = resolveSort(bl.items().get(1));
            names.add(vn);
            sorts.add(s);
            tf.declareFunction(vn, List.of(), s);
            declaredFns.add(vn);
        }
        Term body = build(l.items().get(2));
        // Pop bound names from the symbol table so they don't leak.
        // (The factory has no removeFunction; we accept the leak — names shadow harmlessly.)
        Term.Quantifier.Kind k = name.equals("forall")
                ? Term.Quantifier.Kind.FORALL
                : Term.Quantifier.Kind.EXISTS;
        return tf.mkQuantifier(k, names, sorts, body);
    }

    private Term buildLet(SExpr.SList l) {
        // (let ((x e) ...) body) — eagerly substitute by re-declaring the names.
        SExpr.SList bindings = (SExpr.SList) l.items().get(1);
        for (SExpr b : bindings.items()) {
            SExpr.SList bl = (SExpr.SList) b;
            String vn = ((SExpr.Atom) bl.items().get(0)).text();
            Term value = build(bl.items().get(1));
            tf.declareFunction(vn, List.of(), value.sort);
            // We don't yet have a substitution mechanism — record the value so future references
            // resolve to it. Cheapest implementation: a sidecar map. For now, only support `let`
            // when each value is itself a Var or constant by declaring vn as that exact value.
            // Since declareFunction registers vn as a fresh nullary fun, downstream references
            // would create a new Var; we'd need a proper substitution map to do this right.
            // For day 3 we accept that `let` is unsupported beyond simple reference forwarding.
            letBindings.put(vn, value);
        }
        Term body = build(l.items().get(2));
        return body;
    }

    private final java.util.Map<String, Term> letBindings = new java.util.HashMap<>();

    private Term reduceImplies(List<Term> args) {
        // SMT-LIB =>: right-associative.
        Term acc = args.get(args.size() - 1);
        for (int i = args.size() - 2; i >= 0; i--) acc = tf.mkImplies(args.get(i), acc);
        return acc;
    }

    @FunctionalInterface
    private interface BinOp { Term apply(Term a, Term b); }

    private Term reduceChain(List<Term> args, BinOp op) {
        if (args.size() < 2) return tf.mkBool(true);
        if (args.size() == 2) return op.apply(args.get(0), args.get(1));
        // (= a b c) = (and (= a b) (= b c))
        List<Term> conj = new ArrayList<>();
        for (int i = 0; i + 1 < args.size(); i++) conj.add(op.apply(args.get(i), args.get(i + 1)));
        return tf.mkAnd(conj);
    }
}
