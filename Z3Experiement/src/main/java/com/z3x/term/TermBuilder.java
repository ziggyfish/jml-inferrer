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
        if (!(head instanceof SExpr.Atom op)) {
            throw new IllegalStateException("Compound head not yet supported: " + head);
        }
        String name = op.text();
        if (name.equals("_") && l.items().size() == 3) {
            // (_ bvN W) bit-vector literal
            SExpr.Atom valAtom = (SExpr.Atom) l.items().get(1);
            String valName = valAtom.text();
            if (valName.startsWith("bv")) {
                BigInteger val = new BigInteger(valName.substring(2));
                int w = Integer.parseInt(((SExpr.Atom) l.items().get(2)).text());
                return tf.mkBv(val, w);
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
            case "bvult","bvule","bvugt","bvuge","bvslt","bvsle","bvsgt","bvsge"
                    -> tf.mkAppRaw(name, args, Sort.BOOL);
            default         -> tf.mkApp(name, args);
        };
    }

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
