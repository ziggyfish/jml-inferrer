import org.apache.commons.lang3.math.NumberUtils;
import org.apache.commons.lang3.BooleanUtils;
import org.apache.commons.lang3.CharUtils;
import org.apache.commons.lang3.Validate;
import org.apache.commons.lang3.Range;
import org.apache.commons.lang3.mutable.MutableInt;
import org.apache.commons.lang3.mutable.MutableDouble;
import org.apache.commons.lang3.mutable.MutableBoolean;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.MutablePair;

/**
 * Workload driver to exercise the same 11 Apache Commons Lang classes used in
 * Article 1, so Daikon (via Chicory instrumentation) can observe runtime
 * values and report likely invariants for their methods.
 *
 * NOTE: this is a hand-written exerciser. Daikon's output depends entirely on
 * what this driver exercises (coverage-dependence is the defining property of
 * dynamic invariant detection), so the workload is deliberately broad: valid
 * inputs, boundary values, negatives, and zero, across each method. The
 * workload choice is itself a confound and is reported as such in the
 * comparison.
 */
public class DaikonDriver {

    public static void main(String[] args) {
        for (int rep = 0; rep < 3; rep++) {
            numberUtils();
            booleanUtils();
            charUtils();
            mutableInt();
            mutableDouble();
            mutableBoolean();
            pairAndMutablePair();
            range();
            validate();
        }
        System.out.println("driver done");
    }

    static void numberUtils() {
        int[] xs = {0, 1, -1, 42, -42, Integer.MAX_VALUE, Integer.MIN_VALUE, 7, 100};
        String[] ss = {"0", "1", "-1", "42", "abc", "", "3.14", "2147483647", "  9 ", null};
        for (String s : ss) {
            try { NumberUtils.toInt(s); } catch (Throwable t) {}
            try { NumberUtils.toInt(s, 99); } catch (Throwable t) {}
            try { NumberUtils.toDouble(s); } catch (Throwable t) {}
            try { NumberUtils.toLong(s); } catch (Throwable t) {}
            try { NumberUtils.isCreatable(s); } catch (Throwable t) {}
            try { NumberUtils.isDigits(s); } catch (Throwable t) {}
            try { NumberUtils.isParsable(s); } catch (Throwable t) {}
        }
        for (int a : xs) {
            for (int b : new int[]{0, 1, -1, 42}) {
                try { NumberUtils.max(a, b); } catch (Throwable t) {}
                try { NumberUtils.min(a, b); } catch (Throwable t) {}
                try { NumberUtils.compare(a, b); } catch (Throwable t) {}
                try { NumberUtils.max(a, b, 5); } catch (Throwable t) {}
                try { NumberUtils.min(a, b, 5); } catch (Throwable t) {}
            }
        }
    }

    static void booleanUtils() {
        Boolean[] bs = {Boolean.TRUE, Boolean.FALSE, null};
        for (Boolean b : bs) {
            try { BooleanUtils.toStringTrueFalse(b == null ? false : b); } catch (Throwable t) {}
            try { BooleanUtils.isTrue(b); } catch (Throwable t) {}
            try { BooleanUtils.isFalse(b); } catch (Throwable t) {}
            try { BooleanUtils.toInteger(b == null ? false : b); } catch (Throwable t) {}
            try { BooleanUtils.toStringYesNo(b == null ? false : b); } catch (Throwable t) {}
            try { BooleanUtils.negate(b); } catch (Throwable t) {}
        }
        for (boolean a : new boolean[]{true, false}) {
            for (boolean b : new boolean[]{true, false}) {
                try { BooleanUtils.and(new boolean[]{a, b}); } catch (Throwable t) {}
                try { BooleanUtils.or(new boolean[]{a, b}); } catch (Throwable t) {}
                try { BooleanUtils.xor(new boolean[]{a, b}); } catch (Throwable t) {}
                try { BooleanUtils.toInteger(a); } catch (Throwable t) {}
            }
        }
    }

    static void charUtils() {
        char[] cs = {'a', 'Z', '0', '9', ' ', '\n', '~', (char) 200, '@'};
        for (char c : cs) {
            try { CharUtils.toIntValue(c); } catch (Throwable t) {}
            try { CharUtils.isAscii(c); } catch (Throwable t) {}
            try { CharUtils.isAsciiNumeric(c); } catch (Throwable t) {}
            try { CharUtils.isAsciiAlpha(c); } catch (Throwable t) {}
            try { CharUtils.isAsciiAlphanumeric(c); } catch (Throwable t) {}
            try { CharUtils.isAsciiControl(c); } catch (Throwable t) {}
            try { CharUtils.toString(c); } catch (Throwable t) {}
        }
    }

    static void mutableInt() {
        int[] xs = {0, 1, -1, 10, -10, 100};
        for (int x : xs) {
            MutableInt m = new MutableInt(x);
            try { m.increment(); } catch (Throwable t) {}
            try { m.decrement(); } catch (Throwable t) {}
            try { m.add(5); } catch (Throwable t) {}
            try { m.subtract(3); } catch (Throwable t) {}
            try { m.intValue(); } catch (Throwable t) {}
            try { m.getValue(); } catch (Throwable t) {}
            try { m.setValue(x * 2); } catch (Throwable t) {}
            try { m.compareTo(new MutableInt(x)); } catch (Throwable t) {}
            try { m.toInteger(); } catch (Throwable t) {}
        }
    }

    static void mutableDouble() {
        double[] xs = {0.0, 1.5, -1.5, 10.0, -0.0, 3.14159};
        for (double x : xs) {
            MutableDouble m = new MutableDouble(x);
            try { m.add(2.0); } catch (Throwable t) {}
            try { m.subtract(1.0); } catch (Throwable t) {}
            try { m.increment(); } catch (Throwable t) {}
            try { m.doubleValue(); } catch (Throwable t) {}
            try { m.intValue(); } catch (Throwable t) {}
            try { m.setValue(x + 1); } catch (Throwable t) {}
            try { m.isNaN(); } catch (Throwable t) {}
            try { m.compareTo(new MutableDouble(x)); } catch (Throwable t) {}
        }
    }

    static void mutableBoolean() {
        for (boolean b : new boolean[]{true, false}) {
            MutableBoolean m = new MutableBoolean(b);
            try { m.setValue(!b); } catch (Throwable t) {}
            try { m.booleanValue(); } catch (Throwable t) {}
            try { m.isTrue(); } catch (Throwable t) {}
            try { m.isFalse(); } catch (Throwable t) {}
            try { m.toBoolean(); } catch (Throwable t) {}
            try { m.setTrue(); } catch (Throwable t) {}
            try { m.setFalse(); } catch (Throwable t) {}
            try { m.compareTo(new MutableBoolean(b)); } catch (Throwable t) {}
        }
    }

    static void pairAndMutablePair() {
        for (int i = 0; i < 5; i++) {
            Pair<String, Integer> p = Pair.of("k" + i, i);
            try { p.getLeft(); } catch (Throwable t) {}
            try { p.getRight(); } catch (Throwable t) {}
            try { p.getKey(); } catch (Throwable t) {}
            try { p.getValue(); } catch (Throwable t) {}
            try { p.toString(); } catch (Throwable t) {}

            MutablePair<String, Integer> mp = MutablePair.of("m" + i, i);
            try { mp.setLeft("x" + i); } catch (Throwable t) {}
            try { mp.setRight(i * 2); } catch (Throwable t) {}
            try { mp.setValue(i * 3); } catch (Throwable t) {}
            try { mp.getLeft(); } catch (Throwable t) {}
            try { mp.getRight(); } catch (Throwable t) {}
        }
    }

    static void range() {
        Range<Integer> r = Range.between(1, 10);
        int[] probes = {0, 1, 5, 10, 11, -3, 100};
        for (int x : probes) {
            try { r.contains(x); } catch (Throwable t) {}
            try { r.isBefore(x); } catch (Throwable t) {}
            try { r.isAfter(x); } catch (Throwable t) {}
            try { r.isStartedBy(x); } catch (Throwable t) {}
            try { r.isEndedBy(x); } catch (Throwable t) {}
        }
        try { r.getMinimum(); } catch (Throwable t) {}
        try { r.getMaximum(); } catch (Throwable t) {}
        try { r.containsRange(Range.between(2, 5)); } catch (Throwable t) {}
    }

    static void validate() {
        // Validate methods throw on failure; exercise mostly the passing path
        // plus a few failing ones (caught) so Daikon sees both outcomes.
        for (int i = -2; i <= 3; i++) {
            try { Validate.isTrue(i >= 0); } catch (Throwable t) {}
            try { Validate.isTrue(i > 0, "msg"); } catch (Throwable t) {}
            try { Validate.notNull(i == 0 ? null : Integer.valueOf(i)); } catch (Throwable t) {}
            try { Validate.inclusiveBetween(0, 5, i); } catch (Throwable t) {}
            try { Validate.exclusiveBetween(0, 5, i); } catch (Throwable t) {}
        }
    }
}
