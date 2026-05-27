/**
 * Synthetic client of Apache Commons Lang. Each method calls one (or a few)
 * library methods so that, when the inferrer is run with the compositional
 * pass against version V_old vs V_new of the library, the client method's
 * derived contract changes exactly when the underlying library method's
 * contract changed between the two versions.
 *
 * This is the workload for Experiment 01 H2 (client-side propagation): a
 * library change should propagate into the contracts of code that uses it.
 */
public class Client {

    // --- NumberUtils ---
    public static int parseOr(String s, int def)            { return org.apache.commons.lang3.math.NumberUtils.toInt(s, def); }
    public static long parseLongOr(String s)                { return org.apache.commons.lang3.math.NumberUtils.toLong(s); }
    public static double parseDoubleOr(String s)            { return org.apache.commons.lang3.math.NumberUtils.toDouble(s); }
    public static boolean looksCreatable(String s)          { return org.apache.commons.lang3.math.NumberUtils.isCreatable(s); }
    public static boolean isOnlyDigits(String s)            { return org.apache.commons.lang3.math.NumberUtils.isDigits(s); }
    public static int maxOf3(int a, int b, int c)           { return org.apache.commons.lang3.math.NumberUtils.max(a, b, c); }
    public static int minOf3(int a, int b, int c)           { return org.apache.commons.lang3.math.NumberUtils.min(a, b, c); }
    public static int maxOfArr(int[] xs)                    { return org.apache.commons.lang3.math.NumberUtils.max(xs); }
    public static int compareInts(int x, int y)             { return org.apache.commons.lang3.math.NumberUtils.compare(x, y); }

    // --- BooleanUtils ---
    public static boolean isTrueOrNull(Boolean b)           { return org.apache.commons.lang3.BooleanUtils.isTrue(b); }
    public static boolean allTrue(boolean[] a)              { return org.apache.commons.lang3.BooleanUtils.and(a); }
    public static boolean anyTrue(boolean[] a)              { return org.apache.commons.lang3.BooleanUtils.or(a); }
    public static int toIntFlag(boolean b)                  { return org.apache.commons.lang3.BooleanUtils.toInteger(b); }

    // --- CharUtils ---
    public static int charDigit(char c)                     { return org.apache.commons.lang3.CharUtils.toIntValue(c); }
    public static boolean ascii(char c)                     { return org.apache.commons.lang3.CharUtils.isAscii(c); }

    // --- Validate (guards) ---
    public static void mustBePositive(int n)                { org.apache.commons.lang3.Validate.isTrue(n > 0); }
    public static <T> T mustExist(T v)                      { return org.apache.commons.lang3.Validate.notNull(v); }
    public static void mustBeInRange(int lo, int hi, int v) { org.apache.commons.lang3.Validate.inclusiveBetween(lo, hi, v); }

    // --- Range ---
    public static boolean withinUnit(int x)                 { return org.apache.commons.lang3.Range.between(0, 1).contains(x); }

    // --- Mutable wrappers ---
    public static int bumpAndGet(int seed)                  { org.apache.commons.lang3.mutable.MutableInt m = new org.apache.commons.lang3.mutable.MutableInt(seed); m.increment(); return m.intValue(); }
    public static int addInPlace(int seed, int delta)       { org.apache.commons.lang3.mutable.MutableInt m = new org.apache.commons.lang3.mutable.MutableInt(seed); m.add(delta); return m.intValue(); }
    public static double addDoubleInPlace(double s, double d){ org.apache.commons.lang3.mutable.MutableDouble m = new org.apache.commons.lang3.mutable.MutableDouble(s); m.add(d); return m.doubleValue(); }
    public static boolean flipBool(boolean b)               { org.apache.commons.lang3.mutable.MutableBoolean m = new org.apache.commons.lang3.mutable.MutableBoolean(b); m.setValue(!b); return m.booleanValue(); }

    // --- Pair ---
    public static String pairKey(String k, Integer v)       { return org.apache.commons.lang3.tuple.Pair.of(k, v).getLeft(); }
    public static Integer pairVal(String k, Integer v)      { return org.apache.commons.lang3.tuple.Pair.of(k, v).getRight(); }
    public static void mutablePairSet(String k, int v)      { org.apache.commons.lang3.tuple.MutablePair<String, Integer> p = org.apache.commons.lang3.tuple.MutablePair.of(k, v); p.setLeft("new"); p.setRight(v + 1); }

    // --- Cherry-picked H2 callees ---
    // Each call below targets a library method whose inferred precondition was
    // STRENGTHENED in 3.14.0 vs 3.12.0 (see exp01_specdiff_strengthened_full.txt).
    // When the interprocedural pass propagates the callee spec into the caller,
    // the caller should gain a new requires-clause in 3.14.0 that is absent in
    // 3.12.0 — the propagation signal H2 was designed to surface.
    public static java.util.Calendar toCalOf(java.util.Date d)            { return org.apache.commons.lang3.time.DateUtils.toCalendar(d); }
    public static java.util.Date addDays(java.util.Date d, int amount)    { return org.apache.commons.lang3.time.DateUtils.add(d, java.util.Calendar.DAY_OF_MONTH, amount); }
    public static java.util.Date setField(java.util.Date d, int field, int v) { return org.apache.commons.lang3.time.DateUtils.set(d, field, v); }
    public static java.lang.reflect.Field findField(Class<?> cls, String fieldName) { return org.apache.commons.lang3.reflect.FieldUtils.getField(cls, fieldName, true); }
    public static java.util.List<String> stackFrameList(Throwable t)      { return org.apache.commons.lang3.exception.ExceptionUtils.getStackFrameList(t); }
    public static <L, R> L makePair(L l, R r)                             { return org.apache.commons.lang3.tuple.ImmutablePair.of(l, r).getLeft(); }
    public static <L, M, R> M makeTriple(L l, M m, R r)                   { return org.apache.commons.lang3.tuple.ImmutableTriple.of(l, m, r).getMiddle(); }
    public static Throwable causeByName(Throwable t, String methodName)   { return org.apache.commons.lang3.exception.ExceptionUtils.getCauseUsingMethodName(t, methodName); }
}
