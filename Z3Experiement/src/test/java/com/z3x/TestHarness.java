package com.z3x;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * Minimal test harness — no external dependencies. Each test class extends this,
 * and any zero-arg, non-static method whose name starts with {@code test} is run.
 *
 * Run all known suites with: {@code java com.z3x.TestHarness}.
 */
public abstract class TestHarness {

    public static void assertEquals(Object expected, Object actual) {
        if (!Objects.equals(expected, actual)) {
            throw new AssertionError("expected " + expected + " but got " + actual);
        }
    }

    public static void assertTrue(boolean cond) {
        if (!cond) throw new AssertionError("expected true");
    }

    public static void assertTrue(boolean cond, String msg) {
        if (!cond) throw new AssertionError(msg);
    }

    public static void assertFalse(boolean cond) {
        if (cond) throw new AssertionError("expected false");
    }

    private static final List<Class<?>> SUITES = Arrays.asList(
            SatTest.class,
            EufTest.class,
            LiaTest.class,
            IntegerLiaTest.class,
            ArrayTest.class,
            ArrayExtTest.class,
            BvTest.class,
            BvArithTest.class,
            QuantifierTest.class,
            QuantifierAlternationTest.class,
            SpecPatternTest.class
    );

    public static void main(String[] args) throws Exception {
        int passed = 0, failed = 0;
        List<String> failures = new ArrayList<>();
        for (Class<?> suite : SUITES) {
            for (Method m : suite.getDeclaredMethods()) {
                if (!m.getName().startsWith("test")) continue;
                if (m.getParameterCount() != 0) continue;
                Object inst = suite.getDeclaredConstructor().newInstance();
                try {
                    m.setAccessible(true);
                    long t0 = System.nanoTime();
                    m.invoke(inst);
                    double ms = (System.nanoTime() - t0) / 1e6;
                    System.out.printf("  PASS %-30s %.1fms%n", suite.getSimpleName() + "." + m.getName(), ms);
                    passed++;
                } catch (Throwable t) {
                    Throwable cause = t.getCause() != null ? t.getCause() : t;
                    System.out.printf("  FAIL %-30s %s%n", suite.getSimpleName() + "." + m.getName(), cause);
                    failures.add(suite.getSimpleName() + "." + m.getName() + ": " + cause);
                    failed++;
                }
            }
        }
        System.out.println();
        System.out.printf("Total: %d passed, %d failed%n", passed, failed);
        if (failed > 0) {
            for (String f : failures) System.out.println("  - " + f);
            System.exit(1);
        }
    }
}
