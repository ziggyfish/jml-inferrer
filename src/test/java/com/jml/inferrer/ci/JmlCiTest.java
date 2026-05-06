package com.jml.inferrer.ci;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class JmlCiTest {

    @Test
    @DisplayName("CLI prints usage and returns non-zero on no arguments")
    void usageOnNoArgs() throws Exception {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        int rc = new JmlCi().run(new String[]{}, new PrintStream(baos));
        assertEquals(1, rc);
        assertTrue(baos.toString().contains("Usage: jml-ci"), "should print usage; got: " + baos);
    }

    @Test
    @DisplayName("CLI returns zero on --help")
    void helpReturnsZero() throws Exception {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        int rc = new JmlCi().run(new String[]{"--help"}, new PrintStream(baos));
        assertEquals(0, rc);
        assertTrue(baos.toString().contains("Subcommands"));
    }

    @Test
    @DisplayName("Verify subcommand fail-opens when OPENJML_HOME is unset")
    void verifyFailOpensWithoutOpenjml() throws Exception {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        Path tmp = Files.createTempDirectory("jml-ci-test-");
        try {
            // OPENJML_HOME may or may not be set in the test environment;
            // the verify command must not throw either way.
            int rc = new JmlCi().run(
                    new String[]{"verify", "--root", tmp.toString(),
                            "--report", tmp.resolve("verify.json").toString()},
                    new PrintStream(baos));
            assertEquals(0, rc, "verify must exit 0 by default (fail-open); output: " + baos);
            String out = baos.toString();
            assertTrue(out.contains("[jml-ci verify]"), out);
        } finally {
            deleteRecursive(tmp);
        }
    }

    @Test
    @DisplayName("Summary subcommand renders markdown when report files are absent")
    void summaryHandlesMissingReports() throws Exception {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        Path tmp = Files.createTempDirectory("jml-ci-test-");
        try {
            int rc = new JmlCi().run(
                    new String[]{"summary",
                            "--infer-report", tmp.resolve("missing.json").toString(),
                            "--verify-report", tmp.resolve("missing.json").toString()},
                    new PrintStream(baos));
            assertEquals(0, rc);
            assertTrue(baos.toString().contains("## JML inference summary"),
                    "should render markdown with summary heading; got: " + baos);
        } finally {
            deleteRecursive(tmp);
        }
    }

    @Test
    @DisplayName("Cache key is deterministic and content-sensitive")
    void cacheKeyDeterministic() throws Exception {
        Path a = Files.createTempFile("a", ".java");
        Path b = Files.createTempFile("b", ".java");
        try {
            Files.writeString(a, "class A { int x() { return 42; } }");
            Files.writeString(b, "class A { int x() { return 42; } }");
            assertEquals(CacheKey.forFile(a), CacheKey.forFile(b),
                    "same content must produce same key");
            Files.writeString(b, "class A { int x() { return 99; } }");
            assertNotEquals(CacheKey.forFile(a), CacheKey.forFile(b),
                    "different content must produce different key");
        } finally {
            Files.deleteIfExists(a);
            Files.deleteIfExists(b);
        }
    }

    @Test
    @DisplayName("Per-method cache key incorporates callee specs")
    void perMethodCacheKeyVariesWithCallees() {
        String body = "int caller() { return helper(42); }";
        String key1 = CacheKey.forMethod(body, java.util.List.of("p > 0"));
        String key2 = CacheKey.forMethod(body, java.util.List.of("p >= 0"));
        assertNotEquals(key1, key2,
                "callee spec change should invalidate caller's cache key");
    }

    @Test
    @DisplayName("parseOptions handles --key value and --flag forms")
    void parseOptionsBoth() {
        var opts = JmlCi.parseOptions(new String[]{
                "--root", "/tmp/x", "--strict", "--diff", "main..HEAD"});
        assertEquals("/tmp/x", opts.get("root"));
        assertEquals("main..HEAD", opts.get("diff"));
        assertTrue(opts.containsKey("strict"));
        assertEquals("", opts.get("strict"));
    }

    private static void deleteRecursive(Path root) throws java.io.IOException {
        if (!Files.exists(root)) return;
        try (var s = Files.walk(root)) {
            s.sorted(java.util.Comparator.reverseOrder()).forEach(p -> {
                try { Files.deleteIfExists(p); } catch (Exception ignored) {}
            });
        }
    }
}
