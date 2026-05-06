package com.jml.inferrer.ci;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HexFormat;
import java.util.List;

/**
 * RQ4 §2.1 — content-hash cache key.
 *
 * <p>Each cache entry's key is the SHA-256 of:</p>
 *
 * <pre>
 *   method-source-text +
 *   "|" +
 *   canonical-form-of-each-callee-spec +
 *   "|" +
 *   inferrer-version
 * </pre>
 *
 * <p>The callee-spec hash is what makes the cache compositional-friendly:
 * when a callee's spec changes, every caller's hash changes too,
 * invalidating the right slice of the cache without invalidating the
 * wrong slice. The inferrer-version bumps invalidate the whole cache on
 * engine upgrade, which is the correct default.</p>
 */
public final class CacheKey {

    /** Bumped manually on each release of the inferrer that changes
     * inference behaviour. The cache key incorporates this so an upgrade
     * invalidates the whole cache rather than mixing old and new specs. */
    public static final String INFERRER_VERSION = "1.0.0";

    private CacheKey() {
    }

    /**
     * Hash a single method against its callees' inferred specs.
     *
     * @param methodSourceText the raw source text of the method declaration
     * @param calleeSpecCanonicalForms the canonical-form text of every spec
     *                                  the inferrer would propagate from
     *                                  callees at this site
     * @return the hex-encoded SHA-256 of the concatenated content
     */
    public static String forMethod(String methodSourceText, List<String> calleeSpecCanonicalForms) {
        MessageDigest sha = sha256();
        sha.update(methodSourceText.getBytes(StandardCharsets.UTF_8));
        sha.update((byte) '|');
        for (String c : calleeSpecCanonicalForms) {
            sha.update(c.getBytes(StandardCharsets.UTF_8));
            sha.update((byte) ',');
        }
        sha.update((byte) '|');
        sha.update(INFERRER_VERSION.getBytes(StandardCharsets.UTF_8));
        return HexFormat.of().formatHex(sha.digest());
    }

    /**
     * Hash a whole source file. Coarser than the per-method hash but
     * sufficient when the consumer caches per-file rather than per-method.
     */
    public static String forFile(Path javaFile) {
        try {
            byte[] bytes = Files.readAllBytes(javaFile);
            MessageDigest sha = sha256();
            sha.update(bytes);
            sha.update((byte) '|');
            sha.update(INFERRER_VERSION.getBytes(StandardCharsets.UTF_8));
            return HexFormat.of().formatHex(sha.digest());
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static MessageDigest sha256() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 unavailable on this JVM", e);
        }
    }
}
