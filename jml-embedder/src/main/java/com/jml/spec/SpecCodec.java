package com.jml.spec;

import java.util.Arrays;
import java.util.Comparator;

/**
 * Token-dictionary codec for JML clause strings.
 *
 * <p>An instance holds a dictionary of {@code (token, encoded-character)}
 * pairs. The encoder substitutes each occurrence of {@code token} with its
 * single-character encoding; the decoder reverses the substitution. Both
 * directions are pure {@link String#replace(CharSequence, CharSequence)}
 * loops over the dictionary entries, sorted longest-first so that a
 * longer token whose prefix is also a token in the dictionary is tried
 * before the prefix.</p>
 *
 * <p>The encoded characters must be single Unicode code points that
 * cannot appear in legitimate JML source. The default dictionary uses
 * U+0001 through U+0011 (control characters), which UTF-8 encodes as
 * single bytes; for a learned dictionary the caller is responsible for
 * choosing encoding characters from a compatible range.</p>
 *
 * <p>{@link #DEFAULT} is the hand-picked twelve-token dictionary
 * described in the embedder spec-format v2.</p>
 */
public final class SpecCodec {

    private final String[][] tokens;

    /**
     * Construct a codec from a copy of the given dictionary. Entries are
     * stored in length-descending order so the encoder applies longer
     * tokens before shorter ones.
     */
    public SpecCodec(String[][] tokens) {
        this.tokens = new String[tokens.length][2];
        for (int i = 0; i < tokens.length; i++) {
            this.tokens[i][0] = tokens[i][0];
            this.tokens[i][1] = tokens[i][1];
        }
        Arrays.sort(this.tokens, Comparator.<String[]>comparingInt(t -> t[0].length()).reversed());
    }

    /** The hand-picked default dictionary used by the v2 writer/reader. */
    public static final SpecCodec DEFAULT = new SpecCodec(new String[][]{
        {"\\result",       ""},
        {"\\old(",         ""},
        {"\\forall ",      ""},
        {"\\exists ",      ""},
        {"\\sum ",         ""},
        {"\\product ",     ""},
        {"\\num_of ",      ""},
        {" ==> ",          ""},
        {"!= null",        ""},
        {"== null",        ""},
        {"\\nothing",      ""},
        {"\\everything",   ""},
    });

    /** An identity codec (no token substitution). Useful for tests and for {@code WriterConfig.NONE}. */
    public static final SpecCodec IDENTITY = new SpecCodec(new String[0][0]);

    /** Encode a JML clause string. Null passes through. */
    public String encode(String s) {
        if (s == null) return null;
        for (String[] t : tokens) s = s.replace(t[0], t[1]);
        return s;
    }

    /** Decode a JML clause string. Null passes through. */
    public String decode(String s) {
        if (s == null) return null;
        // Order is irrelevant for decode (each encoded byte is unique),
        // but follow the same iteration for consistency.
        for (String[] t : tokens) s = s.replace(t[1], t[0]);
        return s;
    }

    /** Exposed for the {@code DictionaryLearner} so it can inspect what's already covered. */
    public String[][] tokens() {
        String[][] copy = new String[tokens.length][2];
        for (int i = 0; i < tokens.length; i++) {
            copy[i][0] = tokens[i][0];
            copy[i][1] = tokens[i][1];
        }
        return copy;
    }
}
