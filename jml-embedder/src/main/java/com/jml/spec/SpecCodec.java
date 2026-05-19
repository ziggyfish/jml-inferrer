package com.jml.spec;

/**
 * Token dictionary for JML clause strings.
 *
 * <p>Common JML tokens are encoded as single bytes in the spec-format v2
 * payload to reduce the size of the constant-pool UTF-8 entries that carry
 * clause text. The encoding is invertible; the reader decodes on read.</p>
 *
 * <p>The chosen byte values (Unicode code points 0x01--0x11, avoiding the
 * whitespace controls 0x09/0x0A/0x0D) are control characters that never
 * appear in legitimate JML source, so detection is unambiguous. UTF-8
 * encodes them as single bytes, so the saving is one byte minus the
 * original token length per occurrence.</p>
 */
public final class SpecCodec {

    /**
     * (token, single-character-encoding) pairs. None of the current entries
     * share prefixes, so encode/decode are order-independent; the explicit
     * order is retained as a defensive contract should a longer/shorter
     * token pair be added later.
     */
    static final String[][] TOKENS = {
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
    };

    private SpecCodec() {}

    /**
     * Encode a JML clause string by substituting dictionary tokens with
     * their single-byte encodings. Null input passes through.
     */
    public static String encode(String s) {
        if (s == null) return null;
        for (String[] t : TOKENS) s = s.replace(t[0], t[1]);
        return s;
    }

    /**
     * Decode a JML clause string by reversing the dictionary substitution.
     * Null input passes through.
     */
    public static String decode(String s) {
        if (s == null) return null;
        for (String[] t : TOKENS) s = s.replace(t[1], t[0]);
        return s;
    }
}
