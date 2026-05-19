package com.jml.spec;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Learns a token dictionary from a corpus of JML clause strings.
 *
 * <p>The algorithm is greedy: for each candidate substring length, count
 * the occurrences across the corpus; score each candidate by
 * {@code (length - 1) * frequency} (the number of bytes that would be
 * saved by encoding the token as a single byte); pick the highest-scoring
 * candidate; deduct its occurrences from the rolling counts (so an
 * overlapping prefix or extension is not also picked); repeat until the
 * byte budget is exhausted.</p>
 *
 * <p>The control-byte range available for single-byte UTF-8 tokens is
 * U+0001 through U+001F, excluding the whitespace controls U+0009 (tab),
 * U+000A (line feed), and U+000D (carriage return). That leaves 28
 * usable byte values. The learner reserves the first <em>k</em> for any
 * caller-supplied seed dictionary (typically {@link SpecCodec#DEFAULT}'s
 * twelve hand-picked tokens) and fills the remainder by learning.</p>
 */
public final class DictionaryLearner {

    /** Control-byte values usable as token encodings (UTF-8 single byte, not whitespace). */
    private static final char[] AVAILABLE_BYTES = buildAvailableBytes();

    private static char[] buildAvailableBytes() {
        StringBuilder sb = new StringBuilder();
        for (int b = 0x01; b <= 0x1F; b++) {
            if (b == 0x09 || b == 0x0A || b == 0x0D) continue;
            sb.append((char) b);
        }
        return sb.toString().toCharArray();
    }

    private DictionaryLearner() {}

    /**
     * Learn a dictionary from a corpus of {@code MethodSpec} instances.
     *
     * @param corpus       the specs to learn from (all clause strings are
     *                     concatenated and scanned)
     * @param seed         a starter dictionary whose tokens are preserved
     *                     (and whose byte assignments are reserved); pass
     *                     {@link SpecCodec#IDENTITY} for a from-scratch
     *                     learning run
     * @param totalTokens  upper bound on the total dictionary size,
     *                     including seed entries; values above
     *                     {@link #maxTokens()} are clamped
     * @param minLen       minimum candidate token length (typically 4 ---
     *                     shorter tokens save little after the codec's
     *                     per-call overhead)
     * @param maxLen       maximum candidate token length
     * @param minOccur     a candidate must appear at least this many times
     *                     in the corpus to be considered
     */
    public static SpecCodec learn(Collection<MethodSpec> corpus,
                                  SpecCodec seed,
                                  int totalTokens,
                                  int minLen, int maxLen, int minOccur) {
        totalTokens = Math.min(totalTokens, maxTokens());

        // 1. Build the corpus string (a single big string suffices for counts).
        StringBuilder corpusSb = new StringBuilder();
        for (MethodSpec s : corpus) {
            for (String c : s.requires())     { corpusSb.append(c).append('\n'); }
            for (String c : s.ensures())      { corpusSb.append(c).append('\n'); }
            for (String c : s.assignable())   { corpusSb.append(c).append('\n'); }
            for (String c : s.loopInvariant()){ corpusSb.append(c).append('\n'); }
            for (SignalsClause sig : s.signals()) {
                corpusSb.append(sig.exceptionType()).append('|').append(sig.condition()).append('\n');
            }
        }
        String corpusStr = corpusSb.toString();

        // 2. Reserve seed bytes. Each seed token consumes one available byte.
        String[][] seedTokens = seed.tokens();
        if (seedTokens.length >= totalTokens) {
            return seed;  // budget exhausted by seed
        }
        java.util.Set<Character> usedBytes = new java.util.HashSet<>();
        for (String[] t : seedTokens) usedBytes.add(t[1].charAt(0));

        // 3. Greedy learning over the corpus (after removing seed tokens).
        String working = corpusStr;
        for (String[] t : seedTokens) working = working.replace(t[0], t[1]);

        List<String[]> learned = new ArrayList<>(java.util.Arrays.asList(seedTokens));
        int byteCursor = 0;
        while (learned.size() < totalTokens) {
            // find next free byte
            while (byteCursor < AVAILABLE_BYTES.length
                    && usedBytes.contains(AVAILABLE_BYTES[byteCursor])) byteCursor++;
            if (byteCursor >= AVAILABLE_BYTES.length) break;
            char nextByte = AVAILABLE_BYTES[byteCursor];

            // count all substrings of [minLen, maxLen] and pick the highest-savings candidate
            Map<String, Integer> counts = countSubstrings(working, minLen, maxLen, minOccur);
            String best = null;
            int bestScore = 0;
            for (Map.Entry<String, Integer> e : counts.entrySet()) {
                int score = (e.getKey().length() - 1) * e.getValue();
                if (score > bestScore) {
                    best = e.getKey();
                    bestScore = score;
                }
            }
            if (best == null || bestScore <= 0) break;
            learned.add(new String[]{best, String.valueOf(nextByte)});
            usedBytes.add(nextByte);
            byteCursor++;
            working = working.replace(best, String.valueOf(nextByte));
        }

        return new SpecCodec(learned.toArray(new String[0][]));
    }

    private static Map<String, Integer> countSubstrings(String corpus, int minLen, int maxLen, int minOccur) {
        Map<String, Integer> counts = new HashMap<>();
        for (int len = minLen; len <= maxLen; len++) {
            for (int i = 0; i + len <= corpus.length(); i++) {
                String sub = corpus.substring(i, i + len);
                // skip substrings that contain a newline (clause boundary) or already-encoded byte
                if (containsControl(sub)) continue;
                counts.merge(sub, 1, Integer::sum);
            }
        }
        // prune below threshold
        Map<String, Integer> pruned = new LinkedHashMap<>();
        for (Map.Entry<String, Integer> e : counts.entrySet()) {
            if (e.getValue() >= minOccur) pruned.put(e.getKey(), e.getValue());
        }
        return pruned;
    }

    private static boolean containsControl(String s) {
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c < 0x20 && c != 0x09 && c != 0x0A && c != 0x0D) return true;
            if (c == '\n') return true;
        }
        return false;
    }

    public static int maxTokens() {
        return AVAILABLE_BYTES.length;
    }
}
