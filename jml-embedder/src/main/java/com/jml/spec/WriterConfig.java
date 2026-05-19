package com.jml.spec;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Configures how the embedder writes specifications.
 *
 * <p>Three concerns are configurable:</p>
 * <ul>
 *   <li>The token-dictionary codec used to compress clause strings
 *       (default: {@link SpecCodec#DEFAULT}; an inferrer with very
 *       different clause shapes can supply a learned codec).</li>
 *   <li>Per-clause-kind defaults that the writer drops on emission
 *       (default: {@code assignable=[\nothing]} for our inferrer; a
 *       configuration with no defaults makes every spec self-describing
 *       at the cost of more bytes; a configuration with different
 *       defaults suits a different inferrer).</li>
 *   <li>Whether to emit the v2 string-array shape or the v3
 *       DEFLATE-compressed shape (default: v2, which is streamable and
 *       reflection-friendly; v3 trades those properties for further
 *       size reduction).</li>
 * </ul>
 *
 * <p>{@link #JML_INFERRER} is the preset shipped for use with the
 * project's own inferrer. {@link #NONE} produces always-explicit output
 * with no defaults dropped. {@link #compressed()} returns a derived
 * configuration with v3 mode enabled.</p>
 */
public final class WriterConfig {

    /** Configuration shipped for the project's inferrer: default dictionary, drop {@code assignable=[\nothing]}. */
    public static final WriterConfig JML_INFERRER = new WriterConfig(
            SpecCodec.DEFAULT,
            Map.of("assignable", List.of("\\nothing")),
            false);

    /** Always-explicit configuration: no token dictionary, no defaults dropped, v2 shape. */
    public static final WriterConfig NONE = new WriterConfig(
            SpecCodec.IDENTITY,
            Map.of(),
            false);

    private final SpecCodec codec;
    private final Map<String, List<String>> dropDefaults;
    private final boolean compressed;

    public WriterConfig(SpecCodec codec,
                        Map<String, List<String>> dropDefaults,
                        boolean compressed) {
        this.codec = codec;
        this.dropDefaults = Map.copyOf(dropDefaults);
        this.compressed = compressed;
    }

    public SpecCodec codec() { return codec; }
    public Map<String, List<String>> dropDefaults() { return dropDefaults; }
    public boolean compressed() { return compressed; }

    /** A derived configuration with the v3 DEFLATE-compressed shape enabled. */
    public WriterConfig compressed(boolean enabled) {
        return new WriterConfig(this.codec, this.dropDefaults, enabled);
    }

    /** A derived configuration with a different codec (e.g.\ a learned dictionary). */
    public WriterConfig withCodec(SpecCodec other) {
        return new WriterConfig(other, this.dropDefaults, this.compressed);
    }

    /** A derived configuration with different drop-defaults. */
    public WriterConfig withDropDefaults(Map<String, List<String>> other) {
        return new WriterConfig(this.codec, other, this.compressed);
    }

    /**
     * Decide whether the writer should drop the given clause kind for
     * this spec. Returns true iff the kind's clause list matches the
     * configured default for that kind exactly.
     */
    public boolean shouldDrop(String kind, List<String> clauses) {
        List<String> def = dropDefaults.get(kind);
        return def != null && def.equals(clauses);
    }
}
