package com.jml.spec;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Container annotation for a method's complete JML specification.
 *
 * <p><b>Format v2.</b> Each clause kind is stored as a separate {@code String[]}
 * member. Empty arrays are the default and are not emitted; absence of the
 * {@code assignable} member is taken to mean {@code assignable \nothing} (the
 * inferrer's overwhelmingly common case), so writers omit it when the only
 * assignable clause is the default. The {@code signals} member packs each
 * clause as {@code "ExceptionType|condition"} so it can ride a single
 * {@code String[]} member rather than a separate annotation type.</p>
 *
 * <p>Clause text strings are encoded by {@link com.jml.spec.SpecCodec} before
 * being written, which compresses common JML tokens ({@code \result},
 * {@code \old(}, quantifiers, {@code != null}, etc.) to single bytes. The
 * reader decodes them on read; the encoding is invertible.</p>
 *
 * <p><b>Backward compatibility.</b> Bytecode emitted by the v1 writer used a
 * different shape: a {@code JmlSpec[] value()} array of per-clause
 * annotations. The {@link com.jml.spec.read.AsmJmlSpecReader} reads both
 * shapes; the v1 {@code @JmlSpec} type is retained for legacy bytecode but
 * deprecated.</p>
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR, ElementType.FIELD, ElementType.TYPE})
public @interface JmlSpecs {
    String[] requires() default {};
    String[] ensures() default {};
    String[] assignable() default {};
    String[] loopInvariant() default {};
    /** Each entry is {@code "ExceptionType|condition"}. */
    String[] signals() default {};
    String version() default "2";
}
