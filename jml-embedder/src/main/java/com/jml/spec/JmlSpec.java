package com.jml.spec;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Legacy per-clause annotation type from spec-format v1.
 *
 * <p>Retained for backward compatibility: bytecode emitted before v2 carries
 * one {@code @JmlSpec} per JML clause, optionally wrapped in
 * {@code @JmlSpecs(value=...)}. The current writer
 * ({@link com.jml.spec.write.AsmJmlSpecWriter}) emits v2 instead --- a
 * single {@link JmlSpecs} annotation per method with clause arrays. The
 * reader ({@link com.jml.spec.read.AsmJmlSpecReader}) accepts both
 * shapes.</p>
 *
 * <p>This type is no longer marked {@code @Repeatable} because v2's
 * {@link JmlSpecs} no longer has a {@code value()} member to act as the
 * container. New code should not write {@code @JmlSpec}; it exists only
 * to make older embedded bytecode readable.</p>
 *
 * @deprecated v1 format; use {@link JmlSpecs} for new writes.
 */
@Deprecated
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR, ElementType.FIELD, ElementType.TYPE})
public @interface JmlSpec {
    Kind kind();
    String text();
    int order() default 0;
    String version() default "1.0";
    String targetSignature() default "";
}
