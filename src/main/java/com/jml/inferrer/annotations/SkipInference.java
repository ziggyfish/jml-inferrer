package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Annotation to mark methods or classes that should be skipped during JML inference.
 *
 * When applied to a method, the inferrer will not generate any specifications for it.
 * When applied to a class, all methods in that class will be skipped.
 *
 * This is useful for:
 * - Methods with complex logic that the inferrer might misinterpret
 * - Methods that already have manually written specifications elsewhere
 * - Generated code that should not be annotated
 * - Test methods that don't need specifications
 *
 * Example usage:
 * <pre>
 * {@code
 * @SkipInference(reason = "Complex reflection-based logic")
 * public void configureProxy() { ... }
 * }
 * </pre>
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.TYPE})
public @interface SkipInference {

    /**
     * Optional reason explaining why inference should be skipped for this element.
     *
     * @return The reason for skipping, or empty string if not specified
     */
    String reason() default "";
}
