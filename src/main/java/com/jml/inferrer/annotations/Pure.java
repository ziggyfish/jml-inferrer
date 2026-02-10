package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Indicates that a method is pure: it has no side effects and is deterministic.
 * A pure method:
 * - Does not modify any fields (instance or static)
 * - Does not perform I/O operations
 * - Returns the same result for the same inputs
 * - Does not call any non-pure methods
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface Pure {
}
