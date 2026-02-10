package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Specifies the computational complexity of a method in Big-O notation.
 * Examples: "O(1)", "O(n)", "O(n log n)", "O(n^2)"
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface Complexity {
    String time() default "";
    String space() default "";
}
