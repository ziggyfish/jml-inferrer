package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Repeatable;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Specifies which memory locations may be modified by this method.
 * Examples: "this.field", "arr[*]", "\\nothing"
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
@Repeatable(Assignable.List.class)
public @interface Assignable {
    String value();

    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    @interface List {
        Assignable[] value();
    }
}
