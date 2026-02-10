package com.jml.inferrer.annotations;

import java.lang.annotation.*;

/**
 * JML postcondition specification.
 * Specifies what must be true after a method completes successfully.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
@Repeatable(Ensures.List.class)
public @interface Ensures {
    /**
     * The postcondition expression.
     * @return The JML postcondition
     */
    String value();

    /**
     * Container annotation for multiple @Ensures.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    @interface List {
        Ensures[] value();
    }
}
