package com.jml.inferrer.annotations;

import java.lang.annotation.*;

/**
 * JML precondition specification.
 * Specifies what must be true before a method is called.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
@Repeatable(Requires.List.class)
public @interface Requires {
    /**
     * The precondition expression.
     * @return The JML precondition
     */
    String value();

    /**
     * Container annotation for multiple @Requires.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    @interface List {
        Requires[] value();
    }
}
