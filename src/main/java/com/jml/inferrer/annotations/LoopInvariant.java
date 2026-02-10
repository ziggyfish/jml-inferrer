package com.jml.inferrer.annotations;

import java.lang.annotation.*;

/**
 * JML loop invariant specification.
 * Specifies what must remain true throughout loop execution.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
@Repeatable(LoopInvariant.List.class)
public @interface LoopInvariant {
    /**
     * The loop invariant expression.
     * @return The JML loop invariant
     */
    String value();

    /**
     * Container annotation for multiple @LoopInvariant.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    @interface List {
        LoopInvariant[] value();
    }
}
