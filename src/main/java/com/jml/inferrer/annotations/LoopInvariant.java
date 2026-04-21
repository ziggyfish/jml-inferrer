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
     * Source line of the loop this invariant attaches to. The
     * AnnotationToJMLConverter uses this to place each invariant directly above the
     * correct loop when a method contains multiple (nested or sequential) loops.
     * {@code 0} means "first loop in the body" (legacy behaviour).
     */
    int loopLine() default 0;

    /**
     * Container annotation for multiple @LoopInvariant.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    @interface List {
        LoopInvariant[] value();
    }
}
