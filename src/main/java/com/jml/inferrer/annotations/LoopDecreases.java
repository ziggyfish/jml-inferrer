package com.jml.inferrer.annotations;

import java.lang.annotation.*;

/**
 * JML termination measure for a loop. The expression must be a non-negative
 * integer that strictly decreases each iteration. OpenJML proves the loop
 * terminates by checking these two properties at every iteration.
 *
 * When the inferrer emits this and OpenJML cannot discharge it, the resulting
 * `LoopDecreases` failure (with a counter-example) is the intended bug-detection
 * signal for non-terminating or potentially-non-terminating loops.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
@Repeatable(LoopDecreases.List.class)
public @interface LoopDecreases {
    /**
     * The termination-measure expression.
     */
    String value();

    /**
     * Source line of the loop this measure attaches to. Mirrors LoopInvariant.loopLine.
     * {@code 0} means "first loop in the body".
     */
    int loopLine() default 0;

    /**
     * Container annotation for multiple @LoopDecreases.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.METHOD)
    @interface List {
        LoopDecreases[] value();
    }
}
