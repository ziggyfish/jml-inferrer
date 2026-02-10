package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Indicates that certain methods must be called before the object
 * is disposed (typically cleanup methods like close(), dispose()).
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface MustCall {
    String[] value();
}
