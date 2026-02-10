package com.jml.inferrer.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Annotation indicating that specifications on this method are inherited
 * from a parent class or interface.
 *
 * This annotation is automatically added when the inferrer detects that
 * a method overrides a parent method that has specifications.
 *
 * The Liskov Substitution Principle dictates that:
 * - Preconditions can be weakened (but not strengthened) in subclasses
 * - Postconditions can be strengthened (but not weakened) in subclasses
 *
 * Example usage:
 * <pre>
 * {@code
 * @InheritedSpec(from = "AbstractCollection")
 * @Ensures("\\result >= 0")
 * public int size() { ... }
 * }
 * </pre>
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface InheritedSpec {

    /**
     * The source class or interface from which the specifications are inherited.
     *
     * @return The fully qualified name or simple name of the parent class/interface
     */
    String from();

    /**
     * Optional description of how the inherited specifications were modified.
     * Use this when the subclass strengthens postconditions or weakens preconditions.
     *
     * @return Description of modifications, or empty if inherited as-is
     */
    String modifications() default "";
}
