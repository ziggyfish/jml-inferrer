package com.jml.spec.openapi;

import com.jml.spec.SignalsClause;

import java.util.List;

/**
 * Per-OpenAPI-operation specification carrying JML clauses for HTTP/REST
 * endpoints. Mirrors {@link com.jml.spec.MethodSpec} but is keyed by route+verb
 * rather than by class+method+descriptor.
 *
 * <p>Order in {@code requires} is significant (well-definedness chain);
 * order in the others is not. {@code signals} entries pair an exception type
 * (in JVM internal slash form, so cross-language consumers can resolve them)
 * with the condition under which the operation throws it.</p>
 */
public record OperationSpec(
        List<String> requires,
        List<String> ensures,
        List<String> assignable,
        List<String> loopInvariant,
        List<SignalsClause> signals,
        String version
) {
    public OperationSpec {
        if (requires == null) requires = List.of();
        if (ensures == null) ensures = List.of();
        if (assignable == null) assignable = List.of();
        if (loopInvariant == null) loopInvariant = List.of();
        if (signals == null) signals = List.of();
        if (version == null) version = "1.0";
    }
}
