package com.jml.spec;

import java.util.List;

public record MethodSpec(
        List<String> requires,
        List<String> ensures,
        List<String> assignable,
        List<String> loopInvariant,
        List<SignalsClause> signals,
        String version
) {
}
