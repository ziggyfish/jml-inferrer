package com.jml.inferrer.embedder;

import com.jml.inferrer.model.MethodSpecification;
import com.jml.spec.MethodSpec;
import com.jml.spec.SignalsClause;

import java.util.List;

/**
 * Converts between the inferrer's {@link MethodSpecification} model and the
 * {@code jml-embedder} module's {@link MethodSpec} model.
 *
 * <p>The two models carry equivalent information but were defined independently:
 * the inferrer uses package-internal lists with confidence-level tracking, and
 * the embedder uses public records suited to bytecode emission. This converter
 * is the bridge between them.</p>
 *
 * <p>The conversion preserves clause text verbatim — no canonicalisation is
 * applied here. Callers that need canonical form should run
 * {@link com.jml.spec.JmlCanonicaliser#canonicalise} explicitly.</p>
 */
public final class InferrerSpecConverter {

    private InferrerSpecConverter() {
    }

    public static MethodSpec toEmbeddable(MethodSpecification spec) {
        List<String> requires = List.copyOf(spec.getPreconditions());
        List<String> ensures = List.copyOf(spec.getPostconditions());
        List<String> assignable = List.copyOf(spec.getAssignableClauses());
        List<String> loopInvariant = List.copyOf(spec.getLoopInvariants());
        // The inferrer doesn't currently produce signals clauses through the
        // public MethodSpecification API; reserve the slot for future
        // ExceptionAnalyzer integration.
        List<SignalsClause> signals = List.of();
        return new MethodSpec(requires, ensures, assignable, loopInvariant, signals, "1.0");
    }

    public static MethodSpecification fromEmbeddable(MethodSpec spec) {
        MethodSpecification out = new MethodSpecification();
        if (spec.requires() != null) spec.requires().forEach(out::addPrecondition);
        if (spec.ensures() != null) spec.ensures().forEach(out::addPostcondition);
        if (spec.assignable() != null) spec.assignable().forEach(out::addAssignableClause);
        if (spec.loopInvariant() != null) spec.loopInvariant().forEach(out::addLoopInvariant);
        return out;
    }
}
