package com.jml.spec;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

@Disabled("RQ2 Phase 2A.3 implementation — enable once embedder is implemented")
class RoundtripPropertyTest {

    @Test
    void inferredSpecRoundtripsViaAnnotation() {
        // For each method in the inferrer's regression corpus:
        //   1. Run JML-Inferrer to produce MethodSpec spec.
        //   2. Embed spec into the class file via JmlSpecWriter.
        //   3. Extract the embedded annotations via JmlSpecReader.
        //   4. Assert JmlCanonicaliser.equalsCanonical(spec, spec') == true.
        // Target: <5% failure on Article 1 corpus, <2% on verification corpus.
    }

    @Test
    void v2AnnotationReadByV1ReaderSkipsUnknownKinds() {
        // Embed an annotation whose Kind isn't in v1's enum.
        // Read with a v1 reader.
        // Assert: known clauses returned, unknown logged and skipped.
    }

    @Test
    void classWithoutJmlSpecOnClasspathLoadsCleanly() {
        // Embed annotations into a class.
        // Strip the @JmlSpec type from the consumer's classpath (separate ClassLoader).
        // Class.forName must succeed; reflective annotation access throws TypeNotPresentException.
    }

    @Test
    void specsSurviveProGuardWhenAttributesKept() {
        // Run the embedded JAR through ProGuard with -keepattributes RuntimeVisibleAnnotations.
        // Assert: extractor reads identical specs after obfuscation.
    }

    @Test
    void syntheticTargetsResolveToUserMethods() {
        // Source class has lambda, anonymous inner class, record.
        // After embed/extract, every spec's targetSignature resolves to a user-meaningful method.
    }
}
