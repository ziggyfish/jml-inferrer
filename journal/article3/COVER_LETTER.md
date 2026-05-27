# Cover Letter — ICSE Submission

**Title:** Does Compositional Refinement Strictly Extend Heuristic
Specification Inference? A Measurement Study

**Track:** Research Track

**Anonymisation:** The submission is anonymised for double-blind review (author
names, affiliations, contact emails, acknowledgements, and replication-package
URL have all been redacted or replaced with anonymous-archive placeholders).

## Summary for the editors

This paper asks a single, falsifiable, measurable question about specification
inference for Java: when an established heuristic JML inferrer propagates a
called method's contract into its caller's, does single-pass propagation
capture what a genuinely compositional (top-down weakest-precondition) analysis
would? We implement the compositional pass as a 414-line analyser, run it over
five open-source Java libraries totalling 21{,}052 inferred methods, and
report:

- the pass refines 24--44\% of methods per library (median 36.33\%) and adds
  42{,}370 cross-method precondition clauses the single-pass strategy cannot
  express;
- the addition is dominated by branch-conditional implications on four of
  five libraries (34--64\%) and includes polymorphic-dispatch disjunctions on
  every library (1.8--9.7\%) --- both shapes the single pass cannot produce
  by construction;
- the second pass is cheap: 44 seconds total for all 21{,}052 methods.

The paper also includes a concrete, runnable consequence of the propagation:
a diff of inferred specifications across two consecutive Commons Lang versions
(3.12.0 vs 3.14.0) surfaces 436 candidate-breaking method-level changes and
91 strengthened preconditions --- exactly the artefact a behavioural-
compatibility checker would consume.

## Why ICSE

The paper contributes a primary empirical measurement on a question that
every JML / contract-inference designer faces, and a concrete artefact (a
candidate-breaking set on a real version step) that connects the structural
measurement to a use that the SE community values. The technique is
implemented, the corpora are public, and the replication package is at the
anonymous-archive URL given in the Data Availability section.

## Suggested reviewers (optional, for the editors)

Three groups have published nearby and would be informed evaluators:

- Researchers on **JML inference and JML deductive verification** --- e.g.,
  the OpenJML / KeY / Why3 communities; reviewers who have published at
  ICSE/FSE/ISSTA on specification mining or JML extraction would be
  well-placed.
- Researchers on **static analysis with abstract interpretation / dataflow
  analysis** --- the closest neighbour at ICSE'24 is *A Framework For
  Inferring Properties of User-Defined Functions* (Liu, Arulraj, Orso),
  which would be a defensible suggested reviewer pool.
- Researchers on **API breaking-change detection / library evolution** ---
  the candidate-breaking-set artefact in Section V.B sits in this community's
  evaluation territory, and reviewers familiar with japicmp / Revapi /
  Maracas would speak to the breaking-change framing.

(We list these groups by topic rather than by name to preserve the
double-blind review process. Specific suggested-reviewer / non-reviewer lists
will be provided on the submission form per ICSE policy.)

## Statements

- This work is original; it has not been published elsewhere and is not
  under simultaneous review at another venue.
- The submission is anonymised for double-blind review. Acknowledgements,
  funding, ORCIDs, author contributions (CRediT), and the permanent
  replication-package DOI will be added on acceptance.
- The authors declare no conflict of interest.
- All measurements reported in the paper are deterministic given the inputs
  and reproducible from the artefact at the anonymous archive.
