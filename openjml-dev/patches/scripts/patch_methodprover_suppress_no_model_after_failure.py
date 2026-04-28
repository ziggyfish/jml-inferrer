#!/usr/bin/env python3
"""
Patches OpenJML's MethodProverSMT.java so that when the counterexample loop
has already reported at least one Invalid assertion (REAL_TRACE), it does
NOT also emit the secondary "esc.nomodel" / "esc.resourceout" warning when
a subsequent iteration of the loop fails.

Background
----------
When ESC has multiple potential counterexamples (e.g., dx*dx overflow AND
dy*dy overflow in the same method), MethodProverSMT iterates: each iteration
asks the solver for a model, blocks that model with a fresh assertion, and
asks again.  If the FIRST iteration succeeds (counterexample reported) but
the SECOND iteration's solver call times out or returns "no model", the
old code emits BOTH:

  PureCompoundWithLocals.java:20: ArithmeticOperationRange ...   (REAL_TRACE)
  PureCompoundWithLocals.java:17: Validity is unknown - no model available

The second message poisons output classification: tools that scan for
"Validity is unknown" bin the test as SOLVER_UNKNOWN, hiding the first,
real, actionable counterexample.

Fix
---
Gate the secondary `esc.nomodel` and `esc.resourceout` warnings on
`!haveFailedAssertion`. If we've already reported a counterexample, swallow
the "no model" / "timeout" message; the user has been told what's wrong.

The proof result was already gated correctly (it only becomes UNKNOWN/TIMEOUT
if no prior failure was reported), so this just brings the user-visible
warning in line with the proof result.

This is the textbook ``no double-reporting'' fix: by SMT-LIB semantics, an
unknown verdict on a strictly-stronger formula (the previous model is
blocked, so the formula has fewer satisfying assignments) provides no new
information once we already have a model from the looser version.

Idempotent: marker comment guards re-application.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-suppress-secondary-nomodel-patch"


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


# Three sites in MethodProverSMT.java (counterexample loop):
#   (a) line ~693: timeout in get_info(:reason-unknown)
#   (b) line ~709: nomodel inside the unknown branch (after :reason-unknown probe)
#   (c) line ~721: nomodel after fall-through (when initial response wasn't unknown but get_value still errors)
#
# Each looks like:
#     utils.verify(methodDecl,"esc.NAME", ARGS);
#     if (!haveFailedAssertion) proofResult = ...;
#     break b;     [for site (a)]
# We rewrite the verify call so the warning is suppressed when haveFailedAssertion is true.

EDITS = [
    # site (a) - resourceout (timeout)
    {
        "old": (
            "                                if (timeout) {\n"
            "                                \tutils.verify(methodDecl,\"esc.resourceout\",\": \" + msg);\n"
            "                                \tif (!haveFailedAssertion) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.TIMEOUT,start);\n"
            "                                    break b;\n"
            "                                }"
        ),
        "new": (
            "                                if (timeout) {\n"
            "                                \tif (!haveFailedAssertion) { // jml-suppress-secondary-nomodel-patch\n"
            "                                \t\tutils.verify(methodDecl,\"esc.resourceout\",\": \" + msg);\n"
            "                                \t\tproofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.TIMEOUT,start);\n"
            "                                \t}\n"
            "                                    break b;\n"
            "                                }"
        ),
    },
    # site (b) - nomodel inside unknown branch (line ~709 with verbose label)
    {
        "old": (
            "                        IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol(\"NULL\"));\n"
            "                        if (r.isError()) {\n"
            "                            String msg = \": \";\n"
            "                            if (JmlOption.TIMEOUT.value(context) != null) msg = \" (possible timeout): \";\n"
            "                            utils.verify(methodDecl,\"esc.nomodel\",\"method \" + utils.qualifiedName(methodDecl.sym) + \" - \" + msg + r);\n"
            "                            if (!haveFailedAssertion) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);\n"
            "                            break b;\n"
            "                        }"
        ),
        "new": (
            "                        IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol(\"NULL\"));\n"
            "                        if (r.isError()) {\n"
            "                            String msg = \": \";\n"
            "                            if (JmlOption.TIMEOUT.value(context) != null) msg = \" (possible timeout): \";\n"
            "                            if (!haveFailedAssertion) { // jml-suppress-secondary-nomodel-patch\n"
            "                                utils.verify(methodDecl,\"esc.nomodel\",\"method \" + utils.qualifiedName(methodDecl.sym) + \" - \" + msg + r);\n"
            "                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);\n"
            "                            }\n"
            "                            break b;\n"
            "                        }"
        ),
    },
    # site (c) - nomodel from fall-through path (line ~721, no method-name prefix)
    {
        "old": (
            "                    // If we don't clearly know the prover failed, we try to get a simple value and see if there is a model\n"
            "                    IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol(\"NULL\"));\n"
            "                    if (r.isError()) {\n"
            "                        String msg = \": \";\n"
            "                        if (JmlOption.TIMEOUT.value(context) != null) msg = \" (possible timeout): \";\n"
            "                        utils.verify(methodDecl,\"esc.nomodel\",msg + r);\n"
            "                        if (!haveFailedAssertion) proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);\n"
            "                        break b;\n"
            "                    }"
        ),
        "new": (
            "                    // If we don't clearly know the prover failed, we try to get a simple value and see if there is a model\n"
            "                    IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol(\"NULL\"));\n"
            "                    if (r.isError()) {\n"
            "                        String msg = \": \";\n"
            "                        if (JmlOption.TIMEOUT.value(context) != null) msg = \" (possible timeout): \";\n"
            "                        if (!haveFailedAssertion) { // jml-suppress-secondary-nomodel-patch\n"
            "                            utils.verify(methodDecl,\"esc.nomodel\",msg + r);\n"
            "                            proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);\n"
            "                        }\n"
            "                        break b;\n"
            "                    }"
        ),
    },
]


def patch_file(path: Path):
    if not path.exists():
        raise SystemExit(f"File not found: {path}")
    src = path.read_text()
    if already_patched(src):
        print(f"Already patched: {path}")
        return
    for i, edit in enumerate(EDITS):
        if edit["old"] not in src:
            raise SystemExit(
                f"Edit {i} target not found in {path}. "
                f"First 80 chars of expected old: {edit['old'][:80]!r}"
            )
        if src.count(edit["old"]) != 1:
            raise SystemExit(
                f"Edit {i} target appears {src.count(edit['old'])} times "
                f"(expected 1) in {path}"
            )
        src = src.replace(edit["old"], edit["new"], 1)
    path.write_text(src)
    print(f"Patched {path}")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("Usage: patch_methodprover_suppress_no_model_after_failure.py <MethodProverSMT.java>")
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
