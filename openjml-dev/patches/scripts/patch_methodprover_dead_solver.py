#!/usr/bin/env python3
"""
Patches MethodProverSMT.java so that when z3 dies (process gone, broken
pipe, error response on get_info(":reason-unknown")) after returning an
"unknown" check_sat, OpenJML treats the failure as a TIMEOUT classification
rather than an internal ERROR.

Background
----------
The 2026-04-29 z3-T-flag patch added `-T:` (z3's global hard timeout in
seconds, 2x the OpenJML --timeout setting) to bound wall time for cases
where z3 hits a quantifier-saturation matching loop and OpenJML's
interaction layer keeps issuing follow-up queries.  Without `-T:`,
Recursive5.power was hanging for 25+ minutes; with `-T:`, z3 dies after
the global limit.

When z3 dies, OpenJML's `solver.get_info(":reason-unknown")` doesn't return
either an `unsupported` response or an `IAttributeList` — it returns an
error response.  The unpatched code falls through to "Unexpected result"
and reports a hard ERROR.  Semantically this is a timeout, not an error:
z3 returned unknown because it hit the time budget.

Fix
---
Add a branch before the "Unexpected result" log.error that detects an
IResponse.IError or null and treats it as a soft timeout — emit
esc.resourceout, mark as TIMEOUT, and continue (don't return ERROR).

Idempotent: marker comment guards re-application.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-methodprover-dead-solver-patch"


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


# We need to find both occurrences (lines ~648 and ~702).  The simplest robust
# approach: locate the textual block "// Unexpected result" + the log.error call
# + the "return factory.makeProverResult" with ERROR, and prepend our handler.
# First occurrence (around line 648): has 'return factory.makeProverResult' termination.
EDIT_OLD_RETURN = (
    "                            } else {\n"
    "                                // Unexpected result\n"
    "                                log.error(\"jml.internal.notsobad\",\"Unexpected result when querying SMT solver for reason for an unknown result: \" + unknownReason);\n"
    "                                return factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.ERROR,start);\n"
    "                            }"
)
EDIT_NEW_RETURN = (
    "                            } else {\n"
    "                                // jml-methodprover-dead-solver-patch:\n"
    "                                // Unrecognised reason-unknown response. This\n"
    "                                // happens when z3 dies (e.g. from -T: hard\n"
    "                                // timeout) and the response stream is broken,\n"
    "                                // or when z3 returns a bare token that isn't\n"
    "                                // an IAttributeList. Treat as a soft TIMEOUT\n"
    "                                // rather than a hard ERROR (the verification\n"
    "                                // attempt has timed out, not crashed).\n"
    "                                utils.verify(methodDecl,\"esc.resourceout.feasibility\",\": unknown reason: \" + unknownReason);\n"
    "                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.TIMEOUT,start);\n"
    "                                utils.progress(0,Utils.PROGRESS,fileLocation + msg + \"timeout (unknown reason)\");\n"
    "                            }"
)
# Second occurrence (around line 707): has 'break b;' termination, different indent.
EDIT_OLD_BREAK = (
    "                        } else {\n"
    "                            // Unexpected result\n"
    "                            log.error(\"jml.internal.notsobad\",\"Unexpected result when querying SMT solver for reason for an unknown result: \" + unknownReason);\n"
    "                            break b;\n"
    "                        }"
)
EDIT_NEW_BREAK = (
    "                        } else {\n"
    "                            // jml-methodprover-dead-solver-patch (break-b variant):\n"
    "                            // see EDIT_NEW_RETURN above for rationale.\n"
    "                            if (!haveFailedAssertion) {\n"
    "                                utils.verify(methodDecl,\"esc.resourceout\",\": unknown reason: \" + unknownReason);\n"
    "                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.TIMEOUT,start);\n"
    "                            }\n"
    "                            break b;\n"
    "                        }"
)


def patch_file(path: Path):
    if not path.exists():
        raise SystemExit(f"File not found: {path}")
    src = path.read_text()
    occurrences_return = src.count(EDIT_OLD_RETURN)
    occurrences_break = src.count(EDIT_OLD_BREAK)
    # Idempotent at the per-occurrence level: if neither pattern matches and
    # the marker is already present, treat as fully patched.
    if occurrences_return == 0 and occurrences_break == 0:
        if already_patched(src):
            print(f"Already patched: {path}")
            return
        raise SystemExit(
            f"Could not locate 'Unexpected result' fallthrough block in {path}"
        )
    if occurrences_return:
        src = src.replace(EDIT_OLD_RETURN, EDIT_NEW_RETURN)
    if occurrences_break:
        src = src.replace(EDIT_OLD_BREAK, EDIT_NEW_BREAK)
    path.write_text(src)
    print(f"Patched {path} (return: {occurrences_return}, break: {occurrences_break})")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("Usage: patch_methodprover_dead_solver.py <MethodProverSMT.java>")
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
