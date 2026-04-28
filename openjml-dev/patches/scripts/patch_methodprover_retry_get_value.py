#!/usr/bin/env python3
"""
Patches MethodProverSMT.java so that when get_value(NULL) fails with
"model is not available" on the first attempt, OpenJML retries by:

  1. Calling solver.check_sat() once more (same proof obligation).
  2. Re-trying get_value(NULL).

Background
----------
Z3 with `(set-option :smt.MBQI false)` and pattern triggers can return
"unknown" without materialising a model. If OpenJML asks for a model
immediately, z3 returns `(error "model is not available")`. But the
SAME script, sent through a different OpenJML code path (--jmlverbose
mode), gets a successful model — confirmed by direct trace
instrumentation. The difference appears to be timing-sensitive
(perhaps related to how the OpenJML SolverProcess buffers output).

The pragmatic fix: when the first get_value fails, give z3 another
chance. The cost is one extra check_sat per failed-first-iteration
case (a few seconds at most) and the benefit is converting many
"Validity is unknown" outcomes into proper REAL_TRACE counterexamples,
which the inferrer's test classifier handles correctly.

Idempotent: marker comment guards re-application.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-retry-get-value-patch"


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


# We patch the FIRST get_value site (inside the unknown branch, line ~707).
# On error, instead of immediately emitting the warning, we attempt a retry:
# call solver.check_sat() and try get_value once more.  If still error, emit.

EDIT_OLD = (
    "                        // Instead, try to get a simple value and see if there is a model\n"
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
)

EDIT_NEW = (
    "                        // Instead, try to get a simple value and see if there is a model\n"
    "                        IResponse r = solver.get_value(smt.smtConfig.exprFactory.symbol(\"NULL\"));\n"
    "                        // jml-retry-get-value-patch: when get_value errors with\n"
    "                        // \"model is not available\", give z3 one more chance.\n"
    "                        // Some interaction patterns leave z3 without a materialised\n"
    "                        // model on the first request; a retry typically succeeds.\n"
    "                        if (r.isError() && !haveFailedAssertion) {\n"
    "                            IResponse retrySat = solver.check_sat();\n"
    "                            if (retrySat.equals(smt.smtConfig.responseFactory.unknown())\n"
    "                                    || retrySat.toString().equals(\"sat\")) {\n"
    "                                IResponse r2 = solver.get_value(smt.smtConfig.exprFactory.symbol(\"NULL\"));\n"
    "                                if (!r2.isError()) {\n"
    "                                    r = r2;\n"
    "                                    solverResponse = retrySat;\n"
    "                                }\n"
    "                            }\n"
    "                        }\n"
    "                        if (r.isError()) {\n"
    "                            String msg = \": \";\n"
    "                            if (JmlOption.TIMEOUT.value(context) != null) msg = \" (possible timeout): \";\n"
    "                            if (!haveFailedAssertion) { // jml-suppress-secondary-nomodel-patch\n"
    "                                utils.verify(methodDecl,\"esc.nomodel\",\"method \" + utils.qualifiedName(methodDecl.sym) + \" - \" + msg + r);\n"
    "                                proofResult = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.UNKNOWN,start);\n"
    "                            }\n"
    "                            break b;\n"
    "                        }"
)


def patch_file(path: Path):
    if not path.exists():
        raise SystemExit(f"File not found: {path}")
    src = path.read_text()
    if already_patched(src):
        print(f"Already patched: {path}")
        return
    if EDIT_OLD not in src:
        raise SystemExit(
            "Could not find target for retry patch. The previous "
            "patch_methodprover_suppress_no_model_after_failure.py may not "
            "have been applied first, or the source has drifted."
        )
    if src.count(EDIT_OLD) != 1:
        raise SystemExit(
            f"Expected exactly 1 occurrence of target, got {src.count(EDIT_OLD)}"
        )
    src = src.replace(EDIT_OLD, EDIT_NEW, 1)
    path.write_text(src)
    print(f"Patched {path}")


def main():
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
