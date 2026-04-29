#!/usr/bin/env python3
"""
Patches OpenJML's SMTTranslator.java to emit additional z3 SMT options
(macro_finder, MBQI, qi.eager_threshold) for the start-of-script preamble.

Background
----------
The fork already disables AUTO_CONFIG and MBQI when ESC_TRIGGERS is set
(SMTTranslator.java line 890-891).  We add three more options that the
2026-04-29 z3 flag tuning campaign (Z3 flags + version bump) found to be
either neutral or beneficial across the test fixtures:

- :smt.macro-finder true        - allows z3 to inline pure-recursive
                                  function bodies as macros when the spec
                                  syntactically resembles one. Neutral on
                                  every fixture in our suite (does not
                                  regress timings or correctness).
- :smt.qi.eager_threshold 100   - bumps the per-quantifier instantiation
                                  cost threshold from default 10 to 100,
                                  which gives the engine more room to
                                  explore matches before triggering
                                  saturation.

These are added gated on ESC_TRIGGERS.isSet() (which is the same gate that
already controls AUTO_CONFIG and MBQI), so adding `--no-triggers` reverts
to the upstream defaults.

The flags do NOT crack `Recursive5.power` (genuinely solver-limited per the
2026-04-28 evening session), but they do not regress any fixture either,
and they leave the door open for future improvements where macro_finder
specifically helps.

Idempotent: marker comment guards re-application.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-z3-flags-patch"


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


EDIT_OLD = (
    '        if (JmlOption.ESC_TRIGGERS.isSet(context)) {\n'
    '            startCommands.add(command(smt,"(set-option :AUTO_CONFIG false)"));\n'
    '            startCommands.add(command(smt,"(set-option :smt.MBQI false)"));\n'
    '        }'
)
EDIT_NEW = (
    '        if (JmlOption.ESC_TRIGGERS.isSet(context)) {\n'
    '            // jml-z3-flags-patch: extra z3 quantifier engine flags found\n'
    '            // to be neutral or beneficial in the 2026-04-29 flag tuning\n'
    '            // campaign. macro-finder helps z3 inline pure-recursive\n'
    '            // bodies syntactically; eager_threshold bumps the per-q\n'
    '            // instantiation cost from default 10 to 100.\n'
    '            startCommands.add(command(smt,"(set-option :AUTO_CONFIG false)"));\n'
    '            startCommands.add(command(smt,"(set-option :smt.MBQI false)"));\n'
    '            startCommands.add(command(smt,"(set-option :smt.macro-finder true)"));\n'
    '            startCommands.add(command(smt,"(set-option :smt.qi.eager_threshold 100)"));\n'
    '        }'
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
            f"Could not locate ESC_TRIGGERS option block in {path}. "
            f"Either it's already been changed or the source has drifted."
        )
    src = src.replace(EDIT_OLD, EDIT_NEW)
    path.write_text(src)
    print(f"Patched {path}")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("Usage: patch_z3_flags.py <SMTTranslator.java>")
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
