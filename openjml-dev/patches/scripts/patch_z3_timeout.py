#!/usr/bin/env python3
"""
Patches OpenJML's Solver_z3_4_5.java so the OpenJML --timeout=N value (which
the rest of OpenJML treats as seconds) is passed to z3 as milliseconds.

Background
----------
OpenJML's `--timeout=N` is documented and used as **seconds** throughout the
rest of the codebase (e.g. SMT.Configuration.timeout is a Double of seconds,
JmlOption.TIMEOUT advertises seconds). But Solver_z3_4_5 passes it directly
as `-t:N` to z3, and z3 interprets `-t:N` as **milliseconds**:

    z3 -h
        -T:timeout  set the timeout (in seconds).
        -t:timeout  set the soft timeout (in milli seconds). It only kills
                    the current query.

So `--timeout=120` (120 seconds) becomes `-t:120` to z3 (120 ms). Per-query
soft timeout of 120 ms is far too short for any non-trivial verification
condition; the inferrer's `\sum`/`\product`/`\num_of` discharge with the
new axiomatic encoding still routinely exceeds 120 ms on the harder cases.

Fix
---
Multiply the OpenJML-supplied timeout by 1000 before passing to z3. This
matches the unit z3 actually expects.

Idempotent: marker comment guards re-application.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-z3-timeout-ms-patch"


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


EDIT_OLD = (
    "\t\tdouble timeout = smtConfig.timeout;\n"
    "\t\tif (timeout > 0) {\n"
    "\t\t\tList<String> args = new java.util.ArrayList<String>(cmds.length+1);\n"
    "\t\t\targs.addAll(Arrays.asList(cmds));\n"
    "\t\t\tif (isWindows) args.add(\"/t:\" + Integer.toString((int)timeout));\n"
    "\t\t\telse           args.add(\"-t:\" + Integer.toString((int)timeout));\n"
    "\t\t\tcmds = args.toArray(new String[args.size()]);\n"
    "\t\t}"
)
EDIT_NEW = (
    "\t\tdouble timeout = smtConfig.timeout;\n"
    "\t\tif (timeout > 0) {\n"
    "\t\t\t// jml-z3-timeout-ms-patch: OpenJML's --timeout is in SECONDS but\n"
    "\t\t\t// z3's -t: is in MILLISECONDS. Multiply to convert.\n"
    "\t\t\tlong tms = Math.round(timeout * 1000.0);\n"
    "\t\t\tif (tms > Integer.MAX_VALUE) tms = Integer.MAX_VALUE;\n"
    "\t\t\tList<String> args = new java.util.ArrayList<String>(cmds.length+1);\n"
    "\t\t\targs.addAll(Arrays.asList(cmds));\n"
    "\t\t\tif (isWindows) args.add(\"/t:\" + Long.toString(tms));\n"
    "\t\t\telse           args.add(\"-t:\" + Long.toString(tms));\n"
    "\t\t\tcmds = args.toArray(new String[args.size()]);\n"
    "\t\t}"
)


def patch_file(path: Path):
    if not path.exists():
        raise SystemExit(f"File not found: {path}")
    src = path.read_text()
    if already_patched(src):
        print(f"Already patched: {path}")
        return
    if src.count(EDIT_OLD) != 2:
        # Two identical occurrences in Solver_z3_4_5: the (executable) and
        # (String[] command) ctors. We need to patch both.
        raise SystemExit(
            f"Expected 2 occurrences of timeout block in {path}, found {src.count(EDIT_OLD)}"
        )
    src = src.replace(EDIT_OLD, EDIT_NEW)
    path.write_text(src)
    print(f"Patched {path}")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("Usage: patch_z3_timeout.py <Solver_z3_4_5.java>")
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
