#!/usr/bin/env python3
"""
Patches OpenJML's Solver_z3_4_3.java and Solver_z3_4_5.java so the OpenJML
--timeout=N value (which the rest of OpenJML treats as seconds) is correctly
expressed both as a per-query soft timeout AND as a global hard timeout.

Background
----------
OpenJML's `--timeout=N` is documented and used as **seconds** throughout the
rest of the codebase (e.g. SMT.Configuration.timeout is a Double of seconds,
JmlOption.TIMEOUT advertises seconds). But the unpatched Solver_z3 classes
pass the value directly as `-t:N` to z3, and z3 interprets `-t:N` as
**milliseconds**:

    z3 -h
        -T:timeout  set the timeout (in seconds).
        -t:timeout  set the soft timeout (in milli seconds). It only kills
                    the current query.

Two issues:

1. `--timeout=120` becomes `-t:120` to z3 (120 milliseconds soft per-query).
   Per-query soft timeout of 120 ms is far too short for any non-trivial
   verification condition.

2. `-t:` is a per-query soft limit. After it fires, z3 returns "unknown" for
   that query and OpenJML's interaction loop sends additional queries
   (get_value, get_info, push, additional check_sats). Each subsequent query
   gets a fresh `-t:` budget. So total wall time can be unbounded if the
   loop keeps making progress.  This was the root cause of the
   2026-04-29 Recursive5.power 25-minute hang: each individual check_sat
   timed out at 60 s but the loop kept going.

Fix
---
Pass BOTH:
  - `-t:N*1000` (per-query soft limit in ms, multiplier converts s -> ms)
  - `-T:N`     (global hard limit in s, kills the z3 process after total
                cumulative time)

The global hard limit gives an upper bound on wall time per method.

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
    "\t\t\t// z3's -t: is in MILLISECONDS. Multiply to convert.  Also pass\n"
    "\t\t\t// -T: (global hard timeout in SECONDS) so the z3 process is\n"
    "\t\t\t// guaranteed to terminate even if the OpenJML interaction loop\n"
    "\t\t\t// keeps issuing queries past the per-query soft limit.\n"
    "\t\t\tlong tms = Math.round(timeout * 1000.0);\n"
    "\t\t\tif (tms > Integer.MAX_VALUE) tms = Integer.MAX_VALUE;\n"
    "\t\t\tlong tsec = Math.round(timeout * 2.0);\n"
    "\t\t\tif (tsec > Integer.MAX_VALUE) tsec = Integer.MAX_VALUE;\n"
    "\t\t\tList<String> args = new java.util.ArrayList<String>(cmds.length+2);\n"
    "\t\t\targs.addAll(Arrays.asList(cmds));\n"
    "\t\t\tif (isWindows) {\n"
    "\t\t\t\targs.add(\"/t:\" + Long.toString(tms));\n"
    "\t\t\t\targs.add(\"/T:\" + Long.toString(tsec));\n"
    "\t\t\t} else {\n"
    "\t\t\t\targs.add(\"-t:\" + Long.toString(tms));\n"
    "\t\t\t\targs.add(\"-T:\" + Long.toString(tsec));\n"
    "\t\t\t}\n"
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
    occurrences = src.count(EDIT_OLD)
    if occurrences == 0:
        raise SystemExit(
            f"Expected at least 1 occurrence of timeout block in {path}, found 0"
        )
    # Solver_z3_4_5 has 2 occurrences (executable + String[] command ctors);
    # Solver_z3_4_3 has 1 occurrence (executable ctor only - its String[] ctor
    # uses a different timeout structure). Patch whatever we find.
    src = src.replace(EDIT_OLD, EDIT_NEW)
    path.write_text(src)
    print(f"Patched {path} ({occurrences} occurrence{'s' if occurrences > 1 else ''})")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("Usage: patch_z3_timeout.py <Solver_z3_4_5.java>")
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
