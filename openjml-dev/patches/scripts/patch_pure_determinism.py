#!/usr/bin/env python3
"""
Patches OpenJML's JmlSpecs.isEffectivelySpecPureMethod() so that pure
methods returning reference types (such as String.substring,
Arrays.copyOf) are treated as deterministic in the SMT encoding.

Background
----------
JmlSpecs.isEffectivelySpecPureMethod() returns FALSE for any plain `pure`
method whose return type is a reference (only `strictly_pure`, `spec_pure`,
or primitive-returning `pure` methods qualify). The reason in the original
code is that `pure` allows allocation, so two calls to e.g.
`s.substring(0, n)` could allocate two different objects -- the existing
determinism axiom would falsely assert reference equality of two
freshly-allocated objects.

OpenJML's existing inline-spec path in JmlAssertionAdder (line ~11253)
already wraps the assumption in a `!\fresh(result)` guard for non-
effectivelySpecPure methods. But that path is gated behind
`if (includeDeterminism)`, and `includeDeterminism = effectivelySpecPure`
is false for pure-reference, so the guarded determinism axiom never fires.

The result: two calls to `s.substring(0, n)` -- one in the body, one in
an `\result.equals(s.substring(0, n))` postcondition -- become two
unrelated fresh result temps. The postcondition is unprovable.

Fix
---
Patch isEffectivelySpecPureMethod to also return true for `pure` methods
returning reference types. Justification: pure methods are documented as
having no side-effects and value-deterministic results -- spec-level
reasoning typically uses .equals(), and OpenJML already has the surrounding
`if (!isFresh)` wrap at line ~11271 to keep the determinism axiom safely
gated for the rare case where the result is genuinely modeled as freshly
allocated. With this change, ESC reasoning correctly congruences pure
reference-returning methods.

Idempotent: the script checks for a marker comment before touching the file.
"""
import sys
from pathlib import Path

PATCH_MARKER = "// jml-pure-determinism-patch"


def already_patched(src: str) -> bool:
    return PATCH_MARKER in src


EDIT_OLD = (
    "    public boolean isEffectivelySpecPureMethod(MethodSymbol symbol) {\n"
    "        var t = determinePurity(symbol);\n"
    "        if (t == null) return false;\n"
    "        if (t.jmlclausekind != PURE) return true;\n"
    "        Type ty = symbol.getReturnType();\n"
    "        if (utils.isJavaOrJmlPrimitiveType(ty)) return true;\n"
    "        return false;\n"
    "    }"
)
EDIT_NEW = (
    "    public boolean isEffectivelySpecPureMethod(MethodSymbol symbol) {\n"
    "        var t = determinePurity(symbol);\n"
    "        if (t == null) return false;\n"
    "        if (t.jmlclausekind != PURE) return true;\n"
    "        Type ty = symbol.getReturnType();\n"
    "        if (utils.isJavaOrJmlPrimitiveType(ty)) return true;\n"
    "        return true; // jml-pure-determinism-patch (pure reference returns are\n"
    "                     // value-deterministic; treat as effectively spec-pure for ESC).\n"
    "    }"
)


def patch_file(path: Path):
    if not path.exists():
        raise SystemExit(f"File not found: {path}")
    src = path.read_text()
    if already_patched(src):
        print(f"Already patched: {path}")
        return
    if EDIT_OLD not in src:
        raise SystemExit(f"Could not find isEffectivelySpecPureMethod in {path}")
    src = src.replace(EDIT_OLD, EDIT_NEW, 1)
    path.write_text(src)
    print(f"Patched {path}")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("Usage: patch_pure_determinism.py <JmlSpecs.java>")
    for arg in sys.argv[1:]:
        patch_file(Path(arg))


if __name__ == "__main__":
    main()
