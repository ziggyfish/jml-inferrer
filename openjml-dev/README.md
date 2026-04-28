# openjml-dev — vendored OpenJML fork

This directory holds the patches and build wrappers for the OpenJML fork the
Inferrer's verification suite runs against. Upstream is OpenJML 21-0.23
(<https://github.com/OpenJML/OpenJML>); the patches in `patches/scripts/` are
applied at fork-build time.

The fork is needed because vanilla OpenJML 21-0.23, when run with the strict
flags this project uses (`--code-math=safe --spec-math=bigint
--arithmetic-failure=hard --nullable-by-default`), cannot discharge a number of
inferred specifications that are correct but use language features the upstream
SMT translation handles weakly (recursive accumulator definitions; pure-method
referential identity; some `String.toLowerCase`-style stdlib model gaps).

## Layout

| Path | What it is |
|---|---|
| `Dockerfile.build` | Builds the fork image `openjml-fork-build:latest`. Pulls upstream OpenJML, applies the patches in `patches/scripts/` in order, packages the result. |
| `Dockerfile.test` | Lightweight smoke-test image that runs OpenJML on `test-fixtures/` to confirm the patches landed. |
| `patches/scripts/` | Idempotent Python patch scripts. Each guards itself with a marker comment so re-applying is a no-op. |
| `patches/new-files/` | Files added wholesale to the OpenJML source tree (rather than diffed into existing files). |
| `test-fixtures/` | Tiny Java sources used by the smoke-test container to confirm specific patches are active. |
| `Sum*.java` | Inductive-sum smoke fixtures (legacy; pre-date `test-fixtures/`). |

## Patches

### `patch_smttranslator.py`
Adds `define-fun-rec` emission for `\sum`, `\product`, `\num_of` so the SMT
translator can express recursive accumulator quantifiers. Required to discharge
loop-invariant + postcondition pairs of the shape
`sum == (\sum int k; lo<=k<i; arr[k])` — vanilla OpenJML emits these as
underspecified `define-fun` placeholders that z3 cannot evaluate inductively.
See also `patches/new-files/C_define_fun_rec.java`,
`patches/new-files/JmlBoundsExtractor.java`.

### `patch_string_jml.py`
Replaces the `-RAC@` (RAC-only) spec blocks in upstream `Specs/java/lang/String.jml`
and `Integer.jml` with ESC-visible specs that use only `length()`, `equals()`,
and arithmetic. Without this, ESC mode sees no useful postcondition for
`toLowerCase`, `toUpperCase`, `trim`, `strip`, `parseInt`, etc. — so any caller
that relies on, e.g., `\result.length() == s.length()` cannot discharge.
Idempotent: each replacement is guarded by a `// jml-string-transform-patch`
marker.

### `patch_pure_determinism.py`
Single-edit patch on `JmlSpecs.isEffectivelySpecPureMethod` that flips the
return value to `true` for reference-returning pure methods. This activates
OpenJML's existing determinism-axiom path in `JmlAssertionAdder` for
`String.substring`, `Arrays.copyOf`, etc. — making `f(x) == f(x)` hold by
congruence in the SMT encoding. Without this, two calls to `s.substring(0, n)`
in the same spec produce two distinct unconstrained results and any
`\result.equals(s.substring(0, n))`-style postcondition fails. The surrounding
`if (!isFresh)` safety wrap is preserved, so genuinely fresh allocations remain
unaffected.

## Building

From this directory:

```bash
docker build -f Dockerfile.build -t openjml-fork-build:latest .
```

The Inferrer's `docker-compose.yml` references `openjml-fork-build:latest`
indirectly via `Dockerfile.test.fork` in the project root — running
`docker compose build test` from the project root rebuilds the inferrer-test
image against the latest fork image.

## Smoke testing

```bash
docker build -f test-fixtures/Dockerfile.smoke -t openjml-fork-smoke:latest .
docker run --rm openjml-fork-smoke:latest
```

Each fixture in `test-fixtures/` exercises a specific patch — a non-zero exit
or `Invalid` result indicates the patch did not land cleanly.

## Updating upstream

To rebase on a new OpenJML upstream release, edit `Dockerfile.build` to point
at the new tag/commit, rebuild, and re-run the smoke fixtures. Each patch
script is idempotent and uses string-match guards, so most upstream changes
will not break them — but a structural rename (e.g., `JmlSpecs` field
renamed) will require a one-line update to the matching pattern.
