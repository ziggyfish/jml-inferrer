#!/usr/bin/env bash
# ==============================================================================
# run-verification-tests-macos-arm64.sh  [DEPRECATED — kept as compatibility shim]
#
# As of the run-verification-tests.sh rewrite that auto-detects host OS, arch,
# and container runtime (docker vs podman), this script is no longer needed —
# the main script covers Apple Silicon natively (forces linux/amd64 platform,
# detects Rosetta 2, etc.).
#
# This shim simply forwards every argument to run-verification-tests.sh so any
# existing tooling that calls this script continues to work. Please migrate
# callers to run-verification-tests.sh and delete this file.
# ==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
echo "[DEPRECATED] run-verification-tests-macos-arm64.sh is now a shim — calling run-verification-tests.sh" >&2
exec "$SCRIPT_DIR/run-verification-tests.sh" "$@"
