#!/bin/bash
# Build the project and run inference + OpenJML validation on sample code.
#
# Default mode runs locally and uses whatever OpenJML the inferrer's
# OpenJMLInstaller can find (OPENJML_HOME env var, or the auto-installed
# OpenJML 21-0.23 vanilla download). Many inferred specs will not discharge
# under vanilla — the fork in openjml-dev/ adds the patches needed for
# accumulator quantifiers, pure-function determinism, and ESC-visible
# String/Integer specs.
#
# Usage:
#   ./run-validate.sh              # local run, OPENJML_HOME or auto-install
#   ./run-validate.sh --use-fork   # run inside Docker against the patched fork

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR"

USE_FORK=false
for arg in "$@"; do
    case "$arg" in
        --use-fork) USE_FORK=true ;;
        --help|-h)
            sed -n '2,12p' "$0"
            exit 0
            ;;
        *)
            echo "Unknown option: $arg" >&2
            echo "Usage: $0 [--use-fork]" >&2
            exit 1
            ;;
    esac
done

if [ "$USE_FORK" = true ]; then
    echo "Validating against the patched OpenJML fork (Docker)..."
    cd "$PROJECT_ROOT"

    FORK_IMAGE="openjml-fork-build:latest"
    if ! docker image inspect "$FORK_IMAGE" >/dev/null 2>&1; then
        if [ ! -d "$PROJECT_ROOT/openjml-dev" ]; then
            echo "ERROR: openjml-dev/ not found and $FORK_IMAGE not built." >&2
            exit 1
        fi
        echo "Building fork image (~10-15 minutes first time)..."
        docker build -f openjml-dev/Dockerfile.build -t "$FORK_IMAGE" openjml-dev/
    fi

    # Use the test-image build flow (which includes OpenJML), then override
    # the entrypoint to run the inferrer JAR with --validate. The test image
    # already has Maven + JDK + the fork-built OpenJML wired in via OPENJML_HOME.
    docker compose build test
    docker compose run --rm test sh -c "mvn -q clean package && java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar experiment/sample_code --validate"
    exit $?
fi

echo "Building JML Inferrer..."
mvn clean package -q

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

echo "Running inference and validation on sample code (local OpenJML)..."
echo "  (Pass --use-fork to run against the patched OpenJML in openjml-dev/)"
java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar experiment/sample_code --validate
