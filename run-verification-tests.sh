#!/usr/bin/env bash
# ==============================================================================
# run-verification-tests.sh
#
# Builds and runs the formal verification test suite inside a Docker container
# with OpenJML pre-installed.
#
# Usage:
#   ./run-verification-tests.sh              # build image + run tests
#   ./run-verification-tests.sh --build      # build the Docker image only
#   ./run-verification-tests.sh --test-only  # run tests only (assumes image built)
#   ./run-verification-tests.sh --clean      # remove the Docker image
# ==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR"
IMAGE_NAME="jml-inferrer-tests"
DOCKERFILE="Dockerfile.test"

# Colors (disable if not a terminal)
if [ -t 1 ]; then
    RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'
    BLUE='\033[0;34m'; BOLD='\033[1m'; NC='\033[0m'
else
    RED=''; GREEN=''; YELLOW=''; BLUE=''; BOLD=''; NC=''
fi

info()  { echo -e "${BLUE}[INFO]${NC}  $*"; }
ok()    { echo -e "${GREEN}[OK]${NC}    $*"; }
warn()  { echo -e "${YELLOW}[WARN]${NC}  $*"; }
error() { echo -e "${RED}[ERROR]${NC} $*"; }
step()  { echo -e "\n${BOLD}==> $*${NC}"; }

# ==============================================================================
# Check prerequisites
# ==============================================================================

check_docker() {
    if ! command -v docker &>/dev/null; then
        error "Docker not found. Install Docker and ensure 'docker' is on PATH."
        exit 1
    fi

    if ! docker info &>/dev/null; then
        error "Docker daemon is not running. Start Docker Desktop or the Docker service."
        exit 1
    fi

    ok "Docker is available"
}

# ==============================================================================
# Build
# ==============================================================================

do_build() {
    step "Building Docker image: $IMAGE_NAME"
    info "This includes OpenJML (~350MB) and may take a few minutes on first build."

    cd "$PROJECT_ROOT"
    docker build -f "$DOCKERFILE" -t "$IMAGE_NAME" .

    ok "Docker image '$IMAGE_NAME' built successfully"
}

# ==============================================================================
# Run tests
# ==============================================================================

do_test() {
    step "Running verification tests in Docker"

    # Check if image exists
    if ! docker image inspect "$IMAGE_NAME" &>/dev/null; then
        warn "Image '$IMAGE_NAME' not found. Building first..."
        do_build
    fi

    docker run --rm "$IMAGE_NAME" \
        mvn test -B -Dtest="com.jml.inferrer.verification.**" \
        -Dsurefire.failIfNoSpecifiedTests=false

    local exit_code=$?

    echo ""
    if [ $exit_code -eq 0 ]; then
        ok "All verification tests passed!"
    else
        error "Some tests failed (exit code: $exit_code)"
    fi
    return $exit_code
}

# ==============================================================================
# Clean
# ==============================================================================

do_clean() {
    step "Removing Docker image: $IMAGE_NAME"
    if docker image inspect "$IMAGE_NAME" &>/dev/null; then
        docker rmi "$IMAGE_NAME"
        ok "Removed image '$IMAGE_NAME'"
    else
        info "Image '$IMAGE_NAME' not found, nothing to clean"
    fi
}

# ==============================================================================
# Main
# ==============================================================================

main() {
    echo -e "${BOLD}=============================================${NC}"
    echo -e "${BOLD} JML Inferrer - Formal Verification Test Suite${NC}"
    echo -e "${BOLD}=============================================${NC}"

    check_docker

    local mode="${1:-all}"

    case "$mode" in
        --build|-b)
            do_build
            ;;
        --test-only|-t)
            do_test
            ;;
        --clean|-c)
            do_clean
            ;;
        --help|-h)
            echo ""
            echo "Usage: $0 [option]"
            echo ""
            echo "Options:"
            echo "  (no args)     Build image (if needed) and run verification tests"
            echo "  --build       Build the Docker image only"
            echo "  --test-only   Run tests only (builds image if not found)"
            echo "  --clean       Remove the Docker image"
            echo "  --help        Show this help"
            echo ""
            ;;
        all|"")
            do_build
            do_test
            ;;
        *)
            error "Unknown option: $mode"
            echo "Run '$0 --help' for usage."
            exit 1
            ;;
    esac
}

main "$@"
