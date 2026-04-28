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
# Default to the fork-based dockerfile so the verification suite runs against
# the patched OpenJML in openjml-dev/ (define-fun-rec for \sum/\product/\num_of,
# pure-function determinism, ESC-visible String/Integer specs). Override with
# DOCKERFILE=Dockerfile.test to fall back to vanilla OpenJML 21-0.23 — many
# inferred specs will not discharge.
DOCKERFILE="${DOCKERFILE:-Dockerfile.test.fork}"
FORK_IMAGE="openjml-fork-build:latest"
FORK_DIR="$PROJECT_ROOT/openjml-dev"
# Container runtime: set DOCKER=podman to use Podman instead of Docker
DOCKER="${DOCKER:-docker}"

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
    if ! command -v $DOCKER &>/dev/null; then
        error "Docker not found. Install Docker or podman and ensure it is on PATH."
        exit 1
    fi

    if ! $DOCKER info &>/dev/null; then
        error "Docker daemon is not running. Start Docker Desktop or the Docker service."
        exit 1
    fi

    ok "Docker is available"
}

# ==============================================================================
# Build
# ==============================================================================

# Builds the openjml-dev fork image if the inferrer-test image will need it.
# The Dockerfile.test.fork variant FROM-references openjml-fork-build:latest;
# without it docker build fails with "image not found".
ensure_fork_image() {
    if [ "$DOCKERFILE" != "Dockerfile.test.fork" ]; then
        return 0
    fi

    if $DOCKER image inspect "$FORK_IMAGE" &>/dev/null; then
        info "Fork image '$FORK_IMAGE' already built"
        return 0
    fi

    if [ ! -d "$FORK_DIR" ]; then
        error "openjml-dev/ not found at $FORK_DIR"
        error "  The Dockerfile.test.fork variant depends on the patched OpenJML fork."
        error "  Either git pull to fetch openjml-dev/, or set DOCKERFILE=Dockerfile.test"
        error "  to fall back to vanilla OpenJML (many inferred specs will not discharge)."
        exit 1
    fi

    step "Building OpenJML fork image: $FORK_IMAGE"
    info "First-time fork build downloads + patches upstream OpenJML — ~10-15 minutes."
    cd "$FORK_DIR"
    $DOCKER build --platform linux/amd64 -f Dockerfile.build -t "$FORK_IMAGE" .
    cd "$PROJECT_ROOT"
    ok "Fork image '$FORK_IMAGE' built successfully"
}

do_build() {
    ensure_fork_image

    step "Building Docker image: $IMAGE_NAME (using $DOCKERFILE)"
    info "This includes OpenJML (~350MB) and may take a few minutes on first build."

    cd "$PROJECT_ROOT"
    $DOCKER build --platform linux/amd64 -f "$DOCKERFILE" -t "$IMAGE_NAME" .
    # $DOCKER build --platform linux/arm64 -f "$DOCKERFILE" -t "$IMAGE_NAME" .

    ok "Docker image '$IMAGE_NAME' built successfully"
}

# ==============================================================================
# Run tests
# ==============================================================================

do_test() {
    step "Running verification tests in Docker"

    # Check if image exists
    if ! $DOCKER image inspect "$IMAGE_NAME" &>/dev/null; then
        warn "Image '$IMAGE_NAME' not found. Building first..."
        do_build
    fi

    local mvn_args=(-B -Dsurefire.failIfNoSpecifiedTests=false)

    # Test filter: specific suite or default to all verification tests
    if [ -n "$TEST_FILTER" ]; then
        mvn_args+=(-Dtest="$TEST_FILTER")
        info "Running: $TEST_FILTER"
    else
        mvn_args+=(-Dtest="com.jml.inferrer.verification.**")
    fi

    # Show inferred JML output if requested
    if [ "$SHOW_JML" = true ]; then
        mvn_args+=(-Djml.showInferred=true)
        info "Showing inferred JML output"
    fi

    $DOCKER run --rm "$IMAGE_NAME" mvn test "${mvn_args[@]}"

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
    if $DOCKER image inspect "$IMAGE_NAME" &>/dev/null; then
        $DOCKER rmi "$IMAGE_NAME"
        ok "Removed image '$IMAGE_NAME'"
    else
        info "Image '$IMAGE_NAME' not found, nothing to clean"
    fi

    # The fork image is intentionally left in place — it's expensive to
    # rebuild and is reused across many verification runs. Pass --clean-fork
    # to remove it as well.
    if [ "${CLEAN_FORK:-false}" = true ]; then
        step "Removing OpenJML fork image: $FORK_IMAGE"
        if $DOCKER image inspect "$FORK_IMAGE" &>/dev/null; then
            $DOCKER rmi "$FORK_IMAGE"
            ok "Removed image '$FORK_IMAGE'"
        else
            info "Image '$FORK_IMAGE' not found, nothing to clean"
        fi
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

    local mode=""
    TEST_FILTER=""
    SHOW_JML=false

    # Parse arguments
    while [ $# -gt 0 ]; do
        case "$1" in
            --build|-b)       mode="build" ;;
            --test-only|-t)   mode="test-only" ;;
            --clean|-c)       mode="clean" ;;
            --clean-fork)     mode="clean"; CLEAN_FORK=true ;;
            --vanilla)        DOCKERFILE="Dockerfile.test" ;;
            --help|-h)        mode="help" ;;
            --show-jml)       SHOW_JML=true ;;
            --test)
                shift
                if [ -z "$1" ]; then
                    error "--test requires a test class or method name"
                    exit 1
                fi
                TEST_FILTER="$1"
                ;;
            *)
                error "Unknown option: $1"
                echo "Run '$0 --help' for usage."
                exit 1
                ;;
        esac
        shift
    done

    mode="${mode:-all}"

    case "$mode" in
        build)
            do_build
            ;;
        test-only)
            do_test
            ;;
        clean)
            do_clean
            ;;
        help)
            echo ""
            echo "Usage: $0 [options]"
            echo ""
            echo "Options:"
            echo "  (no args)     Build image (if needed) and run all verification tests"
            echo "  --build       Build the Docker image only"
            echo "  --test-only   Run tests only (builds image if not found)"
            echo "  --clean       Remove the inferrer-test image (fork image kept)"
            echo "  --clean-fork  Same as --clean, also remove openjml-fork-build"
            echo "  --vanilla     Use Dockerfile.test (vanilla OpenJML 21-0.23) instead"
            echo "                of Dockerfile.test.fork (patched fork). Many inferred"
            echo "                specs will not discharge under vanilla — only useful"
            echo "                for measuring the fork's contribution."
            echo "  --show-jml    Print inferred JML specifications for each test"
            echo "  --test NAME   Run specific test suite or method, e.g.:"
            echo "                  --test 'com.jml.inferrer.verification.BitwiseSwitchVerificationTest'"
            echo "                  --test '...BitwiseSwitchVerificationTest#switchDispatchCalc'"
            echo "  --help        Show this help"
            echo ""
            echo "Examples:"
            echo "  $0                                    # build + run all"
            echo "  $0 --test-only --show-jml             # run all, show JML output"
            echo "  $0 --test-only --test '...StringOperationVerificationTest'"
            echo "  $0 --test-only --test '...BitwiseSwitchVerificationTest#popcount' --show-jml"
            echo ""
            ;;
        all)
            do_build
            do_test
            ;;
    esac
}

main "$@"
