#!/usr/bin/env bash
# ==============================================================================
# run-verification-tests-macos-arm64.sh
#
# macOS Apple Silicon (M1/M2/M3) variant of run-verification-tests.sh.
#
# OpenJML does not publish a Linux/arm64 binary — only Linux/amd64
# (openjml-ubuntu-22.04) and macOS/arm64 (openjml-macos-14). Because the test
# image is Linux-based, it must be built and run as linux/amd64 under Rosetta 2
# emulation on Apple Silicon.
#
# This script differs from run-verification-tests.sh in two ways:
#   1. Passes --platform linux/amd64 to BOTH build and run (Docker on arm64
#      refuses to execute amd64 images without an explicit platform on run).
#   2. Checks that Rosetta 2 emulation is available.
#
# Usage:
#   ./run-verification-tests-macos-arm64.sh              # build image + run tests
#   ./run-verification-tests-macos-arm64.sh --build      # build the Docker image only
#   ./run-verification-tests-macos-arm64.sh --test-only  # run tests only (assumes image built)
#   ./run-verification-tests-macos-arm64.sh --clean      # remove the Docker image
# ==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR"
IMAGE_NAME="jml-inferrer-tests"
DOCKERFILE="Dockerfile.test"
PLATFORM="linux/amd64"
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

check_arch() {
    local arch
    arch="$(uname -m)"
    if [ "$arch" != "arm64" ] && [ "$arch" != "aarch64" ]; then
        warn "Host arch is '$arch', not arm64. This script is intended for Apple Silicon."
        warn "On amd64 hosts use run-verification-tests.sh instead."
    else
        ok "Host arch: $arch (Apple Silicon)"
    fi
}

check_docker() {
    if ! command -v $DOCKER &>/dev/null; then
        error "Docker not found. Install Docker Desktop for Mac (Apple Silicon)."
        exit 1
    fi

    if ! $DOCKER info &>/dev/null; then
        error "Docker daemon is not running. Start Docker Desktop."
        exit 1
    fi

    ok "Docker is available"
}

check_rosetta() {
    # Rosetta 2 is required to run linux/amd64 images on Apple Silicon.
    # Docker Desktop offers either its classic QEMU-based emulation or the
    # faster Rosetta-backed emulation; either will execute the image, but if
    # neither is present, the `docker run` step will fail.
    if [ "$(uname -s)" = "Darwin" ] && [ "$(uname -m)" = "arm64" ]; then
        if ! /usr/bin/pgrep -q oahd && ! [ -d /Library/Apple/usr/libexec/oah ]; then
            warn "Rosetta 2 does not appear to be installed."
            warn "Install it with: softwareupdate --install-rosetta --agree-to-license"
            warn "Continuing — Docker Desktop's built-in emulation may still work."
        else
            ok "Rosetta 2 detected"
        fi
    fi
}

# ==============================================================================
# Build
# ==============================================================================

do_build() {
    step "Building Docker image: $IMAGE_NAME (platform: $PLATFORM)"
    info "Using amd64 emulation via Rosetta 2 — build will be slower than native."
    info "Image includes OpenJML (~350MB) and may take several minutes on first build."

    cd "$PROJECT_ROOT"
    $DOCKER build --platform "$PLATFORM" -f "$DOCKERFILE" -t "$IMAGE_NAME" .

    ok "Docker image '$IMAGE_NAME' built successfully"
}

# ==============================================================================
# Run tests
# ==============================================================================

do_test() {
    step "Running verification tests in Docker (platform: $PLATFORM)"

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

    $DOCKER run --rm --platform "$PLATFORM" "$IMAGE_NAME" mvn test "${mvn_args[@]}"

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
}

# ==============================================================================
# Main
# ==============================================================================

main() {
    echo -e "${BOLD}==================================================${NC}"
    echo -e "${BOLD} JML Inferrer - Verification Tests (macOS arm64)${NC}"
    echo -e "${BOLD}==================================================${NC}"

    check_arch
    check_docker
    check_rosetta

    local mode=""
    TEST_FILTER=""
    SHOW_JML=false

    # Parse arguments
    while [ $# -gt 0 ]; do
        case "$1" in
            --build|-b)       mode="build" ;;
            --test-only|-t)   mode="test-only" ;;
            --clean|-c)       mode="clean" ;;
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
            echo "macOS Apple Silicon variant — forces linux/amd64 platform on"
            echo "build and run so the amd64 OpenJML binary runs under Rosetta 2."
            echo ""
            echo "Options:"
            echo "  (no args)     Build image (if needed) and run all verification tests"
            echo "  --build       Build the Docker image only"
            echo "  --test-only   Run tests only (builds image if not found)"
            echo "  --clean       Remove the Docker image"
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
            echo ""
            ;;
        all)
            do_build
            do_test
            ;;
    esac
}

main "$@"
