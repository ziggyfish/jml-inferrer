#!/usr/bin/env bash
# ==============================================================================
# run-verification-tests.sh
#
# Builds and runs the formal verification test suite inside a container with
# the patched OpenJML pre-installed. Works on Linux (amd64 native, arm64 with
# emulation), macOS (Apple Silicon via Rosetta 2, Intel native), and Windows
# (via WSL2 / Git Bash). Auto-detects Docker vs Podman.
#
# Usage:
#   ./run-verification-tests.sh              # build image + run tests
#   ./run-verification-tests.sh --build      # build the Docker image only
#   ./run-verification-tests.sh --test-only  # run tests only (assumes image built)
#   ./run-verification-tests.sh --clean      # remove the Docker image
#   ./run-verification-tests.sh --help       # show full help
# ==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR"
IMAGE_NAME="jml-inferrer-tests"
# Default to the fork-based dockerfile so the verification suite runs against
# the patched OpenJML in openjml-dev/ (define-fun-rec for \sum/\product/\num_of,
# pure-function determinism, ESC-visible String/Integer specs). Override with
# DOCKERFILE=Dockerfile.test (or --vanilla) to fall back to vanilla OpenJML
# 21-0.23 — many inferred specs will not discharge.
DOCKERFILE="${DOCKERFILE:-Dockerfile.test.fork}"
FORK_IMAGE="openjml-fork-build:latest"
FORK_DIR="$PROJECT_ROOT/openjml-dev"

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
# Container runtime detection (Docker vs Podman)
# ==============================================================================

# Prefer the explicit override (DOCKER=... or RUNTIME=...). Otherwise auto-detect:
# pick whichever of docker or podman is on PATH. If both are present, prefer
# docker (more common, consistent CLI) — set DOCKER=podman to flip.
detect_runtime() {
    if [ -n "${DOCKER:-}" ]; then
        echo "$DOCKER"; return
    fi
    if [ -n "${RUNTIME:-}" ]; then
        echo "$RUNTIME"; return
    fi
    if command -v docker &>/dev/null; then
        echo "docker"; return
    fi
    if command -v podman &>/dev/null; then
        echo "podman"; return
    fi
    echo ""
}

DOCKER="$(detect_runtime)"

# ==============================================================================
# Platform detection
# ==============================================================================

# OpenJML 21-0.23 ships with amd64-only z3 binaries in Solvers-linux/, so the
# fork build and the test image both run as linux/amd64 even on arm64 hosts
# (Apple Silicon, Linux aarch64). The override `PLATFORM=linux/arm64` is
# accepted for users who have arranged arm64-native solvers.
detect_platform() {
    if [ -n "${PLATFORM:-}" ]; then
        echo "$PLATFORM"; return
    fi
    # Default everywhere — works native on amd64, emulated on arm64.
    echo "linux/amd64"
}

PLATFORM="$(detect_platform)"
HOST_OS="$(uname -s)"
HOST_ARCH="$(uname -m)"

# ==============================================================================
# Check prerequisites
# ==============================================================================

check_runtime() {
    if [ -z "$DOCKER" ]; then
        error "Neither docker nor podman found on PATH."
        error "  Install Docker Desktop (https://www.docker.com/products/docker-desktop/),"
        error "  Docker Engine, or Podman (https://podman.io/), or pass DOCKER=<binary>."
        exit 1
    fi

    # `docker info` and `podman info` both return non-zero when the daemon /
    # service isn't running. Podman in rootless mode doesn't need a daemon and
    # `podman info` succeeds without one, so this check covers both runtimes.
    if ! $DOCKER info &>/dev/null; then
        error "$DOCKER is installed but not running."
        if [ "$DOCKER" = "docker" ]; then
            error "  Start Docker Desktop, or run \`sudo systemctl start docker\`."
        else
            error "  Run \`podman machine start\` (Mac/Win) or check the podman service."
        fi
        exit 1
    fi

    ok "Container runtime: $DOCKER ($($DOCKER --version 2>/dev/null | head -1))"
}

# Apple Silicon: amd64 emulation needs Rosetta 2 (or QEMU fallback). Warn if
# absent — the run will still attempt via QEMU but be much slower.
check_apple_silicon_emulation() {
    if [ "$HOST_OS" = "Darwin" ] && [ "$HOST_ARCH" = "arm64" ] && [ "$PLATFORM" = "linux/amd64" ]; then
        if /usr/bin/pgrep -q oahd 2>/dev/null || [ -d /Library/Apple/usr/libexec/oah ]; then
            ok "Rosetta 2 detected (linux/amd64 emulation will be near-native)"
        else
            warn "Apple Silicon detected but Rosetta 2 does not appear installed."
            warn "  Install with: softwareupdate --install-rosetta --agree-to-license"
            warn "  Continuing — Docker Desktop / Podman will fall back to QEMU (slower)."
        fi
    fi
}

print_environment() {
    info "Host OS:       $HOST_OS ($HOST_ARCH)"
    info "Container:     $DOCKER"
    info "Build platform: $PLATFORM"
    info "Dockerfile:    $DOCKERFILE"
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
        error "  Either git pull to fetch openjml-dev/, or pass --vanilla to fall back"
        error "  to upstream OpenJML (many inferred specs will not discharge)."
        exit 1
    fi

    step "Building OpenJML fork image: $FORK_IMAGE"
    if [ "$HOST_ARCH" = "arm64" ] || [ "$HOST_ARCH" = "aarch64" ]; then
        info "First-time fork build downloads + patches upstream OpenJML — ~15-20 min on arm64 emulation."
    else
        info "First-time fork build downloads + patches upstream OpenJML — ~10-15 min."
    fi
    cd "$FORK_DIR"
    $DOCKER build --platform "$PLATFORM" -f Dockerfile.build -t "$FORK_IMAGE" .
    cd "$PROJECT_ROOT"
    ok "Fork image '$FORK_IMAGE' built successfully"
}

do_build() {
    ensure_fork_image

    step "Building Docker image: $IMAGE_NAME (using $DOCKERFILE, platform $PLATFORM)"
    info "This includes OpenJML (~350MB) and may take a few minutes on first build."

    cd "$PROJECT_ROOT"
    $DOCKER build --platform "$PLATFORM" -f "$DOCKERFILE" -t "$IMAGE_NAME" .

    ok "Docker image '$IMAGE_NAME' built successfully"
}

# ==============================================================================
# Run tests
# ==============================================================================

do_test() {
    step "Running verification tests (platform $PLATFORM)"

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
            --podman)         DOCKER="podman" ;;
            --docker)         DOCKER="docker" ;;
            --platform)
                shift
                if [ -z "$1" ]; then
                    error "--platform requires a value (e.g. linux/amd64, linux/arm64)"
                    exit 1
                fi
                PLATFORM="$1"
                ;;
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

    if [ "$mode" != "help" ]; then
        check_runtime
        check_apple_silicon_emulation
        print_environment
    fi

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
            echo "  --podman      Force podman as container runtime"
            echo "  --docker      Force docker as container runtime"
            echo "  --platform P  Container platform (default linux/amd64; the OpenJML"
            echo "                fork ships amd64-only z3 binaries, so amd64 is needed"
            echo "                even on arm64 hosts — emulation runs near-native via"
            echo "                Rosetta 2 on Apple Silicon and via QEMU elsewhere)"
            echo "  --show-jml    Print inferred JML specifications for each test"
            echo "  --test NAME   Run specific test suite or method, e.g.:"
            echo "                  --test 'com.jml.inferrer.verification.BitwiseSwitchVerificationTest'"
            echo "                  --test '...BitwiseSwitchVerificationTest#switchDispatchCalc'"
            echo "  --help        Show this help"
            echo ""
            echo "Environment variables:"
            echo "  DOCKER        Container runtime (docker | podman). Auto-detected."
            echo "  DOCKERFILE    Override the Dockerfile (default Dockerfile.test.fork)."
            echo "  PLATFORM      Override the platform (default linux/amd64)."
            echo ""
            echo "Examples:"
            echo "  $0                                    # build + run all"
            echo "  $0 --test-only --show-jml             # run all, show JML output"
            echo "  $0 --podman                           # use podman explicitly"
            echo "  $0 --test-only --test '...StringOperationVerificationTest'"
            echo "  DOCKER=podman PLATFORM=linux/arm64 $0 --build   # custom env"
            echo ""
            ;;
        all)
            do_build
            do_test
            ;;
    esac
}

main "$@"
