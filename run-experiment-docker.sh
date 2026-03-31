#!/bin/bash
# =============================================================================
# JML Experiment Runner - Docker Wrapper
# =============================================================================
# Builds and runs the experiment pipeline inside a Docker container.
# All CLI arguments are passed through to run-experiment.sh inside the container.
#
# Usage (remote repo):
#   ./run-experiment-docker.sh --repo https://github.com/user/project.git --api-key KEY
#   ./run-experiment-docker.sh --repo git@github.com:user/project.git --api-key KEY --branch dev
#
# Usage (local repo):
#   ./run-experiment-docker.sh --repo /path/to/java/repo --api-key KEY
#   ./run-experiment-docker.sh --repo ./my-project --api-key KEY --runs 3 --phases P1,P3
#
# Usage (env var for key):
#   GEMINI_API_KEY=KEY ./run-experiment-docker.sh --repo https://github.com/user/project.git
# =============================================================================

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

# Container runtime: set DOCKER=podman to use Podman instead of Docker
DOCKER="${DOCKER:-docker}"

CLONE_DIR="$SCRIPT_DIR/.clone-cache"

# --------------- Parse args ---------------
# We extract --api-key, --repo, and --branch for Docker-level handling,
# then rewrite the args that get passed into the container.
REPO_INPUT=""
REPO_BRANCH=""
FORWARD_ARGS=()
ARGS=("$@")
i=0
while [[ $i -lt ${#ARGS[@]} ]]; do
    case "${ARGS[$i]}" in
        --api-key)
            export GEMINI_API_KEY="${ARGS[$((i + 1))]}"
            # Still forward --api-key to the container script
            FORWARD_ARGS+=("${ARGS[$i]}" "${ARGS[$((i + 1))]}")
            i=$((i + 2))
            ;;
        --repo)
            REPO_INPUT="${ARGS[$((i + 1))]}"
            i=$((i + 2))
            ;;
        --branch)
            REPO_BRANCH="${ARGS[$((i + 1))]}"
            i=$((i + 2))
            ;;
        --help)
            echo "Usage: $0 --repo <path-or-url> [options]"
            echo ""
            echo "Docker wrapper options:"
            echo "  --repo PATH|URL       Java repository to analyze (local path or Git URL)"
            echo "  --branch BRANCH       Branch to clone (default: repo default branch)"
            echo "  --api-key KEY         Gemini API key (or set GEMINI_API_KEY env var)"
            echo ""
            echo "Pass-through options (forwarded to run-experiment.sh):"
            echo "  --model MODEL         Gemini model (default: gemini-2.0-flash)"
            echo "  --runs N              Runs per configuration (default: 5)"
            echo "  --phases P1,P2,...    Phases to run (default: P1,P2,P3,P4)"
            echo "  --skip-inference      Skip JML inference step"
            echo "  --skip-generation     Skip test generation (use existing tests)"
            echo "  --skip-tests          Skip Maven test compilation/execution"
            echo "  --skip-pitest         Skip PiTest mutation testing"
            echo ""
            echo "Examples:"
            echo "  $0 --repo https://github.com/apache/commons-lang.git --api-key KEY"
            echo "  $0 --repo git@github.com:user/project.git --branch main --api-key KEY"
            echo "  $0 --repo ./my-local-project --api-key KEY --runs 3"
            exit 0
            ;;
        *)
            FORWARD_ARGS+=("${ARGS[$i]}")
            i=$((i + 1))
            ;;
    esac
done

# --------------- Validation ---------------
if [[ -z "${GEMINI_API_KEY:-}" ]]; then
    echo "ERROR: Gemini API key required."
    echo "  Use: $0 --api-key YOUR_KEY --repo <path-or-url> [options]"
    echo "  Or:  GEMINI_API_KEY=YOUR_KEY $0 --repo <path-or-url> [options]"
    exit 1
fi

if [[ -z "$REPO_INPUT" ]]; then
    echo "ERROR: Repository path or URL required."
    echo "  Use: $0 --repo <path-or-url> --api-key KEY [options]"
    exit 1
fi

# --------------- Resolve repository ---------------
# Detect if --repo is a Git URL or a local path.
is_git_url() {
    local input="$1"
    # Match https://, http://, git://, ssh://, or git@host: patterns
    [[ "$input" =~ ^https?:// ]] || \
    [[ "$input" =~ ^git:// ]] || \
    [[ "$input" =~ ^ssh:// ]] || \
    [[ "$input" =~ ^git@ ]]
}

CLEANUP_CLONE=""
if is_git_url "$REPO_INPUT"; then
    # Remote URL — clone to a local cache directory
    if ! command -v git &> /dev/null; then
        echo "ERROR: git is required to clone remote repositories."
        exit 1
    fi

    # Derive a directory name from the URL
    REPO_NAME="$(basename "$REPO_INPUT" .git)"
    LOCAL_CLONE="$CLONE_DIR/$REPO_NAME"

    if [[ -d "$LOCAL_CLONE/.git" ]]; then
        echo "Updating cached clone: $LOCAL_CLONE"
        git -C "$LOCAL_CLONE" fetch --all --prune --quiet
        if [[ -n "$REPO_BRANCH" ]]; then
            git -C "$LOCAL_CLONE" checkout "$REPO_BRANCH" --quiet
            git -C "$LOCAL_CLONE" pull --quiet
        else
            git -C "$LOCAL_CLONE" pull --quiet
        fi
    else
        echo "Cloning $REPO_INPUT ..."
        mkdir -p "$CLONE_DIR"
        CLONE_ARGS=(git clone --depth 1)
        if [[ -n "$REPO_BRANCH" ]]; then
            CLONE_ARGS+=(--branch "$REPO_BRANCH")
        fi
        CLONE_ARGS+=("$REPO_INPUT" "$LOCAL_CLONE")
        "${CLONE_ARGS[@]}"
    fi

    REPO_PATH="$LOCAL_CLONE"
    echo "Repository (cloned): $REPO_PATH"
else
    # Local path — resolve to absolute
    REPO_PATH="$(cd "$REPO_INPUT" 2>/dev/null && pwd)" || {
        echo "ERROR: Repository path does not exist: $REPO_INPUT"
        exit 1
    }
    echo "Repository (local): $REPO_PATH"
fi

# Inject --source-dir pointing to the container mount path
FORWARD_ARGS+=("--source-dir" "/app/repo")

# --------------- Detect compose command ---------------
if $DOCKER compose version &> /dev/null; then
    COMPOSE="$DOCKER compose"
elif command -v "${DOCKER}-compose" &> /dev/null; then
    COMPOSE="${DOCKER}-compose"
else
    echo "ERROR: Neither '$DOCKER compose' (v2) nor '${DOCKER}-compose' (v1) found."
    echo "Please install Docker/Podman Compose, or set DOCKER=podman."
    exit 1
fi

echo "Using: $COMPOSE"

# --------------- Create host results directory ---------------
mkdir -p experiment-results

# --------------- Build and run ---------------
echo "Building Docker image..."
$COMPOSE build experiment

echo "Running experiment in container..."
$COMPOSE run --rm -v "$REPO_PATH:/app/repo:ro" experiment "${FORWARD_ARGS[@]}"

echo ""
echo "Results available in: $SCRIPT_DIR/experiment-results/"
