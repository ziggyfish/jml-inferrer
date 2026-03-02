#!/bin/bash
# =============================================================================
# JML Experiment Runner - Full Automation Script
# =============================================================================
# Orchestrates the complete experiment pipeline:
#   1. Build the JML-Inferrer project
#   2. Run ExperimentRunner (JML inference + Gemini test generation)
#   3. Compile and run generated tests (Maven surefire)
#   4. Run PiTest mutation testing per phase
#   5. Parse results and generate summary report
# =============================================================================

set -e

# --------------- Configuration ---------------
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$SCRIPT_DIR"
TEST_PROJECT_DIR="$PROJECT_DIR/experiment/commons-test-project"
OUTPUT_DIR="$PROJECT_DIR/experiment/results"
JAR_FILE="$PROJECT_DIR/target/jml-inferrer-1.0.0-jar-with-dependencies.jar"

# Defaults (can be overridden by CLI args)
API_KEY="${GEMINI_API_KEY:-}"
MODEL="gemini-2.0-flash"
RUNS=5
PHASES="P1,P2,P3,P4"
SOURCE_DIR=""
SKIP_INFERENCE=""
SKIP_GENERATION=""
SKIP_TESTS=""
SKIP_PITEST=""

# --------------- Argument Parsing ---------------
PASSTHROUGH_ARGS=()
while [[ $# -gt 0 ]]; do
    case "$1" in
        --api-key)       API_KEY="$2"; shift 2 ;;
        --model)         MODEL="$2"; shift 2 ;;
        --runs)          RUNS="$2"; shift 2 ;;
        --phases)        PHASES="$2"; shift 2 ;;
        --output-dir)    OUTPUT_DIR="$2"; shift 2 ;;
        --source-dir)    SOURCE_DIR="$2"; shift 2 ;;
        --skip-inference) SKIP_INFERENCE="--skip-inference"; shift ;;
        --skip-generation) SKIP_GENERATION="true"; shift ;;
        --skip-tests)    SKIP_TESTS="true"; shift ;;
        --skip-pitest)   SKIP_PITEST="true"; shift ;;
        --help)
            echo "Usage: $0 [options]"
            echo ""
            echo "Options:"
            echo "  --api-key KEY        Gemini API key (or set GEMINI_API_KEY env var)"
            echo "  --model MODEL        Gemini model (default: gemini-2.0-flash)"
            echo "  --runs N             Runs per configuration (default: 5)"
            echo "  --phases P1,P2,...   Phases to run (default: P1,P2,P3,P4)"
            echo "  --output-dir DIR     Output directory (default: experiment/results)"
            echo "  --source-dir DIR     Source directory to analyze (overrides default)"
            echo "  --skip-inference     Skip JML inference step"
            echo "  --skip-generation    Skip test generation (use existing tests)"
            echo "  --skip-tests         Skip Maven test compilation/execution"
            echo "  --skip-pitest        Skip PiTest mutation testing"
            echo "  --help               Show this help message"
            exit 0
            ;;
        *) PASSTHROUGH_ARGS+=("$1"); shift ;;
    esac
done

# --------------- Validation ---------------
echo "============================================"
echo "  JML Experiment Runner"
echo "============================================"

# Check Java
if ! command -v java &> /dev/null; then
    echo "ERROR: java not found. Please install Java 21+."
    exit 1
fi
echo "Java:  $(java -version 2>&1 | head -1)"

# Check Maven
if ! command -v mvn &> /dev/null; then
    echo "ERROR: mvn not found. Please install Maven."
    exit 1
fi
echo "Maven: $(mvn -version 2>&1 | head -1)"

# Check API key (only needed for generation)
if [[ -z "$SKIP_GENERATION" && -z "$API_KEY" ]]; then
    echo "ERROR: Gemini API key required. Use --api-key KEY or set GEMINI_API_KEY env var."
    exit 1
fi

echo "Model:  $MODEL"
echo "Runs:   $RUNS"
echo "Phases: $PHASES"
echo "Output: $OUTPUT_DIR"
echo "============================================"

# --------------- Step 1: Build Project ---------------
echo ""
echo "[Step 1/5] Building JML-Inferrer project..."
cd "$PROJECT_DIR"
mvn clean package -q -DskipTests
echo "  Build successful: $JAR_FILE"

# --------------- Step 2: Run ExperimentRunner ---------------
if [[ -z "$SKIP_GENERATION" ]]; then
    echo ""
    echo "[Step 2/5] Running test generation..."
    RUNNER_ARGS=(
        --api-key "$API_KEY"
        --model "$MODEL"
        --runs "$RUNS"
        --phases "$PHASES"
        --output-dir "$OUTPUT_DIR"
        --test-project-dir "$TEST_PROJECT_DIR"
    )
    if [[ -n "$SOURCE_DIR" ]]; then
        RUNNER_ARGS+=("--source-dir" "$SOURCE_DIR")
    fi
    if [[ -n "$SKIP_INFERENCE" ]]; then
        RUNNER_ARGS+=("$SKIP_INFERENCE")
    fi

    java -cp "$JAR_FILE" com.jml.inferrer.experiment.ExperimentRunner "${RUNNER_ARGS[@]}"
    echo "  Test generation complete."
else
    echo ""
    echo "[Step 2/5] Skipping test generation (--skip-generation)."
fi

# --------------- Step 3: Compile and Run Tests ---------------
if [[ -z "$SKIP_TESTS" ]]; then
    echo ""
    echo "[Step 3/5] Compiling and running generated tests..."
    cd "$TEST_PROJECT_DIR"

    # Run Maven test (captures both compilation and execution results)
    mvn test -fae 2>&1 | tee "$OUTPUT_DIR/maven-test-output.txt" || true

    # Parse surefire reports
    echo "  Parsing test results..."
    SUREFIRE_DIR="$TEST_PROJECT_DIR/target/surefire-reports"
    if [[ -d "$SUREFIRE_DIR" ]]; then
        # Count test results from surefire XML reports
        TOTAL_TESTS=0
        TOTAL_FAILURES=0
        TOTAL_ERRORS=0
        TOTAL_SKIPPED=0
        COMPILE_FAILURES=0

        for xml_file in "$SUREFIRE_DIR"/TEST-*.xml; do
            if [[ -f "$xml_file" ]]; then
                tests=$(grep -oP 'tests="\K[0-9]+' "$xml_file" | head -1)
                failures=$(grep -oP 'failures="\K[0-9]+' "$xml_file" | head -1)
                errors=$(grep -oP 'errors="\K[0-9]+' "$xml_file" | head -1)
                skipped=$(grep -oP 'skipped="\K[0-9]+' "$xml_file" | head -1)

                TOTAL_TESTS=$((TOTAL_TESTS + ${tests:-0}))
                TOTAL_FAILURES=$((TOTAL_FAILURES + ${failures:-0}))
                TOTAL_ERRORS=$((TOTAL_ERRORS + ${errors:-0}))
                TOTAL_SKIPPED=$((TOTAL_SKIPPED + ${skipped:-0}))
            fi
        done

        # Count compilation failures from Maven output
        COMPILE_FAILURES=$(grep -c "COMPILATION ERROR" "$OUTPUT_DIR/maven-test-output.txt" 2>/dev/null || echo "0")

        PASSED=$((TOTAL_TESTS - TOTAL_FAILURES - TOTAL_ERRORS - TOTAL_SKIPPED))
        if [[ $TOTAL_TESTS -gt 0 ]]; then
            PASS_RATE=$(echo "scale=1; $PASSED * 100 / $TOTAL_TESTS" | bc 2>/dev/null || echo "N/A")
        else
            PASS_RATE="N/A"
        fi

        echo "  Total tests: $TOTAL_TESTS"
        echo "  Passed: $PASSED"
        echo "  Failures: $TOTAL_FAILURES"
        echo "  Errors: $TOTAL_ERRORS"
        echo "  Pass rate: $PASS_RATE%"

        # Save compilation/test metrics JSON
        cat > "$OUTPUT_DIR/metrics/test-metrics.json" << METRICSEOF
{
    "totalTests": $TOTAL_TESTS,
    "passed": $PASSED,
    "failures": $TOTAL_FAILURES,
    "errors": $TOTAL_ERRORS,
    "skipped": $TOTAL_SKIPPED,
    "compileFailures": $COMPILE_FAILURES,
    "passRate": "$PASS_RATE"
}
METRICSEOF

    else
        echo "  WARNING: No surefire reports found."
    fi
    cd "$PROJECT_DIR"
else
    echo ""
    echo "[Step 3/5] Skipping test execution (--skip-tests)."
fi

# --------------- Step 4: PiTest Mutation Testing ---------------
if [[ -z "$SKIP_PITEST" ]]; then
    echo ""
    echo "[Step 4/5] Running PiTest mutation testing..."
    cd "$TEST_PROJECT_DIR"

    # Run PiTest
    mvn pitest:mutationCoverage 2>&1 | tee "$OUTPUT_DIR/pitest-output.txt" || true

    # Parse PiTest CSV results
    PITEST_DIR="$TEST_PROJECT_DIR/target/pit-reports"
    if [[ -d "$PITEST_DIR" ]]; then
        CSV_FILE=$(find "$PITEST_DIR" -name "mutations.csv" | head -1)
        if [[ -n "$CSV_FILE" && -f "$CSV_FILE" ]]; then
            TOTAL_MUTATIONS=$(wc -l < "$CSV_FILE")
            TOTAL_MUTATIONS=$((TOTAL_MUTATIONS - 1))  # Subtract header
            KILLED=$(grep -c "KILLED" "$CSV_FILE" 2>/dev/null || echo "0")
            SURVIVED=$(grep -c "SURVIVED" "$CSV_FILE" 2>/dev/null || echo "0")
            NO_COVERAGE=$(grep -c "NO_COVERAGE" "$CSV_FILE" 2>/dev/null || echo "0")

            if [[ $((KILLED + SURVIVED)) -gt 0 ]]; then
                MUTATION_SCORE=$(echo "scale=1; $KILLED * 100 / ($KILLED + $SURVIVED)" | bc 2>/dev/null || echo "N/A")
            else
                MUTATION_SCORE="N/A"
            fi

            echo "  Total mutations: $TOTAL_MUTATIONS"
            echo "  Killed: $KILLED"
            echo "  Survived: $SURVIVED"
            echo "  No coverage: $NO_COVERAGE"
            echo "  Mutation score: $MUTATION_SCORE%"

            # Save mutation metrics JSON
            cat > "$OUTPUT_DIR/metrics/mutation-metrics.json" << MUTEOF
{
    "totalMutations": $TOTAL_MUTATIONS,
    "killed": $KILLED,
    "survived": $SURVIVED,
    "noCoverage": $NO_COVERAGE,
    "mutationScore": "$MUTATION_SCORE"
}
MUTEOF
        else
            echo "  WARNING: No PiTest CSV report found."
        fi
    else
        echo "  WARNING: No PiTest reports directory found."
    fi
    cd "$PROJECT_DIR"
else
    echo ""
    echo "[Step 4/5] Skipping PiTest (--skip-pitest)."
fi

# --------------- Step 5: Generate Summary Report ---------------
echo ""
echo "[Step 5/5] Generating summary report..."

REPORT_FILE="$OUTPUT_DIR/report.txt"
cat > "$REPORT_FILE" << 'HEADER'
========================================================================
  JML-Inferrer Experiment Results
  LLM-Based Test Generation with Formal Specifications
========================================================================

HEADER

echo "Date: $(date)" >> "$REPORT_FILE"
echo "Model: $MODEL" >> "$REPORT_FILE"
echo "Runs per configuration: $RUNS" >> "$REPORT_FILE"
echo "Phases: $PHASES" >> "$REPORT_FILE"
echo "" >> "$REPORT_FILE"

# Append generation metrics
if [[ -f "$OUTPUT_DIR/metrics/generation-metrics.json" ]]; then
    echo "--- Generation Metrics ---" >> "$REPORT_FILE"
    echo "(See metrics/generation-metrics.json for details)" >> "$REPORT_FILE"
    echo "" >> "$REPORT_FILE"
fi

# Append test metrics
if [[ -f "$OUTPUT_DIR/metrics/test-metrics.json" ]]; then
    echo "--- Test Execution Metrics ---" >> "$REPORT_FILE"
    cat "$OUTPUT_DIR/metrics/test-metrics.json" >> "$REPORT_FILE"
    echo "" >> "$REPORT_FILE"
fi

# Append mutation metrics
if [[ -f "$OUTPUT_DIR/metrics/mutation-metrics.json" ]]; then
    echo "--- Mutation Testing Metrics ---" >> "$REPORT_FILE"
    cat "$OUTPUT_DIR/metrics/mutation-metrics.json" >> "$REPORT_FILE"
    echo "" >> "$REPORT_FILE"
fi

echo "========================================================================" >> "$REPORT_FILE"
echo "Report saved to: $REPORT_FILE"

echo ""
echo "============================================"
echo "  Experiment Complete!"
echo "============================================"
echo "Results directory: $OUTPUT_DIR"
echo "Report: $REPORT_FILE"
echo ""
echo "Key output files:"
echo "  $OUTPUT_DIR/metrics/generation-metrics.json"
echo "  $OUTPUT_DIR/metrics/test-metrics.json"
echo "  $OUTPUT_DIR/metrics/mutation-metrics.json"
echo "  $OUTPUT_DIR/report.txt"
echo "============================================"
