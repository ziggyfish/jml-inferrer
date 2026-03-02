@echo off
REM =============================================================================
REM JML Experiment Runner - Full Automation Script (Windows)
REM =============================================================================
REM Orchestrates the complete experiment pipeline:
REM   1. Build the JML-Inferrer project
REM   2. Run ExperimentRunner (JML inference + Gemini test generation)
REM   3. Compile and run generated tests (Maven surefire)
REM   4. Run PiTest mutation testing
REM   5. Generate summary report
REM =============================================================================

setlocal enabledelayedexpansion

set "SCRIPT_DIR=%~dp0"
set "PROJECT_DIR=%SCRIPT_DIR%"
set "TEST_PROJECT_DIR=%PROJECT_DIR%experiment\commons-test-project"
set "OUTPUT_DIR=%PROJECT_DIR%experiment\results"
set "JAR_FILE=%PROJECT_DIR%target\jml-inferrer-1.0.0-jar-with-dependencies.jar"

REM Defaults
set "API_KEY=%GEMINI_API_KEY%"
set "MODEL=gemini-2.0-flash"
set "RUNS=5"
set "PHASES=P1,P2,P3,P4"
set "SKIP_INFERENCE="
set "SKIP_GENERATION="
set "SKIP_TESTS="
set "SKIP_PITEST="

REM --------------- Argument Parsing ---------------
:parse_args
if "%~1"=="" goto done_args
if "%~1"=="--api-key"       (set "API_KEY=%~2" & shift & shift & goto parse_args)
if "%~1"=="--model"         (set "MODEL=%~2" & shift & shift & goto parse_args)
if "%~1"=="--runs"          (set "RUNS=%~2" & shift & shift & goto parse_args)
if "%~1"=="--phases"        (set "PHASES=%~2" & shift & shift & goto parse_args)
if "%~1"=="--output-dir"    (set "OUTPUT_DIR=%~2" & shift & shift & goto parse_args)
if "%~1"=="--skip-inference" (set "SKIP_INFERENCE=--skip-inference" & shift & goto parse_args)
if "%~1"=="--skip-generation" (set "SKIP_GENERATION=true" & shift & goto parse_args)
if "%~1"=="--skip-tests"    (set "SKIP_TESTS=true" & shift & goto parse_args)
if "%~1"=="--skip-pitest"   (set "SKIP_PITEST=true" & shift & goto parse_args)
if "%~1"=="--help"          goto show_help
shift
goto parse_args

:show_help
echo Usage: %~nx0 [options]
echo.
echo Options:
echo   --api-key KEY        Gemini API key (or set GEMINI_API_KEY env var)
echo   --model MODEL        Gemini model (default: gemini-2.0-flash)
echo   --runs N             Runs per configuration (default: 5)
echo   --phases P1,P2,...   Phases to run (default: P1,P2,P3,P4)
echo   --output-dir DIR     Output directory (default: experiment\results)
echo   --skip-inference     Skip JML inference step
echo   --skip-generation    Skip test generation (use existing tests)
echo   --skip-tests         Skip Maven test compilation/execution
echo   --skip-pitest        Skip PiTest mutation testing
echo   --help               Show this help message
exit /b 0

:done_args

REM --------------- Validation ---------------
echo ============================================
echo   JML Experiment Runner
echo ============================================

where java >nul 2>nul
if errorlevel 1 (
    echo ERROR: java not found. Please install Java 21+.
    exit /b 1
)
for /f "tokens=*" %%i in ('java -version 2^>^&1 ^| findstr /n "." ^| findstr "^1:"') do echo Java:  %%i

where mvn >nul 2>nul
if errorlevel 1 (
    echo ERROR: mvn not found. Please install Maven.
    exit /b 1
)

if "%SKIP_GENERATION%"=="" (
    if "%API_KEY%"=="" (
        echo ERROR: Gemini API key required. Use --api-key KEY or set GEMINI_API_KEY env var.
        exit /b 1
    )
)

echo Model:  %MODEL%
echo Runs:   %RUNS%
echo Phases: %PHASES%
echo Output: %OUTPUT_DIR%
echo ============================================

REM --------------- Step 1: Build Project ---------------
echo.
echo [Step 1/5] Building JML-Inferrer project...
cd /d "%PROJECT_DIR%"
call mvn clean package -q -DskipTests
if errorlevel 1 (
    echo ERROR: Build failed.
    exit /b 1
)
echo   Build successful: %JAR_FILE%

REM --------------- Step 2: Run ExperimentRunner ---------------
if "%SKIP_GENERATION%"=="" (
    echo.
    echo [Step 2/5] Running test generation...
    set "RUNNER_ARGS=--api-key %API_KEY% --model %MODEL% --runs %RUNS% --phases %PHASES% --output-dir %OUTPUT_DIR% --test-project-dir %TEST_PROJECT_DIR%"
    if not "%SKIP_INFERENCE%"=="" set "RUNNER_ARGS=!RUNNER_ARGS! %SKIP_INFERENCE%"

    java -cp "%JAR_FILE%" com.jml.inferrer.experiment.ExperimentRunner !RUNNER_ARGS!
    if errorlevel 1 (
        echo ERROR: Test generation failed.
        exit /b 1
    )
    echo   Test generation complete.
) else (
    echo.
    echo [Step 2/5] Skipping test generation --skip-generation.
)

REM --------------- Step 3: Compile and Run Tests ---------------
if "%SKIP_TESTS%"=="" (
    echo.
    echo [Step 3/5] Compiling and running generated tests...
    cd /d "%TEST_PROJECT_DIR%"
    call mvn test -fae > "%OUTPUT_DIR%\maven-test-output.txt" 2>&1

    echo   Parsing test results...
    set "SUREFIRE_DIR=%TEST_PROJECT_DIR%\target\surefire-reports"
    if exist "!SUREFIRE_DIR!" (
        set "TOTAL_TESTS=0"
        set "TOTAL_FAILURES=0"
        set "TOTAL_ERRORS=0"

        for /f "tokens=*" %%f in ('dir /b "!SUREFIRE_DIR!\TEST-*.xml" 2^>nul') do (
            for /f "tokens=2 delims=^=^"" %%t in ('findstr /r "tests=" "!SUREFIRE_DIR!\%%f"') do (
                set /a "TOTAL_TESTS+=%%t" 2>nul
            )
        )

        echo   Total tests found: !TOTAL_TESTS!

        REM Save basic metrics
        if not exist "%OUTPUT_DIR%\metrics" mkdir "%OUTPUT_DIR%\metrics"
        echo {"totalTests": !TOTAL_TESTS!} > "%OUTPUT_DIR%\metrics\test-metrics.json"
    ) else (
        echo   WARNING: No surefire reports found.
    )
    cd /d "%PROJECT_DIR%"
) else (
    echo.
    echo [Step 3/5] Skipping test execution --skip-tests.
)

REM --------------- Step 4: PiTest Mutation Testing ---------------
if "%SKIP_PITEST%"=="" (
    echo.
    echo [Step 4/5] Running PiTest mutation testing...
    cd /d "%TEST_PROJECT_DIR%"
    call mvn pitest:mutationCoverage > "%OUTPUT_DIR%\pitest-output.txt" 2>&1

    set "PITEST_DIR=%TEST_PROJECT_DIR%\target\pit-reports"
    if exist "!PITEST_DIR!" (
        echo   PiTest reports generated in !PITEST_DIR!

        REM Count mutations from CSV
        for /f %%f in ('dir /s /b "!PITEST_DIR!\mutations.csv" 2^>nul') do (
            set "CSV_FILE=%%f"
        )
        if defined CSV_FILE (
            set "KILLED=0"
            set "SURVIVED=0"
            for /f "tokens=*" %%l in ('findstr /c:"KILLED" "!CSV_FILE!" 2^>nul') do set /a "KILLED+=1"
            for /f "tokens=*" %%l in ('findstr /c:"SURVIVED" "!CSV_FILE!" 2^>nul') do set /a "SURVIVED+=1"
            echo   Killed: !KILLED!
            echo   Survived: !SURVIVED!

            if not exist "%OUTPUT_DIR%\metrics" mkdir "%OUTPUT_DIR%\metrics"
            echo {"killed": !KILLED!, "survived": !SURVIVED!} > "%OUTPUT_DIR%\metrics\mutation-metrics.json"
        )
    ) else (
        echo   WARNING: No PiTest reports found.
    )
    cd /d "%PROJECT_DIR%"
) else (
    echo.
    echo [Step 4/5] Skipping PiTest --skip-pitest.
)

REM --------------- Step 5: Generate Summary Report ---------------
echo.
echo [Step 5/5] Generating summary report...

set "REPORT_FILE=%OUTPUT_DIR%\report.txt"
if not exist "%OUTPUT_DIR%" mkdir "%OUTPUT_DIR%"

(
    echo ========================================================================
    echo   JML-Inferrer Experiment Results
    echo   LLM-Based Test Generation with Formal Specifications
    echo ========================================================================
    echo.
    echo Date: %DATE% %TIME%
    echo Model: %MODEL%
    echo Runs per configuration: %RUNS%
    echo Phases: %PHASES%
    echo.
    if exist "%OUTPUT_DIR%\metrics\generation-metrics.json" (
        echo --- Generation Metrics ---
        echo See metrics\generation-metrics.json for details
        echo.
    )
    if exist "%OUTPUT_DIR%\metrics\test-metrics.json" (
        echo --- Test Execution Metrics ---
        type "%OUTPUT_DIR%\metrics\test-metrics.json"
        echo.
    )
    if exist "%OUTPUT_DIR%\metrics\mutation-metrics.json" (
        echo --- Mutation Testing Metrics ---
        type "%OUTPUT_DIR%\metrics\mutation-metrics.json"
        echo.
    )
    echo ========================================================================
) > "%REPORT_FILE%"

echo Report saved to: %REPORT_FILE%

echo.
echo ============================================
echo   Experiment Complete!
echo ============================================
echo Results directory: %OUTPUT_DIR%
echo Report: %REPORT_FILE%
echo.
echo Key output files:
echo   %OUTPUT_DIR%\metrics\generation-metrics.json
echo   %OUTPUT_DIR%\metrics\test-metrics.json
echo   %OUTPUT_DIR%\metrics\mutation-metrics.json
echo   %OUTPUT_DIR%\report.txt
echo ============================================

endlocal
