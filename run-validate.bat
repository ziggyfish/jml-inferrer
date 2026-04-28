@echo off
REM Build the project and run inference + OpenJML validation on sample code.
REM
REM Default mode runs locally and uses whatever OpenJML the inferrer's
REM OpenJMLInstaller can find (OPENJML_HOME env var, or the auto-installed
REM OpenJML 21-0.23 vanilla download). Many inferred specs will not discharge
REM under vanilla — the fork in openjml-dev\ adds the patches needed.
REM
REM Usage:
REM   run-validate.bat              Local run with OPENJML_HOME or auto-install
REM   run-validate.bat --use-fork   Run inside Docker against the patched fork

if /I "%~1"=="--use-fork" goto fork_mode
if /I "%~1"=="--help" goto help_mode
if /I "%~1"=="-h"     goto help_mode

echo Building JML Inferrer...
call mvn clean package -q

if %ERRORLEVEL% neq 0 (
    echo Build failed!
    exit /b 1
)

echo Running inference and validation on sample code (local OpenJML)...
echo   (Pass --use-fork to run against the patched OpenJML in openjml-dev\)
java -jar target\jml-inferrer-1.0.0-jar-with-dependencies.jar experiment\sample_code --validate
exit /b %ERRORLEVEL%

:fork_mode
echo Validating against the patched OpenJML fork (Docker)...

docker image inspect openjml-fork-build:latest >nul 2>&1
if %ERRORLEVEL% neq 0 (
    if not exist openjml-dev\ (
        echo ERROR: openjml-dev\ not found and openjml-fork-build:latest not built.
        exit /b 1
    )
    echo Building fork image (~10-15 minutes first time)...
    docker build -f openjml-dev\Dockerfile.build -t openjml-fork-build:latest openjml-dev\
    if %ERRORLEVEL% neq 0 (
        echo Fork image build failed.
        exit /b 1
    )
)

docker compose build test
docker compose run --rm test sh -c "mvn -q clean package && java -jar target/jml-inferrer-1.0.0-jar-with-dependencies.jar experiment/sample_code --validate"
exit /b %ERRORLEVEL%

:help_mode
echo Usage: %~n0 [--use-fork]
echo.
echo Default mode runs locally with whatever OpenJML the inferrer can find.
echo --use-fork runs inside Docker against the patched OpenJML in openjml-dev\.
exit /b 0
