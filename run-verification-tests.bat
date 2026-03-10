@echo off
REM ===========================================================================
REM run-verification-tests.bat
REM
REM Windows wrapper for the formal verification test suite.
REM Builds a Docker image with OpenJML and runs the verification tests.
REM
REM Usage:
REM   run-verification-tests.bat              Build + run tests
REM   run-verification-tests.bat --build      Build the Docker image only
REM   run-verification-tests.bat --test-only  Run tests only
REM   run-verification-tests.bat --clean      Remove the Docker image
REM ===========================================================================

setlocal enabledelayedexpansion

set "SCRIPT_DIR=%~dp0"
set "SCRIPT_DIR=%SCRIPT_DIR:~0,-1%"

echo =============================================
echo  JML Inferrer - Formal Verification Test Suite
echo =============================================
echo.

REM Check for Git Bash
where bash >nul 2>&1
if %ERRORLEVEL% neq 0 (
    echo [ERROR] bash not found. Install Git for Windows or MSYS2.
    echo         Download: https://gitforwindows.org/
    exit /b 1
)

REM Forward to the shell script
bash "%SCRIPT_DIR%\run-verification-tests.sh" %*
exit /b %ERRORLEVEL%
