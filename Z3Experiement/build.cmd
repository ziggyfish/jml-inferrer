@echo off
REM Build + test runner (Windows).
cd /d %~dp0
if not exist out mkdir out
dir /s /b src\main\java\*.java > sources.txt
javac --release 21 -d out @sources.txt
if errorlevel 1 exit /b 1
dir /s /b src\test\java\*.java > tests.txt
javac --release 21 -cp out -d out @tests.txt
if errorlevel 1 exit /b 1
java -cp out com.z3x.TestHarness
