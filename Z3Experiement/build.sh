#!/usr/bin/env bash
# Build + test runner for environments without Maven.
set -e
cd "$(dirname "$0")"
mkdir -p out
find src/main/java -name "*.java" > sources.txt
javac --release 21 -d out @sources.txt
find src/test/java -name "*.java" > tests.txt
javac --release 21 -cp out -d out @tests.txt
java -cp out com.z3x.TestHarness
