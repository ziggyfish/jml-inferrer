#!/usr/bin/env bash
set -e
cd /work

DAIKON=/work/daikon/daikon.jar
CL=/work/commons-lang3.jar

echo "=== compiling driver ==="
javac -cp "$DAIKON:$CL" DaikonDriver.java

echo "=== running Chicory + Daikon over org.apache.commons.lang3 ==="
# Chicory instruments the driver + target classes, runs it, feeds the trace to
# Daikon online (--daikon), and writes DaikonDriver.inv.gz. We restrict the
# program points to the lang3 classes the driver exercises.
java -cp "$DAIKON:$CL:." daikon.Chicory \
    --daikon \
    --ppt-select-pattern='org\.apache\.commons\.lang3' \
    DaikonDriver 2>&1 | tail -5

echo "=== printing invariants ==="
java -cp "$DAIKON" daikon.PrintInvariants DaikonDriver.inv.gz \
    > /work/out/daikon-invariants.txt 2>/dev/null || \
java -cp "$DAIKON" daikon.PrintInvariants DaikonDriver.inv.gz \
    > /work/out/daikon-invariants.txt

echo "=== invariant count ==="
wc -l /work/out/daikon-invariants.txt
echo "=== sample (first 80 lines) ==="
head -80 /work/out/daikon-invariants.txt
