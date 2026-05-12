#!/bin/sh
# Log everything sent to z3 (stdin), copy unchanged to actual z3.
LOG=/tmp/z3-stdin.log
> $LOG
tee -a $LOG | /opt/openjml/Solvers-linux/z3-4.13.4 "$@"
