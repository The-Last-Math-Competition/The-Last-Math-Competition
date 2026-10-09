#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LAKE_BIN="${LAKE_BIN:-lake}"
mkdir -p logs
"$LAKE_BIN" build 2>&1 | tee logs/final-build.log
python3 check_inputs_and_pins.py 2>&1 | tee logs/input-and-pin-check.log
"$LAKE_BIN" env lean -DwarningAsError=true -o .lake/build/lib/lean/Solution.olean Solution.lean 2>&1 | tee logs/final-source-replay.log
"$LAKE_BIN" env lean -DwarningAsError=true Audit.lean 2>&1 | tee logs/final-audit.log
printf '%s\n' 'PASS: build, fresh mathematical-source replay, and full declaration audit'
