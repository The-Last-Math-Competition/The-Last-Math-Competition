#!/usr/bin/env bash
set -euo pipefail
mkdir -p build-logs
lake build 2>&1 | tee build-logs/lake-build.log
for source in Conjecture2821/Basic.lean Conjecture2821/Limits.lean Conjecture2821/LDP.lean Conjecture2821.lean; do
  name="${source//\//-}"
  lake env lean -DwarningAsError=true "$source" 2>&1 | tee "build-logs/${name}.log"
done
