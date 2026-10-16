#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -n "${1:-}" ]]; then export PATH="$1:$PATH"; fi
mkdir -p logs
lean --version | tee logs/toolchain.log
lake build 2>&1 | tee logs/build.log
for m in Algebra Geometry Main; do
  lake env leanchecker "$m" > "logs/kernel-$m.log" 2>&1
  echo "$m: independent kernel replay PASS" | tee -a "logs/kernel-$m.log"
done
lake env lean Audit.lean | tee logs/axioms.log
if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' logs/axioms.log; then exit 1; fi
python3 verify.py | tee logs/independent.log
