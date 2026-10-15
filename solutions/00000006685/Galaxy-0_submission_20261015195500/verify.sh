#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Optional argument: directory containing Lean 4.31.0's lean/lake/leanchecker.
if [[ -n "${1:-}" ]]; then export PATH="$1:$PATH"; fi
mkdir -p logs
lean --version | tee logs/toolchain.log
lake build 2>&1 | tee logs/build.log
for module in PowerCells NoSphere FacialBound K5Rotation Conjecture6685; do
  lake env leanchecker "$module" > "logs/kernel-$module.log" 2>&1
  printf '%s: independent kernel replay PASS\n' "$module" | tee -a "logs/kernel-$module.log"
done
lake env lean Audit.lean 2>&1 | tee logs/axioms.log
python3 verify.py | tee logs/exact-geometry.log
printf 'Build, independent kernel replay, axiom audit, and exact geometry passed.\n'
