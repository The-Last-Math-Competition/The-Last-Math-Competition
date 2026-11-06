#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -n "${1:-}" ]]; then export PATH="$1:$PATH"; fi
mkdir -p logs
lean --version | tee logs/toolchain.log
lake clean
lake build 2>&1 | tee logs/build.log
lake env lean Audit.lean | tee logs/axioms.log
if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' logs/axioms.log; then exit 1; fi
lake env leanchecker Main > logs/kernel-Main.log 2>&1
printf 'Main: independent kernel replay PASS\n' | tee -a logs/kernel-Main.log
if [[ -f Square.lean ]]; then
  lake env leanchecker Square > logs/kernel-Square.log 2>&1
  printf 'Square: independent kernel replay PASS\n' | tee -a logs/kernel-Square.log
fi
lake env leanchecker Bridge > logs/kernel-Bridge.log 2>&1
printf "Bridge: independent kernel replay PASS\n" | tee -a logs/kernel-Bridge.log
