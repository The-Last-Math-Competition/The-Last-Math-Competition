#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [ $# -ge 1 ]; then export PATH="$1:$PATH"; fi
mkdir -p verification
lean --version > verification/toolchain.log
# Remove only generated build products from this submission, never source files.
if [ -d .lake/build ]; then rm -rf .lake/build; fi
lake build > verification/lake-build.log 2>&1
lake env lean -DwarningAsError=true Main.lean > verification/lean-build.log 2>&1
lake env leanchecker Main > verification/kernel-check.log 2>&1
python3 verification/recurrence_check.py > verification/python-recurrence.log
python3 verification/independent_r_check.py > verification/python-independent.log
sha256sum Main.lean solution.tex solution.pdf > verification/SHA256SUMS
