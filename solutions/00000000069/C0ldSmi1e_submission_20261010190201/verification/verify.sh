#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
lean --version
lake --version
lake build
for file in TLMC69/Kernel.lean TLMC69/Primitive.lean TLMC69/KernelIntegrals.lean TLMC69/Approximation.lean TLMC69/Main.lean TLMC69.lean verification/Axioms.lean; do
  printf '\nChecking %s with warnings as errors\n' "$file"
  lake env lean -DwarningAsError=true "$file"
done
python3 verification/check_sources.py
