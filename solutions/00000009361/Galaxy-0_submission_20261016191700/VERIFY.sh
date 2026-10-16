#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build Main Audit
for module in Permutations RecordSemantics RecordsCount Main; do
  lake env lean -DwarningAsError=true "$module.lean"
  lake env leanchecker "$module"
done
lake env lean Audit.lean
python3 verification/independent.py
printf 'All verification commands passed.\n'
