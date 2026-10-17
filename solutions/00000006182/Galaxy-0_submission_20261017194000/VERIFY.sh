#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake build Main Audit
lake env lean -DwarningAsError=true Main.lean
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker Main
lake env leanchecker Audit
python3 verification/independent.py
printf 'All checks passed.\n'
