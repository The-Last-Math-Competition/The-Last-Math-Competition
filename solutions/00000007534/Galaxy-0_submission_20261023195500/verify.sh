#!/usr/bin/env bash
set -euo pipefail
# Requires an existing Lean 4.31.0 toolchain and Python 3 on PATH.
# No dependency download, installation, network access, or native proof computation.
source_dir="$(cd "$(dirname "$0")" && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/tlmc7534-clean.XXXXXXXX")"
trap 'rm -rf "$work"' EXIT
cp "$source_dir"/{Counterexample.lean,Audit.lean,lakefile.lean,lean-toolchain,check_finite_model.py} "$work/"
cd "$work"
lean --version
lean -DwarningAsError=true Counterexample.lean
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker Counterexample
python3 check_finite_model.py
printf 'PASS: clean source-only build, strict compilation, complete axiom audit, kernel replay, finite model check.\n'
