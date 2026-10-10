#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$ROOT/logs"
cp -R "$ROOT/lean4" "$TMP/lean4"
cd "$TMP/lean4"
lean --version | tee "$ROOT/logs/toolchain.log"
lean --version | grep -F 'version 4.31.0' >/dev/null
lake --no-cache build 2>&1 | tee "$ROOT/logs/clean-build.log"
lake env lean Check.lean 2>&1 | tee "$ROOT/logs/axioms.log"
if grep -E 'sorryAx|native_decide|ofReduceBool|Classical.choice' "$ROOT/logs/axioms.log"; then
  echo 'Unexpected axiom in audit.' >&2; exit 1
fi
python3 "$ROOT/reproduce.py" | tee "$ROOT/logs/reproduce.log"
echo 'PASS: clean Lake build, principal-theorem axiom audit, and independent exact checker.'
