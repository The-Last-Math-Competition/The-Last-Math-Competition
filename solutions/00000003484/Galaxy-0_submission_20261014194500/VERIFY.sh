#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake --version
lake clean
lake build
lake env lean -DwarningAsError=true Main.lean
lake env lean -DwarningAsError=true Axioms.lean
if command -v leanchecker >/dev/null 2>&1; then
  lake env leanchecker Main
else
  echo 'leanchecker not installed; independent kernel replay was not run in this invocation.' >&2
fi
if grep -nE '(^|[[:space:]])(sorry|admit|axiom|native_decide|unsafe)([[:space:]]|$)' Main.lean; then
  echo 'Forbidden declaration or tactic token detected.' >&2
  exit 1
fi
