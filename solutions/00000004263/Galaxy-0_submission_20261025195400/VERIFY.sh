#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Put the pinned Lean 4.31.0 toolchain's bin directory on PATH first.
lean --version
lake build Main Audit
lake env lean --trust=0 -DwarningAsError=true Main.lean
lake env lean --trust=0 -DwarningAsError=true Audit.lean
lake env leanchecker Main
printf 'Build, warning-strict source compilation, all named theorem audits, and kernel replay passed.\n'
