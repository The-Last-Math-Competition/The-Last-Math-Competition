#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build Main Audit
lake env lean -DwarningAsError=true Main.lean
lake env lean Audit.lean
lake env leanchecker Main
printf 'All Lean verification commands passed.\n'
