#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build +Basic
# Keep peak memory bounded by compiling certificate modules serially.
for i in $(seq -w 0 19); do lake build "+Cert$i"; done
lake build
