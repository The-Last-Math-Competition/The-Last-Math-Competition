#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake build
lean -DwarningAsError=true --trust=0 Main.lean
lake env leanchecker Main
