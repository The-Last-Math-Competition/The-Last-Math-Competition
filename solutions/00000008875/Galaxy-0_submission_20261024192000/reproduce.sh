#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake build
lake env lean --error=warning Main.lean
lake env leanchecker Main
