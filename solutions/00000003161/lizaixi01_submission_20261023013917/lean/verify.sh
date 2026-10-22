#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
