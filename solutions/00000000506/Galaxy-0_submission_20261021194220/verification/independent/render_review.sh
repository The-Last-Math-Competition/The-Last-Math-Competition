#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PACKAGE="$(cd "${1:-$HERE/../..}" && pwd)"
mkdir -p "$HERE/render"
pdftoppm -r 130 -png "$PACKAGE/solution.pdf" "$HERE/render/page"
pdftotext -layout "$PACKAGE/solution.pdf" "$HERE/pdf-text.txt"
pdfinfo "$PACKAGE/solution.pdf" > "$HERE/pdfinfo.txt"
(cd "$HERE" && sha256sum render/*.png) > "$HERE/render-SHA256SUMS"
