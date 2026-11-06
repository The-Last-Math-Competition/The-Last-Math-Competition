#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$here"/{OddDegree.lean,lakefile.lean,lean-toolchain,Audit.lean,solution.tex} "$work/"
cd "$work"
lake build
lake env lean -DwarningAsError=true -t0 OddDegree.lean
lake env lean -DwarningAsError=true -t0 Audit.lean
lake env leanchecker OddDegree
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex >/dev/null
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex >/dev/null
test -s solution.pdf
printf 'Clean build, strict trust-zero, axiom audit, kernel replay, PDF rebuild passed.\n'
