#!/usr/bin/env bash
set -euo pipefail
lake build
lake env lean -DwarningAsError=true -t0 Exchangeable.lean
lake env lean -DwarningAsError=true -t0 Audit.lean
lake env leanchecker Exchangeable
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
