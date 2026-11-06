#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape solution.tex
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape solution.tex
