#!/bin/sh
set -eu
cd "$(dirname "$0")"
(cd lean && lake build && lake env lean -DwarningAsError=true IntegralCG.lean)
pdflatex -interaction=nonstopmode -halt-on-error proof.tex
pdflatex -interaction=nonstopmode -halt-on-error proof.tex
