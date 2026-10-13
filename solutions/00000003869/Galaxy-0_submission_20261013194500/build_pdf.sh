#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [ "${1:-}" != "" ]; then
 export TEXFORMATS="$1:"
 export TEXINPUTS=/usr/share/texlive/texmf-dist/tex//:
 export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:
 export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:
 export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:
 export TEXMFVAR="$(pwd)/.tex-cache"
fi
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error main.tex > verification/pdf-build.log 2>&1
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error main.tex >> verification/pdf-build.log 2>&1
