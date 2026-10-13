#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
# Ordinary TeX installations need only the two pdflatex invocations below.
# Optional arguments expose existing TeX sources and a prebuilt format on minimal images.
if [ "${1:-}" != "" ]; then
 export TEXFORMATS="$1:"
 export TEXINPUTS=/usr/share/texlive/texmf-dist/tex//:
 export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:
 export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:
 export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:
 export TEXMFVAR="$(pwd)/.tex-cache"
fi
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error report.tex > pdf-build.txt 2>&1
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error report.tex >> pdf-build.txt 2>&1
