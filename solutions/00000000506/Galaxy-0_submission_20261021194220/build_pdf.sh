#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -d ../tlmc20261008/reports ]]; then
  export TEXFORMATS="$(cd ../tlmc20261008/reports && pwd):"
fi
export TEXINPUTS=.:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:
export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:
export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:
export ENCFONTS=/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:
export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:
export TEXMFVAR=/tmp/tlmc506-texmfvar
export TEXMFCONFIG=/tmp/tlmc506-texmfconfig
mkdir -p render verification
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex > verification/latex-build.log
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex >> verification/latex-build.log
pdftoppm -r 120 -png solution.pdf render/page
pdfinfo solution.pdf > verification/pdfinfo.txt
