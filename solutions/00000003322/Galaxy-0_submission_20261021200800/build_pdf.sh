#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export TEXMFVAR="${TMPDIR:-/tmp}/tlmc3322-texmf-var"
export TEXMFCONFIG="${TMPDIR:-/tmp}/tlmc3322-texmf-config"
if [ -n "${TLMC_TEXFORMATS:-}" ]; then
  export TEXFORMATS="$TLMC_TEXFORMATS:"
fi
export TEXINPUTS=.:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:
export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:
export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:
export ENCFONTS=/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:
export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:
export SOURCE_DATE_EPOCH=1792540800
mkdir -p "$TEXMFVAR" "$TEXMFCONFIG"
pdflatex -output-format=pdf -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -output-format=pdf -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex
