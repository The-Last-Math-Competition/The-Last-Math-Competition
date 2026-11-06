#!/usr/bin/env bash
set -eu
# Standard installations can simply run pdflatex twice.
# This cloud image has TeX sources/fonts but no prebuilt format or search index.
cd "$(dirname "$0")"
if [ ! -f /tmp/tlmc-tex/pdflatex.fmt ]; then
  mkdir -p /tmp/tlmc-tex
  (cd /tmp/tlmc-tex && \
    TEXINPUTS=/usr/share/texlive/texmf-dist/tex//: \
    TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//: \
    TEXMFVAR=/tmp/tlmc-tex-var \
    pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex \
      '\pdfoutput=1 \input latex.ltx' > format-build.log 2>&1)
fi
export TEXINPUTS=/usr/share/texlive/texmf-dist/tex//:
export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:
export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:
export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:
export TEXFORMATS=/tmp/tlmc-tex:
export TEXMFVAR=/tmp/tlmc-tex-var
pdflatex -interaction=nonstopmode -halt-on-error solution.tex > latex-build.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error solution.tex >> latex-build.log 2>&1
