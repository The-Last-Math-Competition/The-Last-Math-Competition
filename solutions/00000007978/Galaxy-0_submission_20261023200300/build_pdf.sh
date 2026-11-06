#!/usr/bin/env bash
set -eu
# Standard installations can simply run pdflatex twice.
# This cloud image has TeX sources/fonts but no prebuilt format or search index.
cd "$(dirname "$0")"
# Ordinary indexed TeX installations need no environment workarounds.
if kpsewhich article.cls >/dev/null 2>&1 && kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  pdflatex -interaction=nonstopmode -halt-on-error solution.tex > latex-build.log 2>&1
  pdflatex -interaction=nonstopmode -halt-on-error solution.tex >> latex-build.log 2>&1
  exit 0
fi
# Regenerate the font map from installed distributions; no fonts are bundled.
cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map > pdftex.map
if [ ! -f /tmp/tlmc-tex/pdflatex.fmt ]; then
  mkdir -p /tmp/tlmc-tex
  (cd /tmp/tlmc-tex && \
    TEXINPUTS=/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//: \
    TFMFONTS=/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//: \
    TEXMFVAR=/tmp/tlmc-tex-var \
    pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex \
      '\pdfoutput=1 \input latex.ltx' > format-build.log 2>&1)
fi
export TEXINPUTS=/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//:
export TFMFONTS=/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:
export T1FONTS=/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:
export TEXFONTMAPS=.:/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:
export ENCFONTS=/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:
export TEXFORMATS=/tmp/tlmc-tex:
export TEXMFVAR=/tmp/tlmc-tex-var
pdflatex -interaction=nonstopmode -halt-on-error solution.tex > latex-build.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error solution.tex >> latex-build.log 2>&1
