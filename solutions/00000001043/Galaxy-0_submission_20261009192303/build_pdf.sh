#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p logs
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
# A normal TeX installation needs only two pdflatex runs. This fallback uses
# already installed TeX sources/fonts if its search index or format is absent.
if ! kpsewhich article.cls >/dev/null || ! kpsewhich pdflatex.fmt >/dev/null; then
  export TEXINPUTS=/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:
  export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:
  export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:
  export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:
  export TEXMFVAR="$TMP/texmf-var"
  (cd "$TMP" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
    -jobname=pdflatex '\pdfoutput=1 \input latex.ltx') > logs/latex-format-build.log 2>&1
  export TEXFORMATS="$TMP:"
fi
pdflatex -interaction=nonstopmode -halt-on-error solution.tex > logs/latex-build.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error solution.tex >> logs/latex-build.log 2>&1
