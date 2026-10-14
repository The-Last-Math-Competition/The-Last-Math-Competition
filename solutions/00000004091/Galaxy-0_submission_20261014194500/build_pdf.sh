#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$(mktemp -d /tmp/tlmc4091-pdf.XXXXXX)}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
# Optional second argument: prebuilt pdflatex.fmt directory on minimal images.
# Ordinary TeX installations do not need this branch.
if [ -n "${2:-}" ]; then
  export TEXFORMATS="$2:"
  export TEXINPUTS=/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//:
  export TFMFONTS=/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:
  export T1FONTS=/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:
  export TEXFONTMAPS=/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:
  export ENCFONTS=/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:
  export TEXMFVAR="$out/tex-var"
  export TEXMFCONFIG="$out/tex-config"
fi
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error -output-directory="$out" "$here/solution.tex" > "$out/latex-build.log" 2>&1
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error -output-directory="$out" "$here/solution.tex" >> "$out/latex-build.log" 2>&1
if grep -E 'Overfull|undefined references|Citation .* undefined' "$out/solution.log"; then
  echo 'PDF quality check requires review' >&2
  exit 1
fi
pdfinfo "$out/solution.pdf" > "$out/pdfinfo.txt"
printf 'PASS: compiled twice with no overfull boxes or undefined references\n'
printf 'PDF: %s/solution.pdf\n' "$out"
