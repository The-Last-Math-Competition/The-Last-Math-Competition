#!/usr/bin/env bash
# Independent verification, using only source/configuration copied from the package.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PACKAGE="$(cd "${1:-$HERE/../..}" && pwd)"
if [[ -n "${LEAN_BIN_DIR:-}" ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
WORK="$(mktemp -d "${TMPDIR:-/tmp}/tlmc506-review.XXXXXXXX")"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$HERE/logs"
cp "$PACKAGE"/*.lean "$PACKAGE/lean-toolchain" "$PACKAGE/lakefile.toml" "$WORK/"
cp "$HERE/ReviewContract.lean" "$WORK/"
MODULES=(PolynomialCore RawPolynomial PolynomialRing Syzygy PolynomialRingExtras BettiSupport MinimalPresentation SyzygyQuotient PolynomialGrading Resolution Main)
FILES=()
for m in "${MODULES[@]}"; do FILES+=("$m.lean"); done
python3 "$HERE/make_audit.py" "$WORK" "${FILES[@]}" > "$HERE/logs/declaration-audit-generation.log"
(
  cd "$WORK"
  lean --version
  export LEAN_PATH=.
  for m in "${MODULES[@]}"; do
    printf '\nSTRICT SOURCE COMPILE: %s\n' "$m"
    lean -j1 -DwarningAsError=true -o "$m.olean" "$m.lean"
  done
  printf '\nSTRICT SOURCE BUILD PASS\n'
) > "$HERE/logs/strict-source-build.log" 2>&1
(
  cd "$WORK"
  export LEAN_PATH=.
  lean -j1 -DwarningAsError=true ReviewAxioms.lean
) > "$HERE/logs/named-declarations-axioms.log" 2>&1
(
  cd "$WORK"
  export LEAN_PATH=.
  lean -j1 -DwarningAsError=true -o ReviewContract.olean ReviewContract.lean
  lean -j1 -DwarningAsError=true Audit.lean
) > "$HERE/logs/contracts-and-all-theorem-audit.log" 2>&1
(
  cd "$WORK"
  export LEAN_PATH=.
  for m in "${MODULES[@]}" ReviewContract; do
    printf 'KERNEL REPLAY: %s\n' "$m"
    leanchecker "$m"
    printf 'PASS: %s\n' "$m"
  done
) > "$HERE/logs/kernel-replay.log" 2>&1
(
  cd "$WORK"
  unset LEAN_PATH
  lake build Main Audit
) > "$HERE/logs/fresh-lake-build.log" 2>&1
cp "$WORK/ReviewAxioms.lean" "$HERE/ReviewAxioms.lean"
cp "$WORK/review-declarations.json" "$HERE/review-declarations.json"
python3 "$HERE/check_graded_pieces.py" > "$HERE/graded-pieces-result.json"
python3 "$PACKAGE/reproduce.py" > "$HERE/logs/author-reproduction.json"
python3 "$HERE/check_source_tokens.py" "$PACKAGE" > "$HERE/logs/source-token-scan.log"
python3 - "$HERE" <<'PY'
import pathlib,re,sys
root=pathlib.Path(sys.argv[1])
allowed={'propext','Classical.choice','Quot.sound'}
text=(root/'logs/named-declarations-axioms.log').read_text()
for match in re.finditer(r'depends on axioms: \[([^]]*)\]',text):
    actual={x.strip() for x in match.group(1).split(',') if x.strip()}
    assert actual <= allowed, actual
assert 'sorryAx' not in text and 'ofReduceBool' not in text
assert 'PASS: audited all' in (root/'logs/contracts-and-all-theorem-audit.log').read_text()
print('PASS: named-declaration and environment-wide theorem axiom audits.')
PY
printf 'PASS: source-only strict build, theorem contracts, both axiom audits, all-module kernel replay, fresh Lake build, and both finite diagnostics.\n'
