#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
if [[ -n "${LEAN_BIN_DIR:-}" ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
unset LEAN_PATH
mkdir -p "$ROOT/verification"
CLEAN="$(mktemp -d "${TMPDIR:-/tmp}/tlmc506-clean.XXXXXXXX")"
trap 'rm -rf "$CLEAN"' EXIT
cp "$ROOT"/*.lean "$ROOT/lean-toolchain" "$ROOT/lakefile.toml" "$CLEAN/"
(
  cd "$CLEAN"
  lean --version
  lake build Main Audit
  for f in PolynomialCore RawPolynomial PolynomialRing Syzygy PolynomialRingExtras \
      BettiSupport MinimalPresentation SyzygyQuotient PolynomialGrading Resolution Main; do
    lake env lean -DwarningAsError=true "$f.lean"
  done
) > "$ROOT/verification/clean-build.log" 2>&1
(cd "$CLEAN" && lake env lean -DwarningAsError=true Audit.lean) \
  > "$ROOT/verification/all-theorem-axioms.log" 2>&1
(cd "$CLEAN" && lake env leanchecker Main && printf 'PASS: fresh kernel replay of Main and its imports.\n') \
  > "$ROOT/verification/kernel-replay.log" 2>&1
python3 "$ROOT/reproduce.py" > "$ROOT/verification/reproduction.json"
python3 - "$ROOT" <<'PY'
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
for p in root.glob('*.lean'):
    s = p.read_text()
    # Strip comments before checking executable source tokens.
    s = re.sub(r'/\-.*?\-/', '', s, flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    s = re.sub(r'"(?:\\.|[^"\\])*"', '""', s)
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b', s), p
    assert 'ofReduceBool' not in s, p
print('PASS: authored Lean sources have no proof bypass tokens.')
PY
printf 'PASS: clean source build, strict checks, all-theorem audit, kernel replay, and Python reproduction.\n'
