#!/usr/bin/env bash
set -euo pipefail
FINAL="$(cd "$(dirname "$0")/../.." && pwd)"
TOOLCHAIN=/workspace/scratch/76cdbd0d1d68/tlmc20261008/toolchain/bin
export PATH="$TOOLCHAIN:$PATH"
OUT="$FINAL/verification/independent-final"
mkdir -p "$OUT"
CHECK=$(mktemp -d /tmp/tlmc8872-independent.XXXXXX)
printf '%s\n' "$CHECK" > "$OUT/build-directory.txt"
cp "$FINAL"/lean/*.lean "$FINAL"/lean/lean-toolchain "$CHECK"/
(
  cd "$CHECK"
  sha256sum *.lean lean-toolchain > "$OUT/source-sha256.txt"
  lean --version
  lake --version
  printf '\nSOURCE-ONLY START: no .olean or .lake copied.\n'
  find . -maxdepth 2 -type f | sort
  lake build
) > "$OUT/clean-build.log" 2>&1
(
  cd "$CHECK"
  for m in Core NumberParts Sums Toggle Stabilization StarHeap OutcomeBridge Main; do
    printf '\n=== %s: warnings as errors ===\n' "$m"
    lake env lean -DwarningAsError=true "$m.lean"
  done
) > "$OUT/warnings-as-errors.log" 2>&1
python3 - "$CHECK" "$OUT" <<'PY'
import re, pathlib, sys
p=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2])
modules=['Core','NumberParts','Sums','Toggle','Stabilization','StarHeap','OutcomeBridge','Main']
names=[]
for module in modules:
    source=(p/(module+'.lean')).read_text()
    for m in re.finditer(r'^(?:@\[[^\n]*\]\s+)?(?:def|theorem|inductive)\s+([A-Za-z_][A-Za-z_0-9]*)',source,re.M):
        names.append(m.group(1))
text='import Main\n\n'+''.join('#print axioms TLMC8872.'+name+'\n' for name in names)
(p/'IndependentAxiomAudit.lean').write_text(text)
(out/'IndependentAxiomAudit.lean').write_text(text)
(out/'audit-count.txt').write_text(str(len(names))+' named project declarations audited\n')
PY
(
  cd "$CHECK"
  lake env lean -DwarningAsError=true IndependentAxiomAudit.lean
) > "$OUT/all-axioms.log" 2>&1
(
  cd "$CHECK"
  lake env leanchecker -v Core NumberParts Sums Toggle Stabilization StarHeap OutcomeBridge Main
) > "$OUT/leanchecker.log" 2>&1
(
  cd "$CHECK"
  lake env leanchecker --fresh -v Main
) > "$OUT/leanchecker-fresh.log" 2>&1
printf 'ALL INDEPENDENT BUILD AND AUDIT COMMANDS PASSED\n' | tee "$OUT/result.txt"
