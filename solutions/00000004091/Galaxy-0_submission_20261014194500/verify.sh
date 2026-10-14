#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$(mktemp -d /tmp/tlmc4091-verify.XXXXXX)}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
if [ -e "$out/lean" ]; then
  echo "Refusing to reuse an existing build directory: $out/lean" >&2
  exit 2
fi
cp -R "$here/lean" "$out/lean"
cd "$out/lean"
lean --version > "$out/toolchain.txt"
lake build > "$out/clean-build.log" 2>&1
lake env lean -DwarningAsError=true Conjecture4091/Basic.lean > "$out/strict-elaboration.log" 2>&1
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Audit.olean Audit.lean > "$out/axiom-audit.log" 2>&1
for mod in Conjecture4091.Basic Conjecture4091 Audit; do
  printf 'Checking %s\n' "$mod" >> "$out/kernel-replay.log"
  lake env leanchecker "$mod" >> "$out/kernel-replay.log" 2>&1
  printf 'PASS: %s (exit 0)\n' "$mod" >> "$out/kernel-replay.log"
done
if grep -nE '\b(sorry|admit|axiom|native_decide|unsafe)\b' Conjecture4091/Basic.lean Conjecture4091.lean Audit.lean > "$out/forbidden-token-scan.log"; then
  echo 'Unexpected forbidden token in Lean source' >&2
  exit 1
fi
printf 'PASS: no admissions, custom axiom declarations, native_decide, or unsafe declarations\n' > "$out/forbidden-token-scan.log"
python3 "$here/empirical.py" > "$out/empirical-results.json"
python3 "$here/review/independent.py" > "$out/independent-computation.log"
python3 - "$here" "$out" <<'PY'
from pathlib import Path
import ast,json,sys
source,out=map(Path,sys.argv[1:])
for p in [source/'empirical.py',source/'review/independent.py']:
    ast.parse(p.read_text(), filename=str(p))
r=json.loads((out/'empirical-results.json').read_text())
assert r['total_graphs_checked']==1099
assert r['witnesses']['K2']['kernel_dimension_over_Q']==0
assert r['witnesses']['C4']['kernel_dimension_over_Q']==1
assert r['witnesses']['K2']['chromatic_number_exhaustive']==2
assert r['witnesses']['C4']['chromatic_number_exhaustive']==2
assert r['connected_graph_first_Betti_values_by_chromatic_number']['2']==[0,1,2]
print('PASS: source parse and exact empirical assertions')
PY
printf 'PASS: clean Lean build, strict elaboration, axiom audit, all three kernel replays, exact computations\n' | tee "$out/result.txt"
printf 'Evidence directory: %s\n' "$out"
