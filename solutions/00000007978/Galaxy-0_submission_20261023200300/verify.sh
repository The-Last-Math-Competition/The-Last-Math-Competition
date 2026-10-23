#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Set LEAN_BIN to an existing Lean 4.31.0 toolchain bin directory.
if [[ -n "${LEAN_BIN:-}" ]]; then export PATH="$LEAN_BIN:$PATH"; fi
lean --version
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp PIR.lean Rates.lean Approx.lean Capacity.lean Coupling.lean CouplingIndexed.lean "$work/"
cd "$work"
export LEAN_PATH=.
for m in PIR Rates Approx Capacity Coupling CouplingIndexed; do
  printf '\nSTRICT BUILD %s\n' "$m"
  lean --trust=0 -DwarningAsError=true -o "$m.olean" "$m.lean"
  printf 'KERNEL REPLAY %s\n' "$m"
  leanchecker -v "$m"
done
python3 - <<'PY' > Audit.lean
import re
print('import Capacity\nimport CouplingIndexed')
for module in ['PIR','Rates','Approx','Capacity','Coupling','CouplingIndexed']:
    for name in re.findall(r'^theorem\s+(\w+)',open(module+'.lean').read(),re.M):
        print('#print axioms PIR.'+name)
PY
lean --trust=0 -DwarningAsError=true Audit.lean
