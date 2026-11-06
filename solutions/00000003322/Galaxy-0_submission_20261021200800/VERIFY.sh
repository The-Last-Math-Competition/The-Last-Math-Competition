#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
if [[ -n "${LEAN_BIN_DIR:-}" ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
unset LEAN_PATH
mkdir -p "$ROOT/verification"
CLEAN="$(mktemp -d "${TMPDIR:-/tmp}/tlmc3322-clean.XXXXXXXX")"
trap 'rm -rf "$CLEAN"' EXIT
cp "$ROOT"/*.lean "$ROOT/lean-toolchain" "$ROOT/lakefile.toml" "$CLEAN/"
python3 "$ROOT/verify.py"
(
 cd "$CLEAN"
 lean --version | tee lean-version.txt
 grep -q 'version 4.31.0' lean-version.txt
 lake build Main Audit OriginAudit
 python3 - "$ROOT/theorem-manifest.json" <<'PY'
import json,subprocess,sys
for m in json.load(open(sys.argv[1]))['modules']:
    subprocess.run(['lake','env','lean','-DwarningAsError=true',m+'.lean'],check=True)
PY
) > "$ROOT/verification/clean-build.log" 2>&1
(cd "$CLEAN" && lake env lean -DwarningAsError=true Audit.lean) > "$ROOT/verification/all-theorem-axioms.log" 2>&1
(cd "$CLEAN" && lake env lean -DwarningAsError=true OriginAudit.lean) > "$ROOT/verification/origin-theorem-axioms.log" 2>&1
python3 "$ROOT/verify.py" --audit
(
 cd "$CLEAN"
 python3 - "$ROOT/theorem-manifest.json" <<'PY'
import json,subprocess,sys
for m in json.load(open(sys.argv[1]))['modules']:
    subprocess.run(['lake','env','leanchecker',m],check=True)
    print('PASS: fresh kernel replay of '+m,flush=True)
PY
) > "$ROOT/verification/kernel-replay.log" 2>&1
printf 'PASS: clean strict build, all-theorem axiom audit, all-module kernel replay.\n'
if [[ "${BUILD_PDF:-1}" = 1 ]]; then "$ROOT/build_pdf.sh" > "$ROOT/verification/pdf-build.log" 2>&1; fi
