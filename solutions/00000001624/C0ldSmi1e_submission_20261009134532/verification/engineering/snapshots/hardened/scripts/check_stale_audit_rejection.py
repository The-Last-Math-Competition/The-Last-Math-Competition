#!/usr/bin/env python3
"""Integration challenge: a no-op audit must not be allowed to reuse a stale PASS."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--stdlib-root', type=Path, required=True)
    args = parser.parse_args()
    fixture = ROOT / '.verification-fixtures' / 'stale-audit'
    if fixture.exists():
        if fixture.is_symlink() or fixture.resolve() != fixture:
            raise RuntimeError('Refusing to remove a symlinked fixture')
        shutil.rmtree(fixture)
    fixture.mkdir(parents=True)
    (fixture / 'scripts').mkdir()
    (fixture / 'records').mkdir()
    for name in ['Conjecture1624.lean', 'Verification.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
        shutil.copy2(ROOT / name, fixture / name)
    shutil.copytree(ROOT / 'source', fixture / 'source')
    shutil.copy2(ROOT / 'scripts/replay.py', fixture / 'scripts/replay.py')
    # The mutated audit compiles successfully but generates no report.
    (fixture / 'Audit.lean').write_text('import Conjecture1624\nimport Verification\n')
    shutil.copy2(ROOT / 'records/dependency-audit.json', fixture / 'records/dependency-audit.json')
    stale_status = json.loads((fixture / 'records/dependency-audit.json').read_text())['status']
    if stale_status != 'PASS': raise RuntimeError('The stale seed is not a PASS record')
    command = [sys.executable, str(fixture / 'scripts/replay.py'), '--lean-bin', str(args.lean_bin), '--stdlib-root', str(args.stdlib_root)]
    done = subprocess.run(command, cwd=fixture, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / 'records/stale-audit-negative-test.log').write_text(done.stdout)
    result = json.loads((fixture / 'records/replay-result.json').read_text())
    expected = 'Audit did not create a new regular dependency report'
    passed = done.returncode != 0 and result['status'] == 'FAIL' and result.get('error') == expected
    # Require the no-op Lean invocation itself to succeed; rejection must be due to absent fresh evidence.
    audit_cmd = next((x for x in result['commands'] if x['label'] == 'audit'), None)
    passed = passed and audit_cmd is not None and audit_cmd['returncode'] == 0
    report = {'challenge': 'Successful no-op audit with a preexisting stale PASS report',
              'status': 'PASS' if passed else 'FAIL', 'stale_seed_status': stale_status,
              'replay_exit_code': done.returncode, 'replay_status': result['status'],
              'expected_rejection': expected, 'actual_rejection': result.get('error'),
              'audit_invocation_exit_code': audit_cmd['returncode'] if audit_cmd else None,
              'stale_report_remaining': (fixture / 'records/dependency-audit.json').exists()}
    (ROOT / 'records/stale-audit-negative-test.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if not passed: raise RuntimeError('Stale-audit rejection challenge failed')


if __name__ == '__main__': main()
