#!/usr/bin/env python3
"""Inject owned forbidden declarations into an isolated built project, then audit.

Only the explicit --work-project is mutated; it must be below this verifier's
workspace. Uses the actual unchanged Audit.lean and actual pinned Lean runtime.
The positive build must have been produced by scripts/replay.py beforehand.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument('--work-project', required=True, type=Path)
parser.add_argument('--lean-bin', required=True, type=Path)
parser.add_argument('--records', required=True, type=Path)
args = parser.parse_args()
base = Path(__file__).resolve().parents[1]
project = args.work_project.resolve()
records = args.records.resolve()
assert project.is_relative_to(base), 'Only an isolated verifier workspace may be changed'
assert records.is_relative_to(base)
records.mkdir(parents=True, exist_ok=True)
source = project / 'Verification.lean'
original = source.read_bytes()
audit_original = (project / 'Audit.lean').read_bytes()
env = dict(os.environ)
env['PATH'] = str(args.lean_bin.resolve()) + os.pathsep + env.get('PATH', '')
lake = str(args.lean_bin.resolve() / 'lake')
rows = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(command, label):
    start = time.monotonic()
    done = subprocess.run(command, cwd=project, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = records / (label + '.log')
    log.write_text(done.stdout)
    row = {'label': label, 'command': command, 'returncode': done.returncode,
           'elapsed_seconds': round(time.monotonic() - start, 3),
           'log': str(log.relative_to(base)), 'log_sha256': sha(log.read_bytes())}
    rows.append(row)
    return done


def compile_verification(label):
    done = run([lake, 'env', 'lean', '-DwarningAsError=true', '-o',
                '.lake/build/lib/lean/Verification.olean', 'Verification.lean'], label)
    if done.returncode:
        raise RuntimeError(f'Control fixture failed to compile: {label}')


controls = [
    ('axiom', '\naxiom EngineeringControl.forbidden : True\n', 'Unexpected collectAxioms result'),
    ('unsafe', '\nunsafe def EngineeringControl.unsafeRoot : True := True.intro\n', 'Dependency audit failed'),
    ('partial', '\npartial def EngineeringControl.partialRoot (n : Nat) : Nat := EngineeringControl.partialRoot n\n', 'Missing dependency: _obj'),
]
summary = {'status': 'RUNNING', 'project': str(project),
           'source_sha256': sha(original), 'audit_sha256': sha(audit_original),
           'commands': rows, 'controls': []}
try:
    for label, injection, expected_message in controls:
        source.write_bytes(original + injection.encode())
        summary['controls'].append({'name': label, 'injection': injection,
                                    'mutated_source_sha256': sha(source.read_bytes())})
        compile_verification(label + '-compile')
        report = project / 'records/dependency-audit.json'
        report.unlink(missing_ok=True)
        done = run([lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'], label + '-audit')
        if done.returncode == 0 or expected_message not in done.stdout:
            raise RuntimeError(f'{label} injection did not produce the expected actual audit rejection')
        result = summary['controls'][-1]
        result['expected_rejection_observed'] = True
        if report.exists():
            data = report.read_bytes()
            target = records / (label + '-dependency-audit.json.gz')
            target.write_bytes(gzip.compress(data, mtime=0))
            audit = json.loads(data)
            result['audit_result'] = {k: audit[k] for k in ['status', 'forbidden_axioms', 'unsafe_dependencies', 'partial_dependencies']}
            result['audit_gzip'] = str(target.relative_to(base))
            result['audit_gzip_sha256'] = sha(target.read_bytes())
    summary['status'] = 'PASS'
except Exception as exc:
    summary['status'] = 'FAIL'
    summary['error'] = str(exc)
    raise
finally:
    source.write_bytes(original)
    compile_verification('restore-compile')
    (project / 'records/dependency-audit.json').unlink(missing_ok=True)
    restored = run([lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'], 'restore-audit')
    summary['restored_positive_audit'] = restored.returncode == 0 and 'Audit PASS:' in restored.stdout
    if not summary['restored_positive_audit']:
        summary['status'] = 'FAIL'
    assert (project / 'Audit.lean').read_bytes() == audit_original
    summary['source_restored'] = source.read_bytes() == original
    (records / 'lean-controls-result.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: summary[k] for k in ['status', 'controls', 'restored_positive_audit', 'source_restored']}, indent=2))
if summary['status'] != 'PASS':
    raise SystemExit(1)
