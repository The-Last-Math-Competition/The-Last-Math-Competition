#!/usr/bin/env python3
"""Fresh local replay. Never treats an existing success file as evidence of this run."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid

from fingerprints import DEFAULT_PACKAGES, DEFAULT_RUNTIME, inventory, runtime_inventory, sha

PROJECT = Path(__file__).resolve().parent.parent
PROTECTED_SHA256 = 'dba8912404dde60babdd5c20daa14d0286ca60e4ce58bec7931ff025e888b2e6'
INPUT_MANIFEST_SHA256 = '6ae1b92afd1d1f78a64addf92af8cf8db6a645f05b3baae4a1f4330ee46a04a4'
MATH_FILES = ['Conjecture1663.lean', 'Conjecture1663/Definitions.lean',
              'Conjecture1663/Proof.lean', 'Conjecture1663/Challenges.lean', 'Verification.lean']


def require(test, message):
    if not test:
        raise RuntimeError(message)


def checked_output(cmd, **kwargs):
    return subprocess.check_output(cmd, text=True, stderr=subprocess.STDOUT, **kwargs).strip()


def preflight(project):
    project = Path(project)
    require(sha(project / 'PROTECTED.json') == PROTECTED_SHA256, 'Protected pin registry changed')
    protected = json.loads((project / 'PROTECTED.json').read_text())
    for rel, expected in protected.items():
        require(sha(project / rel) == expected, f'Protected input changed: {rel}')
    require(sha(project / 'source/SHA256SUMS.json') == INPUT_MANIFEST_SHA256,
            'Original input hash manifest changed')
    for rel, expected in json.loads((project / 'source/SHA256SUMS.json').read_text()).items():
        require(sha(project / 'source' / rel) == expected, f'Original source changed: {rel}')
    original = json.loads((project / 'source/lake-manifest.json').read_text())
    current = json.loads((project / 'lake-manifest.json').read_text())
    expected_manifest = dict(original, name='tlmc1663')
    require(current == expected_manifest, 'Package manifest differs beyond authorized project rename')
    require((project / 'lean-toolchain').read_text() == 'leanprover/lean4:v4.19.0\n', 'Toolchain changed')
    for rel in MATH_FILES:
        # Comments are retained in this conservative source check. The dependency audit is decisive.
        forbidden = re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|partial)\b',
                              (project / rel).read_text())
        require(forbidden is None, f'Forbidden source token in {rel}: {forbidden}')
    packages = Path(os.environ.get('TLMC_PACKAGES', DEFAULT_PACKAGES))
    package_results = []
    for package in current['packages']:
        root = packages / package['name']
        revision = checked_output(['git', '-C', str(root), 'rev-parse', 'HEAD'])
        require(revision == package['rev'], f'Package revision changed: {package["name"]}')
        status = checked_output(['git', '-C', str(root), 'status', '--porcelain=v1', '--untracked-files=normal'])
        require(status == '', f'Package source is not clean: {package["name"]}: {status}')
        package_results.append(dict(name=package['name'], revision=revision, source_status='clean'))
    expected_runtime = json.loads((project / 'RUNTIME.lock.json').read_text())
    require(runtime_inventory() == expected_runtime, 'Runtime binary or shared-library pin changed')
    runtime_bin = Path(os.environ.get('TLMC_LEAN_BIN', DEFAULT_RUNTIME))
    expected_imports = json.loads((project / 'IMPORTS.lock.json').read_text())
    for row in expected_imports:
        base = runtime_bin.parent / 'lib/lean' if row['provider'] == 'runtime' else packages / row['provider'] / '.lake/build/lib/lean'
        source_base = runtime_bin.parent / 'src/lean' if row['provider'] == 'runtime' else packages / row['provider']
        relative = Path(*row['module'].split('.'))
        obj = base / relative.with_suffix('.olean')
        src = source_base / relative.with_suffix('.lean')
        require(sha(obj) == row['compiled_sha256'], f'Imported compiled object changed: {row["module"]}')
        require((sha(src) if src.is_file() else None) == row['source_sha256'],
                f'Imported source availability/hash changed: {row["module"]}')
    return dict(packages=package_results, runtime=expected_runtime,
                lean_version=checked_output([str(runtime_bin / 'lean'), '--version']),
                python_version=sys.version, protected_registry_sha256=PROTECTED_SHA256)


def audit_summary(log):
    lines = Path(log).read_text().splitlines()
    hits = [s for s in lines if s.startswith('AUDIT_OK\t')]
    require(len(hits) == 1, 'Fresh audit did not emit exactly one success record')
    match = re.fullmatch(r'AUDIT_OK\towned=(\d+)\treachable=(\d+)\taxioms=\[(.*)\]', hits[0])
    require(match is not None, 'Malformed fresh audit summary')
    owned, reachable = int(match[1]), int(match[2])
    require(owned == sum(s.startswith('OWNED\t') for s in lines), 'Owned declaration count mismatch')
    require(reachable == sum(s.startswith('REACHABLE\t') for s in lines), 'Reachable declaration count mismatch')
    axioms = sorted(s.strip() for s in match[3].split(','))
    require(axioms == sorted(['propext', 'Classical.choice', 'Quot.sound']), 'Unexpected closure axiom set')
    return dict(owned_declarations=owned, reachable_declarations=reachable, axioms=axioms)


def validate_receipt(receipt_path):
    receipt_path = Path(receipt_path)
    receipt = json.loads(receipt_path.read_text())
    require(receipt['status'] == 'VERIFIED', 'Receipt is not a success')
    require(receipt['protected_registry_sha256'] == PROTECTED_SHA256, 'Receipt binds a different protected source')
    for rel, expected in receipt['evidence_hashes'].items():
        require(sha(receipt_path.parent / rel) == expected, f'Stale or changed evidence: {rel}')
    require(audit_summary(receipt_path.parent / 'audit.log') == receipt['audit'], 'Receipt/audit mismatch')
    for rel, expected in receipt['own_compiled'].items():
        require(sha(receipt_path.parent / 'workspace' / rel) == expected, f'Changed owned compiled object: {rel}')
    return receipt


def run(project):
    started = time.time()
    run_id = uuid.uuid4().hex
    run_parent = project / 'evidence/runs'
    run_parent.mkdir(parents=True, exist_ok=True)
    run_dir = Path(tempfile.mkdtemp(prefix='run-' + run_id + '-', dir=run_parent))
    workspace = run_dir / 'workspace'
    workspace.mkdir()
    state = dict(run_id=run_id, status='IN_PROGRESS', started_unix=started)
    receipt_path = run_dir / 'receipt.json'
    receipt_path.write_text(json.dumps(state, indent=2) + '\n')
    try:
        pins = preflight(project)
        protected = json.loads((project / 'PROTECTED.json').read_text())
        for rel in protected:
            target = workspace / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(project / rel, target)
        # Copy the pinned registry and the replay entry point as provenance, never compiled cache.
        shutil.copy2(project / 'PROTECTED.json', workspace / 'PROTECTED.json')
        shutil.copy2(project / 'scripts/replay.py', workspace / 'scripts/replay.py')
        package_dir = workspace / '.lake/packages'
        package_dir.mkdir(parents=True)
        packages = Path(os.environ.get('TLMC_PACKAGES', DEFAULT_PACKAGES))
        for p in pins['packages']:
            (package_dir / p['name']).symlink_to(packages / p['name'])
        require(not (workspace / '.lake/build').exists(), 'Fresh build directory unexpectedly exists')
        runtime = Path(os.environ.get('TLMC_LEAN_BIN', DEFAULT_RUNTIME))
        env = dict(os.environ, PATH=str(runtime) + os.pathsep + os.environ.get('PATH', ''))
        commands = [
            ('build-mathematical.log', [str(runtime / 'lake'), 'build', 'Conjecture1663']),
            ('build-verification.log', [str(runtime / 'lake'), 'build', 'Verification']),
            ('audit.log', [str(runtime / 'lake'), 'env', 'lean', '-DwarningAsError=true', 'scripts/Audit.lean']),
            ('finite-checks.json', [sys.executable, 'scripts/finite_checks.py']),
        ]
        for log, command in commands:
            with (run_dir / log).open('w') as out:
                completed = subprocess.run(command, cwd=workspace, env=env,
                                           stdout=out, stderr=subprocess.STDOUT)
            require(completed.returncode == 0, f'Fresh command failed ({completed.returncode}): {command}; see {log}')
        summary = audit_summary(run_dir / 'audit.log')
        imports = inventory(run_dir / 'audit.log', workspace)
        external = [r for r in imports if r['provider'] != 'owned']
        require(external == json.loads((project / 'IMPORTS.lock.json').read_text()), 'Fresh import closure differs from pins')
        (run_dir / 'import-fingerprints.json').write_text(json.dumps(imports, indent=2) + '\n')
        finite = json.loads((run_dir / 'finite-checks.json').read_text())
        require(finite['status'] == 'FINITE_CHECKS_OK', 'Finite checks did not finish')
        # Recheck all inputs after execution to detect concurrent changes and source drift.
        require(preflight(project) == pins, 'Inputs changed during replay')
        own_olean = {}
        for path in sorted((workspace / '.lake/build/lib/lean').rglob('*.olean')):
            own_olean[str(path.relative_to(workspace))] = sha(path)
        logs = [name for name, _ in commands] + ['import-fingerprints.json']
        state.update(pins)
        state.update(status='VERIFIED', finished_unix=time.time(), elapsed_seconds=time.time()-started,
                     audit=summary, own_compiled=own_olean, external_modules=len(external),
                     available_external_sources=sum(r['source_status']=='available' for r in external),
                     unavailable_external_sources=sum(r['source_status']=='unavailable' for r in external),
                     shared_dependency_cache_reused=True, owned_cache_reused=False,
                     evidence_hashes={rel:sha(run_dir / rel) for rel in logs},
                     replay_script_sha256=sha(project / 'scripts/replay.py'))
        receipt_path.write_text(json.dumps(state, indent=2) + '\n')
        validate_receipt(receipt_path)
        print(json.dumps(dict(status='VERIFIED', receipt=str(receipt_path), audit=summary), indent=2))
        return receipt_path
    except Exception as error:
        state.update(status='FAILED', error=str(error), finished_unix=time.time())
        receipt_path.write_text(json.dumps(state, indent=2) + '\n')
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--validate-receipt', type=Path)
    args = parser.parse_args()
    if args.validate_receipt:
        preflight(PROJECT)
        receipt = validate_receipt(args.validate_receipt)
        print(json.dumps(dict(status='EXISTING_RECEIPT_INTEGRITY_ONLY', run_id=receipt['run_id']), indent=2))
    elif args.check_only:
        print(json.dumps(dict(status='PREFLIGHT_ONLY', pins=preflight(PROJECT)), indent=2))
    else:
        run(PROJECT)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('REPLAY_REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
