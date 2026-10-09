#!/usr/bin/env python3
"""Rebuild and audit only this project; never modify its pinned library sources."""
from __future__ import annotations
import argparse
import hashlib
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
RECORDS = ROOT / 'records'


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def run(args: list[str], label: str, env: dict[str, str], results: list[dict]) -> str:
    start = time.monotonic()
    done = subprocess.run(args, cwd=ROOT, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = RECORDS / f'replay-{label}.log'
    log.write_text(done.stdout)
    results.append({'label': label, 'command': args, 'returncode': done.returncode,
                    'elapsed_seconds': round(time.monotonic() - start, 3),
                    'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log)})
    if done.returncode:
        raise RuntimeError(f'{label} failed with exit {done.returncode}; see {log}')
    if re.search(r'(?m)^.*\bwarning:', done.stdout):
        raise RuntimeError(f'{label} emitted a warning; see {log}')
    return done.stdout


def strip_lean_comments_strings(text: str) -> str:
    # Preserve line breaks; support nested Lean block comments and escaped string quotes.
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else:
                if text[i] == '\n': out.append('\n')
                i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; i += 1; out.append(' ')
            else:
                if text[i] == '\n': out.append('\n')
                i += 1
        elif text.startswith('/-', i): depth = 1; i += 2; out.append(' ')
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        elif text[i] == '"': string = True; i += 1; out.append(' ')
        else: out.append(text[i]); i += 1
    if depth or string:
        raise RuntimeError('Unterminated comment or string during source scan')
    return ''.join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path, required=True,
                        help='Directory containing the Lean 4.19.0 lean and lake executables')
    parser.add_argument('--stdlib-root', type=Path,
                        help='Optional local directory of the nine pinned packages; links only missing packages')
    opts = parser.parse_args()
    lean_bin = opts.lean_bin.resolve()
    env = dict(os.environ)
    env['PATH'] = str(lean_bin) + os.pathsep + env.get('PATH', '')
    RECORDS.mkdir(exist_ok=True)
    results: list[dict] = []
    summary: dict = {'status': 'RUNNING', 'commands': results}
    try:
        expected = json.loads((ROOT / 'source/SHA256SUMS.json').read_text())
        verified = []
        for name, digest in expected.items():
            actual = sha(ROOT / 'source' / name)
            if actual != digest: raise RuntimeError(f'Input hash mismatch: {name}')
            verified.append({'file': name, 'sha256': actual})
        summary['verified_inputs'] = verified
        if sha(ROOT / 'lean-toolchain') != expected['lean-toolchain']:
            raise RuntimeError('Toolchain file differs from supplied toolchain')
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        original = json.loads((ROOT / 'source/lake-manifest.json').read_text())
        if manifest['packages'] != original['packages']:
            raise RuntimeError('Dependency package records differ from supplied pins')
        if manifest['name'] != 'conjecture1624':
            raise RuntimeError('Unexpected local package name')
        pkgdir = ROOT / '.lake/packages'
        pkgdir.mkdir(parents=True, exist_ok=True)
        package_rows = []
        for pkg in manifest['packages']:
            loc = pkgdir / pkg['name']
            if not loc.exists() and opts.stdlib_root:
                target = (opts.stdlib_root / pkg['name']).resolve()
                if not target.is_dir(): raise RuntimeError(f'Missing package {target}')
                loc.symlink_to(target, target_is_directory=True)
            rev = subprocess.check_output(['git', '-C', str(loc), 'rev-parse', 'HEAD'], text=True).strip()
            tracked = subprocess.check_output(['git', '-C', str(loc), 'status', '--porcelain', '--untracked-files=no'], text=True)
            if rev != pkg['rev'] or tracked:
                raise RuntimeError(f'Package revision/source mismatch: {pkg["name"]}')
            package_rows.append({'name': pkg['name'], 'commit': rev, 'tracked_changes': tracked})
        summary['packages'] = package_rows
        version = run([str(lean_bin / 'lean'), '--version'], 'version', env, results)
        if not re.search(r'\bversion 4\.19\.0\b', version):
            raise RuntimeError(f'Unexpected Lean version: {version}')
        summary['runtime_binaries'] = [
            {'file': name, 'path': str(lean_bin / name), 'sha256': sha(lean_bin / name)}
            for name in ['lean', 'lake']]
        prohibited = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|trustLevel')
        source_checks = []
        for name in ['Conjecture1624.lean', 'Verification.lean']:
            matches = prohibited.findall(strip_lean_comments_strings((ROOT / name).read_text()))
            if matches: raise RuntimeError(f'Prohibited source construct in {name}: {matches}')
            source_checks.append({'file': name, 'sha256': sha(ROOT / name), 'prohibited_matches': []})
        summary['proof_source_checks'] = source_checks
        build = ROOT / '.lake/build'
        if build.exists():
            if build.is_symlink() or build.resolve() != build:
                raise RuntimeError('Refusing to remove a symlinked build directory')
            shutil.rmtree(build)
        summary['removed_owned_build_directory_before_rebuild'] = True
        lake = str(lean_bin / 'lake')
        run([lake, 'build'], 'clean-build', env, results)
        for name, label in [('Conjecture1624.lean', 'core'), ('Verification.lean', 'verification'), ('Audit.lean', 'audit')]:
            run([lake, 'env', 'lean', '-DwarningAsError=true', name], label, env, results)
        audit = json.loads((RECORDS / 'dependency-audit.json').read_text())
        if audit['status'] != 'PASS' or audit['forbidden_axioms'] or audit['unsafe_dependencies'] or audit['partial_dependencies']:
            raise RuntimeError('Dependency audit did not pass')
        summary['audit'] = {key: audit[key] for key in ['status', 'owned_count', 'dependency_count', 'axioms', 'forbidden_axioms', 'unsafe_dependencies', 'partial_dependencies']}
        summary['dependency_audit_sha256'] = sha(RECORDS / 'dependency-audit.json')
        (RECORDS / 'dependency-audit.json.gz').write_bytes(
            gzip.compress((RECORDS / 'dependency-audit.json').read_bytes(), mtime=0))
        summary['dependency_audit_gzip_sha256'] = sha(RECORDS / 'dependency-audit.json.gz')
        # Fingerprint every imported compiled module and every corresponding available source.
        # Runtime sources may be absent from this runtime distribution; this is recorded, not hidden.
        lib_roots = [ROOT / '.lake/build/lib/lean'] + [pkgdir / x['name'] / '.lake/build/lib/lean' for x in manifest['packages']] + [lean_bin.parent / 'lib/lean']
        src_roots = [ROOT] + [pkgdir / x['name'] for x in manifest['packages']] + [lean_bin.parent / 'src/lean']
        fingerprints = []
        for module in audit['imported_modules']:
            rel = Path(*module.split('.'))
            obj = next((d / rel.with_suffix('.olean') for d in lib_roots if (d / rel.with_suffix('.olean')).is_file()), None)
            source = next((d / rel.with_suffix('.lean') for d in src_roots if (d / rel.with_suffix('.lean')).is_file()), None)
            if obj is None: raise RuntimeError(f'Imported module artifact not found: {module}')
            fingerprints.append({'module': module, 'olean_path': str(obj), 'olean_sha256': sha(obj),
                                 'source_path': str(source) if source else None,
                                 'source_sha256': sha(source) if source else None})
        (RECORDS / 'import-fingerprints.json').write_text(json.dumps(fingerprints, indent=2) + '\n')
        summary['import_fingerprint_count'] = len(fingerprints)
        summary['import_fingerprints_sha256'] = sha(RECORDS / 'import-fingerprints.json')
        (RECORDS / 'import-fingerprints.json.gz').write_bytes(
            gzip.compress((RECORDS / 'import-fingerprints.json').read_bytes(), mtime=0))
        summary['import_fingerprints_gzip_sha256'] = sha(RECORDS / 'import-fingerprints.json.gz')
        summary['status'] = 'PASS'
    except Exception as exc:
        summary['status'] = 'FAIL'
        summary['error'] = str(exc)
        raise
    finally:
        (RECORDS / 'replay-result.json').write_text(json.dumps(summary, indent=2) + '\n')
        print(json.dumps({k: v for k, v in summary.items() if k in ['status', 'audit', 'error', 'import_fingerprint_count']}, indent=2))


if __name__ == '__main__':
    main()
