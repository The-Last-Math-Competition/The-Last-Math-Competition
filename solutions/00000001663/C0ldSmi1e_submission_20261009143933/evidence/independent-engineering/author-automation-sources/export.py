#!/usr/bin/env python3
"""Produce a deliberate portable source/evidence bundle, without dependency symlinks/caches."""
import json
from pathlib import Path
import shutil

from fingerprints import sha


def main():
    root = Path(__file__).resolve().parent.parent
    destination = root / 'delivery'
    if destination.exists():
        raise RuntimeError('Refusing to replace existing delivery; inspect it or choose a new export explicitly')
    destination.mkdir()
    keep = ['README.md', 'REPORT.md', 'VERIFICATION.md', 'lakefile.lean', 'lake-manifest.json',
            'lean-toolchain', 'Conjecture1663.lean', 'Verification.lean', 'PROTECTED.json',
            'IMPORTS.lock.json', 'RUNTIME.lock.json']
    for directory in ['Conjecture1663', 'source', 'archive', 'scripts']:
        keep += [str(p.relative_to(root)) for p in sorted((root / directory).rglob('*'))
                 if p.is_file() and '__pycache__' not in p.parts and not p.is_symlink()]
    keep += [str(p.relative_to(root)) for p in sorted((root / 'evidence').iterdir()) if p.is_file() and p.name != 'export-result.json']
    keep += ['evidence/negative-controls/results.json']
    receipts = sorted((root / 'evidence/runs').glob('*/receipt.json'))
    controls = json.loads((root / 'evidence/negative-controls/results.json').read_text())
    for c in controls['controls']:
        if 'receipt' in c:
            receipts.append(Path(c['receipt']))
    runs = []
    for receipt in receipts:
        data = json.loads(receipt.read_text())
        require_files = [receipt] + [receipt.parent / rel for rel in data['evidence_hashes']]
        require_files += [receipt.parent / 'workspace' / rel for rel in data['own_compiled']]
        keep += [str(p.relative_to(root)) for p in require_files]
        runs.append(dict(original_receipt=str(receipt), bundled_receipt=str(receipt.relative_to(root)),
                         run_id=data['run_id'], status=data['status']))
    for rel in sorted(set(keep)):
        source = root / rel
        if source.is_symlink():
            raise RuntimeError('Export must not contain symlinks: ' + rel)
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    (destination / 'evidence/ARCHIVED_RUNS.json').write_text(json.dumps(runs, indent=2) + '\n')
    (destination / 'EXPORT.md').write_text('''# Bundle boundary

This bundle contains the frozen sources, reports, supplied inputs, pins, verification programs, actual development and final logs, receipts, and archival failed source attempts. It excludes dependency checkout symlinks, dependency caches, Python caches, generated C/IR, and unrelated local artifacts.

Each archived successful run retains only its five small owned `.olean` objects, under the original relative workspace path, so receipt validation can also verify those recorded object hashes. A fresh replay reconstructs a complete new workspace. Dependency caches and runtime binaries must be supplied separately with the recorded pins for strict replay. Portable source review is described in VERIFICATION.md.

Some evidence records contain absolute paths from the original author workspace. They are provenance, not portable instructions. `evidence/ARCHIVED_RUNS.json` maps each original receipt to the bundle-relative path. `evidence/FINAL_RUN.json` uses a relative receipt locator.

`evidence/DELIVERABLE_HASHES.json` inventories all bundled files other than itself. Preserve its hash externally when transferring the bundle. It is a content inventory, not an independent attestation or substitute for fresh verification.
''')
    hashes = {str(p.relative_to(destination)):sha(p) for p in sorted(destination.rglob('*')) if p.is_file()}
    (destination / 'evidence/DELIVERABLE_HASHES.json').write_text(json.dumps(hashes, indent=2) + '\n')
    print(json.dumps(dict(destination=str(destination), files=len(hashes),
                          total_bytes=sum(p.stat().st_size for p in destination.rglob('*') if p.is_file()),
                          manifest_sha256=sha(destination/'evidence/DELIVERABLE_HASHES.json')), indent=2))


if __name__ == '__main__':
    main()
