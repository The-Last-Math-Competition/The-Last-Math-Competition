#!/usr/bin/env python3
"""Execute fail-closed mutation checks without editing frozen author sources or shared packages."""
import json
from pathlib import Path
import shutil
import sys
import tempfile

import replay


def main():
    source = Path(__file__).resolve().parent.parent
    destination = source / 'evidence/negative-controls'
    destination.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix='case-', dir=destination))
    registry = json.loads((source / 'PROTECTED.json').read_text())
    for rel in list(registry) + ['PROTECTED.json', 'scripts/replay.py']:
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / rel, target)
    results = []

    def mutation(label, path):
        original = path.read_bytes()
        path.write_bytes(original + b'\nchanged input\n')
        try:
            replay.preflight(root)
        except Exception as error:
            results.append(dict(control=label, status='REJECTED_AS_REQUIRED', reason=str(error)))
        else:
            raise AssertionError(f'{label} was incorrectly accepted')
        finally:
            path.write_bytes(original)

    for label, rel in [
        ('changed_original', 'source/ORIGINAL.md'),
        ('changed_mathematical_source', 'Conjecture1663/Proof.lean'),
        ('changed_toolchain', 'lean-toolchain'),
        ('changed_dependency_manifest', 'lake-manifest.json'),
        ('changed_import_object_pins', 'IMPORTS.lock.json'),
        ('changed_runtime_pins', 'RUNTIME.lock.json'),
        ('changed_pin_registry', 'PROTECTED.json'),
        ('changed_audit_program', 'scripts/Audit.lean'),
    ]:
        mutation(label, root / rel)

    stale = root / 'evidence/runs/stale'
    stale.mkdir(parents=True)
    (stale / 'receipt.json').write_text('{"status":"VERIFIED","run_id":"old-counterfeit"}\n')
    (stale / 'audit.log').write_text('AUDIT_OK\towned=62\treachable=4575\taxioms=[Quot.sound, Classical.choice, propext]\n')
    # A complete new run must execute despite the planted stale success files.
    fresh_receipt = replay.run(root)
    fresh = json.loads(fresh_receipt.read_text())
    assert fresh['run_id'] != 'old-counterfeit' and fresh_receipt.parent != stale
    results.append(dict(control='preexisting_success_cannot_replace_replay', status='FRESH_RUN_EXECUTED',
                        receipt=str(fresh_receipt), run_id=fresh['run_id']))

    for label, path in [
        ('stale_or_modified_audit_evidence', fresh_receipt.parent / 'audit.log'),
        ('modified_owned_compiled_object', fresh_receipt.parent / 'workspace' / next(iter(fresh['own_compiled']))),
    ]:
        original = path.read_bytes()
        path.write_bytes(original + b'\nstale data\n')
        try:
            replay.validate_receipt(fresh_receipt)
        except Exception as error:
            results.append(dict(control=label, status='REJECTED_AS_REQUIRED', reason=str(error)))
        else:
            raise AssertionError(f'{label} was incorrectly accepted')
        finally:
            path.write_bytes(original)
    replay.validate_receipt(fresh_receipt)
    payload = dict(status='NEGATIVE_CONTROLS_OK', controls=results, root=str(root))
    (destination / 'results.json').write_text(json.dumps(payload, indent=2) + '\n')
    print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
