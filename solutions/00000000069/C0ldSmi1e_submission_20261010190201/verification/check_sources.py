#!/usr/bin/env python3
"""Check the exact statement copy and inventory authored proof sources.

This performs no mathematical computation and is not trusted by the Lean proof.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
expected = json.loads((root / 'source/SHA256SUMS.json').read_text())
for name, digest in expected.items():
    path = root / 'source' / name
    assert path.is_file(), f'Missing exact input copy: {name}'
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == digest, f'Input copy mismatch: {name}'
print(f'All {len(expected)} inventoried input copies match the supplied SHA-256 inventory.')
proofs = sorted((root / 'TLMC69').glob('*.lean')) + [root / 'TLMC69.lean']
for path in proofs:
    text = path.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', text), path
    print(f'{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(root)}')
print('No prohibited proof placeholder, custom axiom, or native_decide token found.')
