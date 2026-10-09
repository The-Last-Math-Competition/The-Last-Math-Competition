#!/usr/bin/env python3
"""Portable source/pin checks, deliberately not a claim of strict binary replay."""
import argparse
import json
from pathlib import Path
import subprocess

from fingerprints import sha
from replay import PROTECTED_SHA256, require


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages', type=Path, default=Path('.lake/packages'))
    args = parser.parse_args()
    project = Path(__file__).resolve().parent.parent
    require(sha(project / 'PROTECTED.json') == PROTECTED_SHA256, 'Protected registry changed')
    for rel, expected in json.loads((project / 'PROTECTED.json').read_text()).items():
        require(sha(project / rel) == expected, 'Protected source/lock changed: ' + rel)
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    results = []
    for p in manifest['packages']:
        package = args.packages / p['name']
        head = subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
        status = subprocess.check_output(['git', '-C', str(package), 'status', '--porcelain=v1', '--untracked-files=normal'], text=True).strip()
        require(head == p['rev'], 'Dependency revision differs: ' + p['name'])
        require(status == '', 'Dependency sources are dirty: ' + p['name'])
        results.append(dict(name=p['name'], revision=head, source_status='clean'))
    print(json.dumps(dict(status='SOURCE_PINS_ONLY', packages=results,
                         notice='This is not a strict binary-cache replay result.'), indent=2))


if __name__ == '__main__':
    main()
