#!/usr/bin/env python3
"""Check archival input bytes and all pinned library revisions; no mathematical computation."""
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
manifest = root / "INPUT-SHA256SUMS.json"
expected_manifest_hash = "1b6ce2a1de00707fe55bf3fba767f834d139b546ffbb005d30b191eb502a4da6"
assert hashlib.sha256(manifest.read_bytes()).hexdigest() == expected_manifest_hash
print(f"PASS clean-input manifest {expected_manifest_hash}")
for name, expected in json.loads(manifest.read_text()).items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == expected, (name, actual, expected)
    print(f"PASS input {name} {actual}")
packages = json.loads((root / "lake-manifest.json").read_text())["packages"]
assert len(packages) == 9
for package in packages:
    checkout = root / ".lake" / "packages" / package["name"]
    actual = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert actual == package["rev"], (package["name"], actual, package["rev"])
    dirty = subprocess.check_output(
        ["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"], text=True
    ).strip()
    assert not dirty, (package["name"], dirty)
    print(f"PASS dependency {package['name']} {actual} tracked-source-clean")
