#!/usr/bin/env python3
"""Fingerprint precisely the module import inventory emitted by Lean's audit."""
import hashlib
import json
import os
from pathlib import Path

DEFAULT_PACKAGES = '/private/tmp/tlmc-standard-library-419'
DEFAULT_RUNTIME = '/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def inventory(audit_log, project):
    project = Path(project)
    packages = Path(os.environ.get('TLMC_PACKAGES', DEFAULT_PACKAGES))
    runtime = Path(os.environ.get('TLMC_LEAN_BIN', DEFAULT_RUNTIME)).parent
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    providers = [('runtime', runtime / 'lib/lean', runtime / 'src/lean')]
    providers += [(p['name'], packages / p['name'] / '.lake/build/lib/lean', packages / p['name'])
                  for p in manifest['packages']]
    providers += [('owned', project / '.lake/build/lib/lean', project)]
    modules = sorted({line.split('\t')[1] for line in Path(audit_log).read_text().splitlines()
                      if line.startswith('MODULE\t')})
    assert modules, 'No module inventory in audit log'
    result = []
    for module in modules:
        relative = Path(*module.split('.'))
        found = []
        for provider, compiled, source_root in providers:
            obj = compiled / relative.with_suffix('.olean')
            if obj.is_file():
                src = source_root / relative.with_suffix('.lean')
                found.append(dict(module=module, provider=provider,
                                  compiled_sha256=sha(obj), compiled_bytes=obj.stat().st_size,
                                  source_sha256=sha(src) if src.is_file() else None,
                                  source_status='available' if src.is_file() else 'unavailable'))
        assert len(found) == 1, f'Expected unique module provider for {module}: {found}'
        result.append(found[0])
    return result


def runtime_inventory():
    runtime = Path(os.environ.get('TLMC_LEAN_BIN', DEFAULT_RUNTIME)).parent
    files = [runtime / 'bin/lean', runtime / 'bin/lake']
    files += sorted((runtime / 'lib').rglob('*.dylib'))
    return {str(p.relative_to(runtime)): sha(p) for p in files}
