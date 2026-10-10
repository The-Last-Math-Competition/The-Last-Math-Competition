#!/usr/bin/env python3
"""Independently rebuild and audit this frozen Lean submission.

Run: python3 verify.py [--lean-bin /path/to/lean/bin]
Requires Python 3.9 or later; uses only its standard library.
Optional offline reuse: --stock-mathlib /path/to/pinned/mathlib
Stock sources/caches are copied; local submitted oleans are never reused.
The work directory must not exist. All commands have complete raw receipts.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

EXPECTED = {
    'Conjecture302.lean': 'aedd718cba074730350efded0fbd45b49f1e328b28eed847854c0b01949fef1f',
    'Audit.lean': 'bedbc63410992b36630ac77341bcc060df0c103b64c195feefbcb9837061467b',
    'lakefile.lean': 'c26ffaa3f4917ebf9e35e5782c6182f2c45001d0be47a5ef4a552dd37c97542d',
    'lean-toolchain': '55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea',
    'lake-manifest.json': '56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637',
}
LEAN_FILES = ['lakefile.lean', 'Conjecture302.lean', 'Audit.lean',
              'Verification/ClosureAudit.lean', 'ClosureCheck.lean']
THEOREMS = {'Conjecture302.' + n for n in [
    'mem_II_of_not_liouvilleWith', 'ae_irrational', 'ae_mem_II',
    'dimH_eq_one_of_ae_mem', 'dimH_II', 'dimH_inter_II', 'conjecture', 'II._proof_1']}
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def command(argv, cwd, logs, label, env, expect_success=True):
    started = datetime.now(timezone.utc)
    prefix = logs / (started.strftime('%Y%m%dT%H%M%S.%fZ-') + label)
    out_path, err_path = Path(str(prefix) + '.stdout'), Path(str(prefix) + '.stderr')
    tick = time.monotonic()
    with out_path.open('wb') as out, err_path.open('wb') as err:
        result = subprocess.run([str(a) for a in argv], cwd=cwd, env=env,
                                stdout=out, stderr=err, check=False)
    receipt = {'command': [str(a) for a in argv], 'shell_display': shlex.join(map(str, argv)),
               'cwd': str(cwd), 'started_utc': started.isoformat(),
               'finished_utc': datetime.now(timezone.utc).isoformat(),
               'elapsed_seconds': time.monotonic() - tick, 'exit_code': result.returncode,
               'stdout': str(out_path), 'stderr': str(err_path),
               'environment': {k: env.get(k) for k in ['PATH', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT',
                   'GIT_CONFIG_NOSYSTEM', 'GIT_CONFIG_GLOBAL', 'GIT_NO_REPLACE_OBJECTS',
                   'GIT_NO_LAZY_FETCH', 'GIT_TERMINAL_PROMPT']}}
    Path(str(prefix) + '.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'{label}: exit {result.returncode}; {out_path}', flush=True)
    if expect_success:
        require(result.returncode == 0, f'{label} failed; inspect {out_path} and {err_path}')
    return result.returncode, out_path.read_text(errors='replace'), err_path.read_text(errors='replace')


def verify_frozen(source):
    for name, digest in EXPECTED.items():
        require(sha256(source / name) == digest, f'Frozen source mismatch: {name}')
    discovered = []
    for directory, dirs, files in os.walk(source):
        dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '__pycache__'}]
        for name in files:
            if name.endswith('.lean'):
                discovered.append(str((Path(directory) / name).relative_to(source)))
    require(set(discovered) == set(LEAN_FILES), f'Unaccounted Lean source inventory: {discovered}')
    return {name: sha256(source / name) for name in list(EXPECTED) + LEAN_FILES + ['verify.py']}


def verify_stock(project, logs, env):
    result = {}
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        name = package['name']
        repo = project / '.lake/packages' / name
        _, rev, _ = command(['git', '-C', repo, 'rev-parse', 'HEAD'], project, logs, name + '-pin', env)
        require(rev.strip() == package['rev'], f'Unexpected revision: {name}')
        _, tree, _ = command(['git', '-C', repo, 'ls-tree', '-r', '-z', 'HEAD'], project, logs, name + '-tree', env)
        files = {}
        for entry in tree.split('\0'):
            if not entry:
                continue
            metadata, relative = entry.split('\t', 1)
            mode, object_kind, expected_blob = metadata.split()
            require(object_kind == 'blob', f'Unexpected submodule: {name}/{relative}')
            path = repo / relative
            data = os.readlink(path).encode() if mode == '120000' else path.read_bytes()
            actual_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            require(actual_blob == expected_blob, f'Stock source differs from pinned Git tree: {name}/{relative}')
            files[relative] = hashlib.sha256(data).hexdigest()
        result[name] = {'revision': rev.strip(), 'tracked_files': files}
    (project.parent / 'stock-source-manifest.json').write_text(json.dumps(result, indent=2) + '\n')
    return {name: len(data['tracked_files']) for name, data in result.items()}


def inspect_audit(path):
    audit = json.loads(path.read_text())
    require(not audit['failures'], f'Closure audit failed: {audit["failures"]}')
    declarations = audit['declarations']
    require({d['name'] for d in declarations if d['kind'] == 'theorem'} == THEOREMS,
            'Compiled theorem inventory differs from the seven stated theorems plus the generated numeral proof')
    require({d['name'] for d in declarations if d['kind'] == 'definition'} == {'Conjecture302.II'},
            'Unexpected local definition inventory')
    graph = {d['name']: d for d in audit['dependency_graph']}
    for d in declarations:
        require(not d['unsafe'] and not d['unsafe_dependencies'], 'Unsafe local dependency')
        require(set(d['axioms']) <= STANDARD_AXIOMS, 'Forbidden axiom in closure')
        require(set(d['lean_collectAxioms']) <= set(d['axioms']), 'Axiom collector discrepancy')
        reached, pending = set(), [d['name']]
        while pending:
            n = pending.pop()
            if n not in reached:
                require(n in graph, f'Missing graph node {n}')
                reached.add(n)
                pending.extend(graph[n]['dependencies'])
        require(reached == set(d['closure']), f'Incomplete closure export for {d["name"]}')
        require({n for n in reached if graph[n]['kind'] == 'axiom'} == set(d['axioms']), 'Incomplete axiom list')
        require({n for n in reached if graph[n]['unsafe']} == set(d['unsafe_dependencies']), 'Incomplete unsafe list')
    return {'local_declarations': len(declarations), 'reachable_declarations': len(graph),
            'axioms': sorted({a for d in declarations for a in d['axioms']})}


def record_artifacts(project, logs, env, lake, lean):
    _, paths, _ = command([lake, 'env', sys.executable, '-c',
                           'import os; print(os.environ.get("LEAN_PATH", ""))'],
                          project, logs, 'lean-search-path', env)
    _, prefix, _ = command([lake, 'env', 'lean', '--print-prefix'],
                           project, logs, 'lean-prefix', env)
    roots = [Path(p) if Path(p).is_absolute() else project / p
             for p in paths.strip().split(os.pathsep) if p]
    roots.append(Path(prefix.strip()) / 'lib/lean')
    modules = json.loads((project / 'closure-audit.json').read_text())['imported_modules']
    artifacts = {}
    for name in modules:
        relative = Path(*name.split('.')).with_suffix('.olean')
        matches = [root / relative for root in roots if (root / relative).is_file()]
        require(matches, f'Cannot locate imported compiled module: {name}')
        path = matches[0].resolve()
        artifacts[name] = {'path': str(path), 'sha256': sha256(path)}
    native = {}
    for root in [project / '.lake/packages', Path(prefix.strip()) / 'lib']:
        for directory, dirs, files in os.walk(root, followlinks=False):
            dirs[:] = [d for d in dirs if d != '.git']
            for filename in files:
                if filename.endswith(('.dylib', '.so')):
                    path = Path(directory) / filename
                    native[str(path.resolve())] = sha256(path)
    result = {'module_artifacts': artifacts, 'available_native_libraries': native,
              'executables': {str(Path(lean).resolve()): sha256(Path(lean).resolve()),
                              str(Path(lake).resolve()): sha256(Path(lake).resolve())}}
    (project.parent / 'compiled-input-manifest.json').write_text(json.dumps(result, indent=2) + '\n')
    return len(artifacts)


def rejection_controls(project, logs, env, lake):
    controls = project / 'VerificationControls'
    controls.mkdir(exist_ok=True)
    cases = {
        'Admission': ('import Lean\ntheorem omitted : True := by sorry\n', 'warning', None),
        'HiddenAxiom': ('import Lean\naxiom hidden : False\ntheorem exported : False := hidden\n', 'audit', 'forbidden axiom'),
        'UnsafeDefinition': ('import Lean\nunsafe def hiddenUnsafe : Nat := 0\n', 'audit', 'unsafe dependency'),
        'NativeDecision': ('import Lean\ntheorem nativeResult : (1 : Nat) = 1 := by native_decide\n#print axioms nativeResult\n', 'audit', 'unsafe dependency'),
    }
    results = {}
    for name, (source, mode, expected_message) in cases.items():
        module = 'VerificationControls.' + name
        path = controls / (name + '.lean')
        path.write_text(source)
        olean = project / '.lake/build/lib/lean/VerificationControls' / (name + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        code, out, err = command([lake, 'env', 'lean', '-DwarningAsError=true', path.relative_to(project),
                                  '-o', olean.relative_to(project)], project, logs,
                                 'control-compile-' + name, env, expect_success=False)
        if mode == 'warning':
            require(code != 0 and "declaration uses 'sorry'" in out + err, 'Admission control was not rejected')
        else:
            require(code == 0, f'Control did not compile: {name}; {out} {err}')
            check = controls / ('Check' + name + '.lean')
            check.write_text(f'import {module}\nimport Verification.ClosureAudit\n#audit_modules [{module}] "control-{name}.json"\n')
            code, out, err = command([lake, 'env', 'lean', '-DwarningAsError=true', check.relative_to(project)],
                                     project, logs, 'control-audit-' + name, env, expect_success=False)
            require(code != 0 and expected_message in out + err, f'Control was not rejected as intended: {name}')
        results[name] = 'rejected as intended'
    # Ensure the Python manifest guard does not depend on stale compiled objects.
    source = project / 'Conjecture302.lean'
    original = source.read_bytes()
    try:
        source.write_bytes(original + b'\n-- changed frozen input\n')
        try:
            verify_frozen(project)
        except RuntimeError as error:
            require(str(error) == 'Frozen source mismatch: Conjecture302.lean',
                    f'Unexpected mutation rejection: {error}')
        else:
            raise RuntimeError('Manifest guard accepted changed frozen source')
    finally:
        source.write_bytes(original)
    results['FrozenMutation'] = 'detected by exact hash'
    try:
        verify_frozen(project)
    except RuntimeError as error:
        require(str(error).startswith('Unaccounted Lean source inventory:'),
                f'Unexpected unlisted-module rejection: {error}')
    else:
        raise RuntimeError('Source inventory guard accepted unlisted control modules')
    results['UnlistedModule'] = 'rejected by exhaustive source inventory'
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--stock-mathlib', type=Path)
    parser.add_argument('--work-dir', type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    source_hashes = verify_frozen(source)
    if args.work_dir:
        require(not args.work_dir.resolve().is_relative_to(source),
                'Use a work directory outside the frozen source directory')
    work = args.work_dir or Path(tempfile.mkdtemp(prefix='tlmc302-verification-'))
    if args.work_dir:
        work.mkdir(parents=True, exist_ok=False)
    work = work.resolve()
    logs = work / 'logs'
    logs.mkdir()
    project = work / 'project'
    project.mkdir()
    for name in set(EXPECTED) | set(LEAN_FILES):
        target = project / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / name, target)
    env = os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_'):
            env.pop(key)
    env.update({'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': os.devnull,
                'GIT_NO_REPLACE_OBJECTS': '1', 'GIT_NO_LAZY_FETCH': '1',
                'GIT_TERMINAL_PROMPT': '0'})
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
        env.pop(key, None)
    if args.lean_bin:
        env['PATH'] = str(args.lean_bin.resolve()) + os.pathsep + env.get('PATH', '')
    lake = shutil.which('lake', path=env['PATH'])
    lean = shutil.which('lean', path=env['PATH'])
    require(lake and lean, 'Lean and Lake must be installed')
    _, version, _ = command([lean, '--version'], project, logs, 'lean-version', env)
    require(re.search(r'\bversion 4\.19\.0,', version), 'Wrong Lean version')
    command([lake, '--version'], project, logs, 'lake-version', env)
    if args.stock_mathlib:
        packages = project / '.lake/packages'
        packages.mkdir(parents=True)
        stock = args.stock_mathlib.resolve()
        if platform.system() == 'Darwin':
            command(['/bin/cp', '-cR', stock, packages / 'mathlib'], project, logs, 'copy-stock', env)
        else:
            shutil.copytree(stock, packages / 'mathlib', symlinks=True)
        manifest = json.loads((project / 'lake-manifest.json').read_text())
        for p in manifest['packages']:
            if p['name'] != 'mathlib':
                (packages / p['name']).symlink_to(Path('mathlib/.lake/packages') / p['name'])
    require(not (project / '.lake/build').exists(), 'Fresh project unexpectedly contains local build artifacts')
    command([lake, 'build'], project, logs, 'fresh-project-build', env)
    stock_counts = verify_stock(project, logs, env)
    for name in LEAN_FILES:
        argv = [lake, 'env', 'lean', '-DwarningAsError=true', name]
        if name == 'Verification/ClosureAudit.lean':
            output = project / '.lake/build/lib/lean/Verification/ClosureAudit.olean'
            output.parent.mkdir(parents=True, exist_ok=True)
            argv += ['-o', str(output.relative_to(project))]
        command(argv, project, logs, 'replay-' + name.replace('/', '-'), env)
    audit_summary = inspect_audit(project / 'closure-audit.json')
    artifact_count = record_artifacts(project, logs, env, lake, lean)
    controls = rejection_controls(project, logs, env, lake)
    require(source_hashes == verify_frozen(source), 'Original source changed during verification')
    for name, digest in EXPECTED.items():
        require(sha256(project / name) == digest, f'Working source changed: {name}')
    summary = {'status': 'pass', 'finished_utc': datetime.now(timezone.utc).isoformat(),
               'source': str(source), 'work': str(work), 'source_sha256': source_hashes,
               'stock_tracked_file_counts': stock_counts, 'audit': audit_summary,
               'imported_compiled_module_count': artifact_count,
               'controls': controls, 'auxiliary_mathematical_computations_required': False,
               'scope': 'Fresh local module build, direct warning-as-error replay of every submitted Lean source, compiled inventory and complete type/body dependency closure. Pinned stock compiled artifacts may be reused; stock modules are not all rebuilt.'}
    (work / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
