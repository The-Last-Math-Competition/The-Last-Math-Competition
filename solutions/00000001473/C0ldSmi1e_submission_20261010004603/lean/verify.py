#!/usr/bin/env python3
"""Freshly build and independently audit a frozen Lean submission (Python 3.9+).

Usage: python3 verify.py --lean-bin /path/to/lean/bin \
         [--stock-mathlib /path/to/pinned/mathlib] [--work-dir NEW_DIRECTORY]

The adjacent verification-manifest.json lists every frozen input, every authored
Lean module and the exact expected mathematical declaration inventory. It is a
public review artifact, not a cryptographic signature. Its own digest is recorded.
No submitted compiled files are copied. Optional pinned stock binary caches are
copied, source-verified, and explicitly reported as reused rather than rebuilt.
Without --stock-mathlib the pinned dependencies and stock cache are downloaded.
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
import traceback

STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EDGE_KINDS = ('type_dependencies', 'body_dependencies', 'recursor_dependencies',
              'inductive_dependencies')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


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
               'stdout_sha256': sha256(out_path), 'stderr_sha256': sha256(err_path),
               'environment': {k: env.get(k) for k in ['PATH', 'LEAN_PATH', 'LEAN_SRC_PATH',
                   'LEAN_SYSROOT', 'GIT_CONFIG_NOSYSTEM', 'GIT_CONFIG_GLOBAL',
                   'GIT_NO_REPLACE_OBJECTS', 'GIT_NO_LAZY_FETCH', 'GIT_TERMINAL_PROMPT']}}
    write_json(Path(str(prefix) + '.json'), receipt)
    print(f'{label}: exit {result.returncode}; {out_path}', flush=True)
    if expect_success:
        require(result.returncode == 0, f'{label} failed; inspect {out_path} and {err_path}')
    return result.returncode, out_path.read_text(errors='replace'), err_path.read_text(errors='replace')


def verify_frozen(source, manifest):
    for name, digest in manifest['frozen_files'].items():
        require(not Path(name).is_absolute() and '..' not in Path(name).parts,
                f'Frozen source must remain within the package: {name}')
        path = source / name
        require(path.is_file() and not path.is_symlink(), f'Missing or symlinked frozen source: {name}')
        require(sha256(path) == digest, f'Frozen source mismatch: {name}')
    discovered = []
    for directory, dirs, files in os.walk(source):
        dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '__pycache__'}]
        for name in files:
            if name.endswith('.lean'):
                discovered.append(str((Path(directory) / name).relative_to(source)))
    require(set(discovered) == set(manifest['lean_files']),
            f'Unaccounted Lean source inventory: {sorted(discovered)}')
    require(set(manifest['lean_files']) <= set(manifest['frozen_files']),
            'Every Lean source must be frozen, including configuration and auditors')
    return {name: sha256(source / name) for name in manifest['frozen_files']}


def check_proof_tokens(source, modules):
    """Reject forbidden Lean keywords outside nested comments/string literals."""
    for module in modules:
        path = source / (module.replace('.', '/') + '.lean')
        text = path.read_text()
        clean, pos, depth = [], 0, 0
        while pos < len(text):
            if depth:
                if text.startswith('/-', pos):
                    depth += 1
                    pos += 2
                elif text.startswith('-/', pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            elif text.startswith('/-', pos):
                clean.append(' ')
                depth, pos = 1, pos + 2
            elif text.startswith('--', pos):
                end = text.find('\n', pos)
                pos = len(text) if end < 0 else end
                clean.append(' ')
            elif text[pos] == '"':
                clean.append(' ')
                pos += 1
                while pos < len(text) and text[pos] != '"':
                    pos += 2 if text[pos] == '\\' else 1
                pos += 1
            else:
                clean.append(text[pos])
                pos += 1
        found = re.findall(r'(?<![\w.])(?:sorry|admit|native_decide|axiom|unsafe)(?![\w])', ''.join(clean))
        require(not found, f'Forbidden proof source token in {module}: {found}')


def verify_stock(project, logs, env, phase):
    result = {}
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        name = package['name']
        repo = project / '.lake/packages' / name
        _, rev, _ = command(['git', '-C', repo, 'rev-parse', 'HEAD'], project, logs,
                            phase + '-' + name + '-pin', env)
        require(rev.strip() == package['rev'], f'Unexpected revision: {name}')
        _, tree, _ = command(['git', '-C', repo, 'ls-tree', '-r', '-z', package['rev']],
                            project, logs, phase + '-' + name + '-tree', env)
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
            require(actual_blob == expected_blob,
                    f'Stock source differs from pinned Git blob: {name}/{relative}')
            files[relative] = {'git_blob': expected_blob, 'sha256': hashlib.sha256(data).hexdigest()}
        _, untracked, _ = command(['git', '-C', repo, 'ls-files', '--others', '--exclude-standard'],
                                 project, logs, phase + '-' + name + '-untracked', env)
        require(not [p for p in untracked.splitlines() if p.endswith('.lean')],
                f'Untracked Lean source in stock package: {name}')
        result[name] = {'revision': rev.strip(), 'tracked_files': files}
    write_json(project.parent / (phase + '-stock-source-manifest.json'), result)
    return {name: len(data['tracked_files']) for name, data in result.items()}


def inspect_audit(path, expected_modules, expected_declarations=None, strict=True):
    audit = json.loads(path.read_text())
    require(audit['strict_proof_check'] == strict, 'Wrong audit enforcement mode')
    require(set(audit['requested_modules']) == set(expected_modules), 'Wrong originating modules')
    if strict:
        require(not audit['failures'], f'Closure audit failed: {audit["failures"]}')
        require(audit['kernel_roots_only'], 'Mathematical audit must enforce every kernel-safe root')
    declarations = audit['declarations']
    require(len(declarations) == audit['local_declaration_count'], 'Declaration count mismatch')
    require(len({d['name'] for d in declarations}) == len(declarations), 'Duplicate inventory entry')
    require(all(d['module'] in expected_modules for d in declarations), 'Foreign root in inventory')
    if expected_declarations is not None:
        require({d['name']: d['kind'] for d in declarations} == expected_declarations,
                'Compiled mathematical declaration inventory differs from frozen specification')
    graph = {d['name']: d for d in audit['dependency_graph']}
    require(len(graph) == audit['closure_declaration_count'], 'Graph count mismatch')
    for node in graph.values():
        require(set(node['dependencies']) == {n for field in EDGE_KINDS for n in node[field]},
                f'Incomplete edge categories: {node["name"]}')
    used = set()
    for d in declarations:
        if strict and not d['unsafe']:
            require(d['trust_enforced'], 'Safe mathematical declaration was not trust-audited')
            require(not d['unsafe'] and not d['unsafe_dependencies'], 'Unsafe mathematical dependency')
            require(set(d['axioms']) <= STANDARD_AXIOMS, 'Forbidden axiom in closure')
        require(set(d['lean_collectAxioms']) <= set(d['axioms']), 'Axiom collector discrepancy')
        reached, pending = set(), [d['name']]
        while pending:
            name = pending.pop()
            if name not in reached:
                require(name in graph, f'Missing graph node {name}')
                reached.add(name)
                pending.extend(graph[name]['dependencies'])
        require(reached == set(d['closure']), f'Incomplete closure export for {d["name"]}')
        if strict and not d['unsafe']:
            require(all(graph[n]['kind'] != 'unavailable' for n in reached),
                    'Incomplete safe mathematical dependency closure')
        require({n for n in reached if graph[n]['kind'] == 'axiom'} == set(d['axioms']),
                'Incomplete axiom list')
        require({n for n in reached if graph[n]['unsafe']} == set(d['unsafe_dependencies']),
                'Incomplete unsafe list')
        used.update(reached)
    require(used == set(graph), 'Extraneous graph nodes')
    return {'local_declarations': len(declarations), 'reachable_declarations': len(graph),
            'kernel_safe_root_count': sum(not d['unsafe'] for d in declarations),
            'compiler_runtime_root_count': sum(d['unsafe'] for d in declarations),
            'kernel_safe_root_axioms': sorted({a for d in declarations if not d['unsafe'] for a in d['axioms']}),
            'kernel_safe_root_unsafe_dependencies': sorted({a for d in declarations if not d['unsafe'] for a in d['unsafe_dependencies']}),
            'runtime_findings_count': len(audit['compiler_runtime_findings']),
            'theorem_types': {d['name']: {'type': d['type'], 'raw_type': d['raw_type']}
                              for d in declarations if d['kind'] == 'theorem'},
            'sha256': sha256(path)}


def record_artifacts(project, logs, env, lake, lean):
    _, paths, _ = command([lake, 'env', sys.executable, '-c',
                           'import os; print(os.environ.get("LEAN_PATH", ""))'],
                          project, logs, 'lean-search-path', env)
    _, prefix, _ = command([lean, '--print-prefix'], project, logs, 'lean-prefix', env)
    roots = [Path(p) if Path(p).is_absolute() else project / p
             for p in paths.strip().split(os.pathsep) if p]
    roots.append(Path(prefix.strip()) / 'lib/lean')
    modules = set()
    for report in ('closure-audit.json', 'infrastructure-audit.json'):
        modules.update(json.loads((project / report).read_text())['imported_modules'])
    artifacts = {}
    for name in sorted(modules):
        relative = Path(*name.split('.')).with_suffix('.olean')
        matches = [root / relative for root in roots if (root / relative).is_file()]
        require(matches, f'Cannot locate imported compiled module: {name}')
        path = matches[0].resolve()
        artifacts[name] = {'path': str(path), 'sha256': sha256(path),
                           'locally_rebuilt': path.is_relative_to(project / '.lake/build')}
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
    write_json(project.parent / 'compiled-input-manifest.json', result)
    return len(artifacts)


def rejection_controls(project, logs, env, lake, manifest):
    controls = project / 'VerificationControls'
    controls.mkdir(exist_ok=True)
    cases = {
        'Admission': ('import Lean\ntheorem omitted : True := by sorry\n', 'compile', "declaration uses 'sorry'"),
        'CustomAxiom': ('import Lean\naxiom hidden : False\ntheorem exported : False := hidden\n', 'audit', 'forbidden axiom'),
        'UnsafeRoot': ('import Lean\nunsafe def hiddenUnsafe : Nat := 0\n', 'audit-all', 'unsafe dependency'),
        'UnsafeProof': ('import Lean\nunsafe def hiddenUnsafe : Nat := 0\ntheorem exported : hiddenUnsafe = 0 := by rfl\n', 'compile', 'unsafe'),
        'NativeDecision': ('import Lean\ntheorem nativeResult : (1 : Nat) = 1 := by native_decide\n', 'audit', 'dependency'),
    }
    results = {}
    for name, (source, mode, expected_message) in cases.items():
        module = 'VerificationControls.' + name
        path = controls / (name + '.lean')
        path.write_text(source)
        try:
            check_proof_tokens(project, [module])
        except RuntimeError as error:
            source_rejection = str(error)
        else:
            raise RuntimeError(f'Forbidden source token accepted in {name} control')
        olean = project / '.lake/build/lib/lean/VerificationControls' / (name + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        code, out, err = command([lake, 'env', 'lean', '-DwarningAsError=true', path.relative_to(project),
                                  '-o', olean.relative_to(project)], project, logs,
                                 'control-compile-' + name, env, expect_success=False)
        if mode == 'compile':
            require(code != 0 and expected_message in out + err, f'{name} control was not rejected')
        else:
            require(code == 0, f'Control did not compile: {name}')
            check = controls / ('Check' + name + '.lean')
            directive = '#audit_modules' if mode == 'audit-all' else '#audit_kernel_modules'
            check.write_text(f'import {module}\nimport Verification.ClosureAudit\n'
                             f'{directive} [{module}] "control-{name}.json"\n')
            code, out, err = command([lake, 'env', 'lean', '-DwarningAsError=true', check.relative_to(project)],
                                     project, logs, 'control-audit-' + name, env, expect_success=False)
            require(code != 0 and expected_message.lower() in (out + err).lower(),
                    f'Control was not rejected as intended: {name}')
            audit = json.loads((project / ('control-' + name + '.json')).read_text())
            require(audit['failures'], f'Negative control lacks its complete audit evidence: {name}')
        results[name] = {'outcome': 'rejected as intended', 'mechanism': mode,
                         'independent_source_rejection': source_rejection}
    source_name = manifest['mutation_control_file']
    source = project / source_name
    original = source.read_bytes()
    try:
        source.write_bytes(original + b'\n-- changed frozen input\n')
        try:
            verify_frozen(project, manifest)
        except RuntimeError as error:
            require(str(error) == 'Frozen source mismatch: ' + source_name,
                    f'Unexpected mutation rejection: {error}')
            results['FrozenMutation'] = {'outcome': 'rejected as intended', 'error': str(error)}
        else:
            raise RuntimeError('Manifest guard accepted changed frozen source')
    finally:
        source.write_bytes(original)
    try:
        verify_frozen(project, manifest)
    except RuntimeError as error:
        require(str(error).startswith('Unaccounted Lean source inventory:'),
                f'Unexpected unlisted-module rejection: {error}')
        results['UnlistedModule'] = {'outcome': 'rejected as intended', 'error': str(error)}
    else:
        raise RuntimeError('Source inventory guard accepted unlisted control modules')
    write_json(project.parent / 'negative-controls.json', results)
    return results


def run(args, source, work, summary):
    logs, project = work / 'logs', work / 'project'
    logs.mkdir()
    project.mkdir()
    manifest_path = source / 'verification-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    require(isinstance(manifest['expected_proof_declarations'], dict),
            'A reviewed exact compiled declaration inventory must be frozen')
    summary['verification_manifest_sha256'] = sha256(manifest_path)
    source_hashes = verify_frozen(source, manifest)
    check_proof_tokens(source, manifest['proof_modules'])
    summary['source_sha256'] = source_hashes
    for name in manifest['frozen_files']:
        target = project / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / name, target)
    shutil.copy2(manifest_path, project / manifest_path.name)
    env = os.environ.copy()
    for key in list(env):
        if key.startswith(('GIT_', 'LEAN_', 'LAKE_')):
            env.pop(key)
    env.update({'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': os.devnull,
                'GIT_NO_REPLACE_OBJECTS': '1', 'GIT_NO_LAZY_FETCH': '1',
                'GIT_TERMINAL_PROMPT': '0'})
    if args.lean_bin:
        env['PATH'] = str(args.lean_bin.resolve()) + os.pathsep + env.get('PATH', '')
    lake, lean = (shutil.which(exe, path=env['PATH']) for exe in ('lake', 'lean'))
    require(lake and lean, 'Lean and Lake must be installed')
    _, version, _ = command([lean, '--version'], project, logs, 'lean-version', env)
    require(re.search(r'\bversion 4\.19\.0,', version), 'Wrong Lean version')
    require('6caaee842e94' in version, 'Wrong Lean 4.19.0 release commit')
    _, lake_version, _ = command([lake, '--version'], project, logs, 'lake-version', env)
    require('Lean version 4.19.0' in lake_version, 'Wrong Lake Lean version')
    summary['lean_version'], summary['lake_version'] = version.strip(), lake_version.strip()
    packages = project / '.lake/packages'
    packages.mkdir(parents=True)
    dependencies = json.loads((project / 'lake-manifest.json').read_text())['packages']
    if args.stock_mathlib:
        stock = args.stock_mathlib.resolve()
        if platform.system() == 'Darwin':
            command(['/bin/cp', '-cR', stock, packages / 'mathlib'], project, logs, 'copy-stock', env)
        else:
            shutil.copytree(stock, packages / 'mathlib', symlinks=True)
        for p in dependencies:
            if p['name'] != 'mathlib':
                (packages / p['name']).symlink_to(Path('mathlib/.lake/packages') / p['name'])
        summary['stock_binary_cache_mode'] = 'copied from explicitly supplied offline stock'
    else:
        for p in dependencies:
            repo = packages / p['name']
            command(['git', 'clone', '--no-checkout', p['url'], repo], project, logs,
                    'clone-' + p['name'], env)
            command(['git', '-C', repo, 'checkout', '--detach', p['rev']], project, logs,
                    'checkout-' + p['name'], env)
        summary['stock_binary_cache_mode'] = 'downloaded by pinned Mathlib cache tool'
    summary['stock_tracked_file_counts'] = verify_stock(project, logs, env, 'before-build')
    if not args.stock_mathlib:
        command([lake, 'exe', 'cache', 'get'], project, logs, 'stock-cache-download', env)
    require(not (project / '.lake/build').exists(), 'Fresh project contains unexpected local artifacts')
    command([lake, 'build'], project, logs, 'fresh-project-build', env)
    for name in manifest['lean_files']:
        output = project / '.lake/build/lib/lean' / Path(name).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        command([lake, 'env', 'lean', '-DwarningAsError=true', name, '-o', output.relative_to(project)],
                project, logs, 'replay-' + name.replace('/', '-'), env)
    # The generated driver is kept outside the authored source inventory. It
    # imports every compiled infrastructure module, including ClosureCheck.
    driver = project / 'GeneratedInfrastructureInventory.lean'
    driver.write_text(''.join('import ' + module + '\n' for module in manifest['inspection_modules']) +
        '\n#inspect_modules [' + ', '.join(manifest['inspection_modules']) +
        '] "infrastructure-audit.json"\n')
    command([lake, 'env', 'lean', '-DwarningAsError=true', driver.name], project, logs,
            'inventory-all-compiled-infrastructure', env)
    summary['proof_audit'] = inspect_audit(project / 'closure-audit.json',
        manifest['proof_modules'], manifest['expected_proof_declarations'])
    proof_inventory = json.loads((project / 'closure-audit.json').read_text())['declarations']
    require(sorted(d['name'] for d in proof_inventory if d['unsafe']) ==
            manifest['expected_compiler_runtime_roots'], 'Compiler-runtime root inventory changed')
    summary['infrastructure_inventory'] = inspect_audit(project / 'infrastructure-audit.json',
        manifest['inspection_modules'], strict=False)
    summary['imported_compiled_module_count'] = record_artifacts(project, logs, env, lake, lean)
    summary['controls'] = rejection_controls(project, logs, env, lake, manifest)
    for name in manifest.get('auxiliary_python_files', []):
        require(name in manifest['frozen_files'], f'Unfrozen mathematical auxiliary: {name}')
        command([sys.executable, name], project, logs,
                'auxiliary-' + name.replace('/', '-'), env)
    summary['independently_executed_auxiliary_files'] = manifest.get('auxiliary_python_files', [])
    require(source_hashes == verify_frozen(source, manifest), 'Original source changed during verification')
    require(sha256(manifest_path) == summary['verification_manifest_sha256'], 'Manifest changed during verification')
    for name, digest in source_hashes.items():
        require(sha256(project / name) == digest, f'Working source changed: {name}')
    require(verify_stock(project, logs, env, 'after-build') == summary['stock_tracked_file_counts'],
            'Dependency tracked file counts changed')
    summary['output_sha256'] = {str(p.relative_to(work)): sha256(p) for p in work.rglob('*')
        if p.is_file() and '.lake/packages' not in str(p.relative_to(work)) and '.git' not in p.parts}
    summary['status'] = 'pass'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--stock-mathlib', type=Path)
    parser.add_argument('--work-dir', type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    if args.work_dir:
        require(not args.work_dir.resolve().is_relative_to(source),
                'Use a work directory outside the frozen source directory')
        args.work_dir.mkdir(parents=True, exist_ok=False)
    work = (args.work_dir or Path(tempfile.mkdtemp(prefix='tlmc1473-verification-'))).resolve()
    summary = {'status': 'failed', 'started_utc': datetime.now(timezone.utc).isoformat(),
               'source': str(source), 'work': str(work),
               'scope': 'Fresh local build and direct warningAsError replay of every authored Lean '
                   'file, including configuration and verification tools. Complete proof module '
                   'declaration inventory and type/body/opaque/recursor dependency graph. Every '
                   'safe kernel declaration has only standard axioms and no unsafe/missing dependency. '
                   'Compiler-generated unsafe runtime roots are explicitly inventoried separately; '
                   'authored unsafe definitions are prohibited by the source guard. '
                   'Infrastructure is inventoried separately and is not mathematical evidence. '
                   'Pinned stock binaries may be reused; stock modules are not all rebuilt.'}
    try:
        run(args, source, work, summary)
    except Exception as error:
        summary['error'] = str(error)
        summary['traceback'] = traceback.format_exc()
        raise
    finally:
        summary['finished_utc'] = datetime.now(timezone.utc).isoformat()
        write_json(work / 'verification.json', summary)
        print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
