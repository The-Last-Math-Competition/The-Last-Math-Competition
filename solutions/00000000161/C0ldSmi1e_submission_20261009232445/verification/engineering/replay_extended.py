#!/usr/bin/env python3
"""Replay engineering checks against an already-provisioned pinned Lean project.

Use the pinned Lean 4.19.0 binaries on PATH. Dependencies must already exist.
Only the selected project's own generated .lake/build directory is removed.
No network operation, source modification, or dependency build cleanup occurs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

MANIFEST = '56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
SOURCES = ['lakefile.lean', 'Conjecture161/Arithmetic.lean', 'Conjecture161.lean', 'Audit.lean']

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-root', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    project, output = args.project_root.resolve(), args.output_dir.resolve()
    helpers = Path(__file__).resolve().parent
    output.mkdir(parents=True, exist_ok=True)
    assert not (output/'commands.jsonl').exists(), 'Choose a fresh output directory'
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)

    def save(name, data):
        (output/name).write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')

    def run(label, argv):
        argv = list(map(str, argv))
        start = time.time()
        p = subprocess.run(argv, cwd=project, env=env, capture_output=True)
        stdout, stderr = output/(label+'.stdout'), output/(label+'.stderr')
        stdout.write_bytes(p.stdout)
        stderr.write_bytes(p.stderr)
        with (output/'commands.jsonl').open('a') as f:
            f.write(json.dumps({'argv':argv, 'cwd':str(project), 'exit_code':p.returncode,
                'seconds':time.time()-start, 'stdout_sha256':digest(stdout),
                'stderr_sha256':digest(stderr), 'label':label})+'\n')
        print(label, p.returncode, flush=True)
        assert p.returncode == 0, f'Failed command: {label}'
        return p.stdout.decode()

    assert (project/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.19.0'
    assert digest(project/'lake-manifest.json') == MANIFEST
    version = run('lean_version', ['lean', '--version'])
    assert 'version 4.19.0,' in version
    manifest = json.loads((project/'lake-manifest.json').read_text())
    before = {s:digest(project/s) for s in SOURCES+['lean-toolchain','lake-manifest.json','verify.py']}
    for s in SOURCES:
        assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b', (project/s).read_text()), s

    def dependency_snapshot(phase):
        result = {}
        for package in manifest['packages']:
            name = package['name']
            path = project/'.lake/packages'/name
            rev = run(phase+'_'+name+'_rev', ['git','-C',path,'rev-parse','HEAD']).strip()
            assert rev == package['rev'], name
            run(phase+'_'+name+'_diff', ['git','-C',path,'diff','--no-ext-diff','--exit-code','HEAD','--'])
            other = run(phase+'_'+name+'_untracked', ['git','-C',path,'ls-files','--others','--exclude-standard'])
            assert not other.strip(), f'Untracked dependency files: {name}'
            files = run(phase+'_'+name+'_files', ['git','-C',path,'ls-files','-z']).split('\0')
            result[name] = {'revision':rev, 'files':{f:digest(path/f) for f in files if f and (path/f).is_file()}}
        save(phase+'_dependencies.json', result)
        return result

    dep_before = dependency_snapshot('before')
    build = project/'.lake/build'
    assert not build.is_symlink(), 'Refusing a symlinked project build directory'
    if build.exists():
        shutil.rmtree(build)
    assert not build.exists()
    run('clean_build', ['lake','build'])
    for source in SOURCES:
        run('strict_'+source.replace('/','_').replace('.','_'), ['lake','env','lean','-DwarningAsError=true',source])
    types = run('full_types_axioms', ['lake','env','lean','-DwarningAsError=true',helpers/'IndependentAudit.lean'])
    closure = run('kernel_closure', ['lake','env','lean','-DwarningAsError=true',helpers/'Discover.lean'])
    expected = set(re.findall(r'^#check (\S+)$', (helpers/'IndependentAudit.lean').read_text(), re.M))
    assert len(expected) == 29
    audited = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", types):
        audited[name] = set(x.strip() for x in axioms.split(',') if x.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", types):
        audited[name] = set()
    assert set(audited) == expected
    assert all(a <= ALLOWED for a in audited.values())
    roots = set(re.findall(r'^AUTHORED_DECL (\S+) MODULE', closure, re.M))
    excluded = set(re.findall(r'^COMPILER_RUNTIME_ONLY (\S+)$', closure, re.M))
    assert excluded == {'Conjecture161.primeIndexInhabited._cstage1', 'Conjecture161.primeIndexInhabited._cstage2'}
    assert roots-excluded == expected
    assert set(re.findall(r'^CLOSURE_AXIOM (\S+) unsafe=false$', closure, re.M)) == ALLOWED
    assert not re.search(r'^DECL_KIND .* def Lean.DefinitionSafety\.(unsafe|partial)$', closure, re.M)
    assert not re.search(r'^(DECL_KIND|CLOSURE_AXIOM) .*unsafe=true$', closure, re.M)
    count = int(re.search(r'^CLOSURE_COUNT (\d+)$', closure, re.M).group(1))
    assert dependency_snapshot('after') == dep_before
    assert {s:digest(project/s) for s in before} == before
    save('result.json', {'status':'PASS', 'scope':'Independent Lean engineering verification only',
         'logical_declarations':sorted(expected), 'logical_declaration_count':len(expected),
         'compiler_runtime_only':sorted(excluded), 'closure_constant_count':count,
         'axioms':sorted(ALLOWED), 'unsafe_or_partial_in_logical_closure':False,
         'source_hashes':before, 'dependencies_unchanged':True})
    print('PASS: clean build, every submitted Lean source strict, all 29 logical declarations and their closure.')

if __name__ == '__main__':
    main()
