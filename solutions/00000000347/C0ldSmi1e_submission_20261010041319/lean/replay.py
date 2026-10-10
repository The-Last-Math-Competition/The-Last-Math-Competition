#!/usr/bin/env python3
"""Replay the complete proof and axiom audit without changing shared Mathlib.

Example (run after initializing the Lean project and obtaining Mathlib's cache):
  python3 replay.py --project /path/to/proof --mathlib /path/to/mathlib \
    --lean-bin /path/to/lean-4.19.0/bin --work /path/to/cf-build

Only --work and the project's .lake/build/lib/lean proof objects are written.
Existing Mathlib object files are linked read-only by convention; no stock files
are compiled in place or modified. Logs preserve every attempted command/result.
"""
import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project', type=pathlib.Path, required=True)
parser.add_argument('--mathlib', type=pathlib.Path, required=True)
parser.add_argument('--lean-bin', type=pathlib.Path, required=True)
parser.add_argument('--work', type=pathlib.Path, required=True)
args = parser.parse_args()
project = args.project.resolve()
mathlib = args.mathlib.resolve()
lean_bin = args.lean_bin.resolve()
work = args.work.resolve()
overlay = work / 'stock-overlay'
logs = work / 'logs'
overlay.mkdir(parents=True, exist_ok=True)
logs.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['PATH'] = str(lean_bin) + os.pathsep + env.get('PATH', '')
path_query = subprocess.run([str(lean_bin / 'lake'), 'env', 'printenv', 'LEAN_PATH'],
                            cwd=project, env=env, text=True, capture_output=True)
(logs / 'lake-path.stdout').write_text(path_query.stdout)
(logs / 'lake-path.stderr').write_text(path_query.stderr)
if path_query.returncode:
    sys.stderr.write(path_query.stderr)
    sys.exit(path_query.returncode)
search_paths = [str((project / p).resolve()) for p in path_query.stdout.strip().split(os.pathsep)]
# Lean resolves a namespace from one search root. Link every cached Mathlib olean
# into this overlay so that both cached and newly compiled modules are available.
stock_objects = mathlib / '.lake/build/lib/lean'
for src in stock_objects.rglob('*.olean'):
    dst = overlay / src.relative_to(stock_objects)
    dst.parent.mkdir(parents=True, exist_ok=True)
    if not dst.exists() and not dst.is_symlink():
        dst.symlink_to(src)
env['LEAN_PATH'] = os.pathsep.join([str(overlay), *search_paths])

def compile_one(source, output, source_root):
    output.parent.mkdir(parents=True, exist_ok=True)
    # Never permit the compiler to follow an output link into stock Mathlib.
    if output.is_symlink():
        raise RuntimeError('Refusing to compile through output symlink: ' + str(output))
    command = [str(lean_bin / 'lean'), '-DwarningAsError=true',
               '-R', str(source_root), '-o', str(output), str(source)]
    stamp = str(time.time_ns())
    record = {'argv': command, 'cwd': str(project), 'LEAN_PATH': env['LEAN_PATH'],
              'source': str(source),
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
    (logs / (stamp + '.command.json')).write_text(json.dumps(record, indent=2) + '\n')
    completed = subprocess.run(command, cwd=project, env=env,
                               text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT)
    (logs / (stamp + '.log')).write_text(completed.stdout)
    (logs / (stamp + '.exit')).write_text(str(completed.returncode) + '\n')
    print(completed.stdout, end='')
    print(str(source) + ': exit ' + str(completed.returncode), flush=True)
    if completed.returncode:
        sys.exit(completed.returncode)

# These are stock Mathlib source files, compiled unchanged, in dependency order.
for module in ('Mathlib.Dynamics.FixedPoints.Topology',
               'Mathlib.Topology.MetricSpace.Contracting'):
    rel = pathlib.Path(*module.split('.'))
    source = mathlib / rel.with_suffix('.lean')
    output = overlay / rel.with_suffix('.olean')
    if output.is_symlink():
        continue  # This Mathlib cache already contains the module.
    compile_one(source, output, mathlib)

for module in ('WordCombinatorics', 'Mechanical', 'CFRealization', 'Proof', 'AxiomAudit'):
    compile_one(project / (module + '.lean'),
                project / '.lake/build/lib/lean' / (module + '.olean'), project)
source_hashes = {str(p.relative_to(project)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in sorted(project.iterdir())
                 if p.is_file() and p.suffix in ('.lean', '.tex', '.py', '.json')}
source_hashes['lean-toolchain'] = hashlib.sha256((project / 'lean-toolchain').read_bytes()).hexdigest()
(logs / 'source-config-sha256.json').write_text(json.dumps(source_hashes, indent=2) + '\n')
print('Build verified. Prefix LEAN_PATH with: ' + str(overlay))
