#!/usr/bin/env python3
"""Independent read-only rehash/receipt cross-check for the completed 7302 run."""
import collections
import ast
import hashlib
import json
import os
import re
from pathlib import Path

R = Path(__file__).resolve().parent.parent
D = R.parent
E = R / 'independent-review/engineering'
def load(p):
    return json.loads(p.read_text())
def sha(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()
def bytes_at(p):
    return os.readlink(p).encode() if p.is_symlink() else p.read_bytes()
def save(name, data):
    (R/'independent-review'/name).write_text(json.dumps(data, indent=2)+'\n')

summary = load(E/'summary.json')
assert summary['status'] in {'PASS', 'PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION'}
freeze = load(R/'frozen-review-manifest.json')
ready = load(R/'verification-readiness.json')
assert sha(E/'selected-manifest.json') == sha(R/'frozen-review-manifest.json') == summary['frozen_manifest_sha256']
assert load(E/'frozen-manifest.json') == freeze
assert sha(R/'author/verification/FROZEN_SOURCES.json') == freeze['author_manifest_sha256']
copies = []
for name, digest in freeze['files'].items():
    author = R/'author'/('verification' if name == 'AxiomAudit.lean' else 'lean')/name
    for label, p in [('author', author), ('review_source', R/'review-source/lean'/name), ('private_replay', E/'project'/name)]:
        assert p.is_file() and not p.is_symlink() and sha(p) == digest, (label, name)
        copies.append({'copy': label, 'file': name, 'sha256': digest})
assert {p.name for p in (R/'review-source/lean').iterdir()} == set(freeze['files'])
for name, digest in ready['tool_hashes'].items():
    assert sha(D/'verification-tools-v2'/name) == digest
assert sha(E/'driver.py.txt') == ready['tool_hashes']['verify.py']
assert sha(E/'project/Verification/ClosureAudit.lean') == ready['tool_hashes']['templates/ClosureAudit.lean.txt']
assert load(E/'active-source-token-audit.json') == []
pins = load(E/'expected-pin-identities.json')
assert Path(pins['directory']) == R/'expected-pins'
assert pins['sha256'] == ready['expected_pins'] == summary['expected_pins']
for name, digest in pins['sha256'].items():
    assert sha(R/'expected-pins'/name) == digest == freeze['files'][name]

runtime = load(E/'runtime-identities.json')
for name, digest in runtime.items():
    assert sha(Path(name)) == digest, name
build = load(R/'independent-stock-build/receipt.json')
assert build['exit_code'] == 0
assert sha(R/'independent-stock-build/stdout.txt') == build['stdout_sha256']
assert sha(R/'independent-stock-build/stderr.txt') == build['stderr_sha256']
assert not (R/'independent-stock-build/stderr.txt').read_text()
built = [line.split('Built ',1)[1] for line in (R/'independent-stock-build/stdout.txt').read_text().splitlines() if 'Built ' in line]
assert set(built) == set(load(R/'independent-stock-preparation.json')['author_additional_cached_modules'])
assert len(built) == 3

manifest = load(R/'expected-pins/lake-manifest.json')
stock = Path(build['cwd'])
assert stock == Path(load(R/'independent-stock-preparation.json')['target'])
packages = E/'project/.lake/packages'
identities = load(E/'package-identities.json')
assert identities == summary['package_identities']
assert len(identities) == len(manifest['packages']) == 9
specs = {s['name']: s for s in manifest['packages']}
source_counts = {}
for identity in identities:
    name = identity['package']
    assert identity['revision'] == specs[name]['rev']
    p = E/'stock'/(name+'.json')
    assert sha(p) == identity['inventory_sha256']
    rows = load(p)
    assert len(rows) == identity['tracked_files']
    origin = stock if name == 'mathlib' else stock/'.lake/packages'/name
    for row in rows:
        original = bytes_at(origin/row['file'])
        copied = bytes_at(packages/name/row['file'])
        assert original == copied
        assert hashlib.sha256(original).hexdigest() == row['sha256']
        assert hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest() == row['git_blob']
    source_counts[name] = len(rows)
index_checks = load(E/'stock-index-stability.json')
for row in index_checks:
    origin = stock if row['package'] == 'mathlib' else stock/'.lake/packages'/row['package']
    assert row['unchanged'] is True and row['before'] == row['after'] == sha(origin/'.git/index')

imports = load(E/'import-identities.json')
assert len(imports) == summary['import_identity_count']
assert len({r['module'] for r in imports}) == len(imports)
stock_sources = {name: {r['file']: r for r in load(E/'stock'/(name+'.json'))} for name in specs}
cache = {name: load(E/'stock'/(name+'-cache.json')) for name in specs}
leanbin = Path(build['command'][0]).parent
roots = [('owned', E/'project/.lake/build/lib/lean')]
roots += [(name, packages/name/'.lake/build/lib/lean') for name in specs]
roots += [('Lean-runtime', leanbin.parent/'lib/lean')]
import_counts = collections.Counter()
for row in imports:
    name, package = row['module'], row['package']
    relative = Path(*name.split('.')).with_suffix('.olean')
    candidates = [(label, root/relative) for label, root in roots if (root/relative).is_file()]
    assert candidates == [(package, Path(row['resolved_path']))], name
    assert sha(Path(row['resolved_path'])) == row['olean_sha256'], name
    source_rel = relative.with_suffix('.lean')
    if package == 'owned':
        assert sha(E/'project'/source_rel) == row['source_sha256']
    elif package != 'Lean-runtime':
        origin = stock if package == 'mathlib' else stock/'.lake/packages'/package
        assert sha(origin/'.lake/build/lib/lean'/relative) == row['olean_sha256'] == cache[package][str(relative)]
        assert sha(origin/source_rel) == row['source_sha256'] == stock_sources[package][str(source_rel)]['sha256']
    import_counts[package] += 1
for name in ['lake-build-outputs.json', 'replay-build-outputs.json', 'audited-build-outputs.json']:
    for rel, digest in load(E/name).items():
        assert sha(E/'project/.lake/build/lib/lean'/rel) == digest, (name, rel)

receipts = []
git_heads = {}
git_clean = set()
git_trees = {}
for p in sorted((E/'receipts').glob('*.json')):
    row = load(p)
    assert sha(p.with_suffix('.stdout')) == row['stdout_sha256']
    assert sha(p.with_suffix('.stderr')) == row['stderr_sha256']
    assert row['effective_argv'] == row['argv']
    if row['expected_exit'] == 0:
        assert row['exit_code'] == 0
    else:
        assert row['expected_exit'] == 'nonzero' and row['exit_code'] != 0
    for name, digest in row['active_source_hashes'].items():
        assert sha(E/'project'/name) == digest, (p.name, name)
    argv = row['argv']
    if argv[:3] == ['/usr/bin/git', 'rev-parse', 'HEAD']:
        git_heads[Path(row['cwd']).name] = p.with_suffix('.stdout').read_text().strip()
    elif argv[:3] == ['/usr/bin/git', 'status', '--porcelain']:
        assert not p.with_suffix('.stdout').read_bytes()
        git_clean.add(Path(row['cwd']).name)
    elif argv[:4] == ['/usr/bin/git', 'ls-tree', '-r', '-z']:
        rows = p.with_suffix('.stdout').read_text().split('\0')
        git_trees[Path(row['cwd']).name] = {r.split('\t',1)[1]:r.split('\t',1)[0].split()[2] for r in rows if r}
    receipts.append({'receipt':p.name, 'argv':row['argv'], 'exit_code':row['exit_code'], 'expected_exit':row['expected_exit']})
expected_modules = sorted(Path(n).stem for n in freeze['files'] if n.endswith('.lean') and n != 'lakefile.lean')
for name, spec in specs.items():
    key = 'stock7302' if name == 'mathlib' else name
    assert git_heads[key] == spec['rev'] and key in git_clean
    assert git_trees[key] == {rel: row['git_blob'] for rel,row in stock_sources[name].items()}
assert summary['modules'] == expected_modules
strict = {r['argv'][-1] for r in receipts if len(r['argv']) > 1 and r['argv'][0] == str(leanbin/'lean') and '-DwarningAsError=true' in r['argv'] and r['exit_code'] == 0}
assert {m+'.lean' for m in expected_modules} <= strict
assert any(r['argv'] == [str(leanbin/'lake'), 'env', 'lean', '-DwarningAsError=true', 'lakefile.lean'] and r['exit_code'] == 0 for r in receipts)
assert any(r['argv'] == [str(leanbin/'lake'), '--no-cache', '--wfail', 'build'] and r['exit_code'] == 0 for r in receipts)
assert len(load(E/'replay-build-outputs.json')) == len(expected_modules) == 5
assert len(load(E/'lake-build-outputs.json')) == 4
assert len(load(E/'audited-build-outputs.json')) == 6

controls = load(E/'control-results.json')
assert controls == summary['controls']
assert {r['fixture'] for r in controls} == {'Good','Axiom','Transitive','Sorry','Native','Unsafe'}
tree = ast.parse((D/'verification-tools-v2/verify.py').read_text())
fixture_node = next(n.value for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='fixtures' for t in n.targets))
fixtures = ast.literal_eval(fixture_node)
for control in controls:
    name = control['fixture']
    assert (E/'project/ReviewControls'/(name+'.lean')).read_text() == fixtures[name]
    data = load(E/('control-'+name+'.json'))
    assert data['kernel_roots_only'] == (name == 'Good')
    graph = {r['name']:r for r in data['dependency_graph']}
    for root in data['declarations']:
        seen, pending = set(), [root['name']]
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            node = graph[current]
            edges = set(node['type_dependencies']) | set(node['body_dependencies']) | set(node['recursor_dependencies']) | set(node['inductive_dependencies'])
            assert edges == set(node['dependencies'])
            pending.extend(edges-seen)
        assert seen == set(root['closure'])
        assert {n for n in seen if graph[n]['kind']=='axiom'} == set(root['axioms'])
        assert {n for n in seen if graph[n]['unsafe']} == set(root['unsafe_dependencies'])
    assert control['failures'] == data['failures']
    assert control['expected_rejected'] == (name != 'Good')
    if name == 'Good':
        assert not data['failures']
    elif name == 'Unsafe':
        assert any('unsafe dependency' in s for s in data['failures'])
    else:
        assert any('forbidden axiom' in s for s in data['failures'])
assert any(r['argv'][-1] == 'ReviewControls/Sorry.lean' and '-DwarningAsError=true' in r['argv'] and r['exit_code'] != 0 for r in receipts)
axiom_prints = re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]", (E/'receipts/0045.stdout').read_text(), re.S)
assert [n for n,_ in axiom_prints] == freeze['capstones']
assert all({s.strip() for s in axioms.split(',')} <= {'propext','Classical.choice','Quot.sound'} for _,axioms in axiom_prints)
audit = load(E/'declaration-audit.json')
assert audit['failures'] == summary['audit_failures'] == []
assert audit['local_declaration_count'] == summary['local_declaration_count']
assert audit['closure_declaration_count'] == summary['closure_declaration_count']
assert audit['requested_modules'] == expected_modules
assert set(audit['imported_modules']) == {r['module'] for r in imports}
assert set(audit['permitted_axioms']) == {'propext','Classical.choice','Quot.sound'}
decls = {r['name']:r for r in audit['declarations']}
assert freeze['capstones'] == summary['capstones'] and len(freeze['capstones']) == 21
for capstone in freeze['capstones']:
    assert capstone in decls and not decls[capstone]['unsafe'] and decls[capstone]['trust_enforced']
safe = [r for r in decls.values() if not r['unsafe']]
assert all(r['trust_enforced'] and not r['unsafe_dependencies'] and set(r['axioms']) <= set(audit['permitted_axioms']) for r in safe)
helpers = [r for r in decls.values() if r['unsafe']]
assert helpers == load(E/'runtime-helper-inventory.json')
assert len(helpers) == summary['runtime_helper_count']
record = {'status':'PASS', 'source_copy_hash_checks':len(copies), 'source_copies':copies,
          'tool_hash_checks':len(ready['tool_hashes']), 'runtime_identity_checks':len(runtime),
          'package_source_counts':source_counts, 'total_pinned_source_files':sum(source_counts.values()),
          'stock_index_checks':len(index_checks), 'import_identity_counts':dict(import_counts),
          'import_identity_total':len(imports), 'receipts':receipts, 'receipt_count':len(receipts),
          'strict_owned_source_replays':expected_modules, 'strict_lake_config_replay':True,
          'lake_default_build_outputs':4, 'replay_build_outputs':5, 'audit_build_outputs':6,
          'targeted_stock_build_modules':built, 'controls':controls, 'owned_roots':len(decls),
          'safe_roots':len(safe), 'unsafe_runtime_helpers':len(helpers), 'capstones':len(freeze['capstones']),
          'reachable_declarations':audit['closure_declaration_count'],
          'limits':['Rehashes and receipt checks corroborate the completed run; they do not constitute a second full build.',
                    'Pinned cached dependencies were not all rebuilt; only the three listed missing imports were freshly rebuilt.',
                    'Lean runtime was not bootstrapped; PATH wrappers are not operating-system network isolation.',
                    'Semantic proof interpretation, report, PDF, eligibility and publication are outside this engineering check.']}
save('engineering-checks.json',record)
print(json.dumps({k:v for k,v in record.items() if k not in {'source_copies','receipts','controls','limits'}},indent=2))
