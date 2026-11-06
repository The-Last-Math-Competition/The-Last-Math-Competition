"""Independent semantic/data audit; reads final Lean, never changes it."""
import hashlib
import itertools as it
import json
from pathlib import Path
import re

source = Path(__file__).resolve().parent.parent / 'lean/Main.lean'
text = source.read_text(encoding='utf-8')
vertices = range(9)
triples = list(it.combinations(vertices, 3))
masks = {name: int(re.search(r'def ' + name + r' : Hypergraph3.*?Nat.testBit (\d+)', text, re.S)[1]) for name in ('X', 'Y')}
edges = {name: {t for t in triples if mask >> (81*t[0] + 9*t[1] + t[2]) & 1} for name, mask in masks.items()}
for name, mask in masks.items():
    assert mask.bit_length() <= 729
    for a, b, c in it.product(vertices, repeat=3):
        assert bool(mask >> (81*a + 9*b + c) & 1) == (tuple(sorted((a,b,c))) in edges[name])

for name in ('X', 'Y'):
    displayed = re.search(r'def edges' + name + r' :.*?:=(.*?)(?=\ntheorem|\ndef)', text, re.S)[1]
    listed = [tuple(map(int, re.findall(r'\d+', group))) for group in re.findall(r'\{([^{}]+)\}', displayed)]
    assert len(listed) == 28 and len(set(listed)) == 28
    assert set(listed) == edges[name]

degree = {name: [sum(a in t for t in E) for a in vertices] for name, E in edges.items()}
codegree = {name: [[sum(a != b and a in t and b in t for t in E) for b in vertices] for a in vertices] for name, E in edges.items()}
for name in ('X', 'Y'):
    declared_deg = list(map(int, re.findall(r'\d+', re.search(r': doubleDegree ' + name + r' a = (.*?) a :=', text, re.S)[1])))
    declared_cg = list(map(int, re.findall(r'\d+', re.search(r': codegree ' + name + r' a b = (.*?) a b :=', text, re.S)[1])))
    assert declared_deg == [2*d for d in degree[name]]
    assert declared_cg == list(it.chain.from_iterable(codegree[name]))

card_results = []
for v, idx in enumerate([0,1,2,3,4,1,2,3,4]):
    block = re.search(r'def cardPerm' + str(idx) + r' :.*?toFun := !\[(.*?)\]', text, re.S)[1]
    p = list(map(int, block.split(',')))
    assert sorted(p) == list(vertices) and p[v] == v
    complement = set(vertices) - {v}
    assert {p[a] for a in complement} == complement
    for t in it.product(complement, repeat=3):
        assert (tuple(sorted(t)) in edges['X']) == (tuple(sorted(p[a] for a in t)) in edges['Y'])
    card_results.append({'deleted_X':v, 'deleted_Y':v, 'full_bijection':p})

# Independently exhaust all degree-compatible bijections, then all pair invariants.
classes = [tuple(a for a in vertices if degree['X'][a] == d) for d in sorted(set(degree['X']))]
degree_candidates = 0
pair_survivors = []
for choices in it.product(*(list(it.permutations(group)) for group in classes)):
    p = [None]*9
    for group, targets in zip(classes, choices):
        for a,b in zip(group, targets): p[a] = b
    degree_candidates += 1
    if any(codegree['X'][a][b] != codegree['Y'][p[a]][p[b]] for a,b in it.combinations(vertices,2)):
        continue
    bad = next((t for t in triples if (t in edges['X']) != (tuple(sorted(p[a] for a in t)) in edges['Y'])), None)
    assert bad is not None, 'Actual isomorphism found'
    pair_survivors.append({'bijection':p, 'distinguishing_triple':bad})

result = {'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'edge_counts':{k:len(v) for k,v in edges.items()}, 'degrees':degree,
    'all_729_ordered_triples_match_simple_uniform_hypergraphs':True,
    'displayed_edge_lists_match_bitmasks':True,
    'declared_degree_and_codegree_tables_match':True,
    'all_nine_card_isomorphisms_match_including_complements':True,
    'degree_compatible_bijections_exhausted':degree_candidates,
    'codegree_compatible_bijections':pair_survivors,
    'nonisomorphic':True,
    'non_steiner_witness': {'pair':[0,1], 'codegree_X':codegree['X'][0][1], 'codegree_Y':codegree['Y'][0][1]}}
out = Path(__file__).with_name('independent_result.json')
out.write_text(json.dumps(result, indent=2), encoding='utf-8')
print(json.dumps(result, indent=2))
