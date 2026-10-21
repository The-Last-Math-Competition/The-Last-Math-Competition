#!/usr/bin/env python3
"""Independent finite sanity checks and source/audit-integrity checks.
The unbounded polynomial proofs are checked by Lean, not by these finite tests.
"""
from pathlib import Path
from itertools import product,combinations
import hashlib,json,re,sys
ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'theorem-manifest.json').read_text())
assert {p.stem for p in ROOT.glob('*.lean')} == set(manifest['modules']) | {'Audit','OriginAudit'}
for m in manifest['modules']:
    s=(ROOT/(m+'.lean')).read_text()
    s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
    s=re.sub(r'--[^\n]*','',s)
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b',s),m
    assert 'ofReduceBool' not in s,m
allnames=manifest['theorems']
audit=(ROOT/'Audit.lean').read_text()
assert re.findall(r'^#check (\S+)$',audit,re.M)==allnames
assert re.findall(r'^#print axioms (\S+)$',audit,re.M)==allnames
assert sum(len(re.findall(r'\btheorem\s+',re.sub(r'/\-.*?\-/','',(ROOT/(m+'.lean')).read_text(),flags=re.S))) for m in manifest['modules'])==len(allnames)
source=(ROOT/'source.md').read_bytes()
blob=hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()
assert blob=='c13f3ca1b54b390533587ff148a83be0d1800bf8'
gate=json.loads((ROOT/'eligibility.json').read_text())
assert gate['metadata']['proven']==gate['metadata']['disproven']=='false'
assert gate['bounded_title_body_hits']==[] and gate['all_pr_count']==1062
for f in ['pr-padded.json','pr-unpadded.json']:
    assert json.loads((ROOT/f).read_text())['structuredContent']['issues']==[]

def graph_checks(n):
    edges=list(combinations(range(n),2))
    matching=max(len(s) for k in range(len(edges)+1) for s in combinations(edges,k)
                 if len({x for e in s for x in e})==2*len(s))
    bipartite=any(all(c[a]!=c[b] for a,b in edges) for c in product(range(2),repeat=n))
    cycle=any(all(tuple(sorted((p[i],p[(i+1)%len(p)]))) in edges for i in range(len(p)))
        for k in range(3,n+1) for p in __import__('itertools').permutations(range(n),k))
    return {'matching':matching,'bipartite':bipartite,'forest':not cycle}
assert graph_checks(2)=={'matching':1,'bipartite':True,'forest':True}
assert graph_checks(3)=={'matching':1,'bipartite':False,'forest':False}
zero=frozenset()
def add(a,b):return a^b
def shift(a,axis):return frozenset(tuple(t[i]+(i==axis) for i in range(3)) for t in a)
def drop(a,axis):return frozenset(tuple(t[i]-(i==axis) for i in range(3)) for t in a if t[axis]>0)
def d1(v):
    a,b,c=v;return shift(shift(a,1),0)^shift(shift(b,2),0)^shift(shift(c,2),1)
def d2(v):
    u,v=v;return (shift(u^v,2),shift(u,1),shift(v,0))
mon=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
polys=[frozenset(m for i,m in enumerate(mon) if (bits>>i)&1) for bits in range(16)]
kernels=0
for v in product(polys,repeat=3):
    if not d1(v):
        kernels+=1
        assert d2((drop(v[1],1),drop(v[2],0)))==v
for u in product(polys,repeat=2):assert not d1(d2(u))
assert len({d2(u) for u in product(polys,repeat=2)})==256
assert max(d-i for i,d in [(0,2)])==2
assert max(d-i for i,d in [(0,0),(1,2),(2,3)])==1
if '--audit' in sys.argv:
    log=(ROOT/'verification/all-theorem-axioms.log').read_text()
    checked=set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",log))
    assert checked==set(allnames),(len(checked),len(allnames),set(allnames)-checked)
    allowed={'propext','Classical.choice','Quot.sound'}
    for listing in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S):
        assert {x.strip() for x in listing.split(',') if x.strip()}<=allowed,listing
    assert not re.search(r'sorryAx|ofReduceBool|declaration uses',log)
    origin=(ROOT/'verification/origin-theorem-axioms.log').read_text()
    assert 'PASS: independently audited 554 authored theorems among 758 authored constants' in origin
print(json.dumps({'status':'PASS','theorems':len(allnames),'modules':len(manifest['modules']),
    'source_blob':blob,'K2':graph_checks(2),'K3':graph_checks(3),
    'finite_sanity_degree_at_most':1,'triangle_triples_checked':4096,'kernel_triples':kernels,
    'note':'Finite Python checks are independent sanity checks, not substitutes for arbitrary-polynomial Lean proofs.'},indent=2))
