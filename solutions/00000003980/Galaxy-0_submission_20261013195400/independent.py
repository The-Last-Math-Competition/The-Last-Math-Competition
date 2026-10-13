#!/usr/bin/env python3
"""Independent serialization/semantics regression, not a proof oracle."""
from itertools import product
import random
B=('b',)
TRUTH=('i',B,B)

def encf(f):
    if f[0]=='b':return [1]
    if f[0]=='a':return [0]+[3]*f[1]+[4]
    return [2]+encf(f[1])+encf(f[2])
def size(f):
    if f[0]=='b':return 1
    if f[0]=='a':return f[1]+2
    return 1+size(f[1])+size(f[2])
def nv(f):
    if f[0]=='b':return 0
    if f[0]=='a':return f[1]+1
    return max(nv(f[1]),nv(f[2]))
def ev(f,v):
    if f[0]=='b':return False
    if f[0]=='a':return v[f[1]] if f[1]<len(v) else False
    return not ev(f[1],v) or ev(f[2],v)
def rows(n):
    if not n:return [[]]
    return [[b]+v for v in rows(n-1) for b in [False,True]]
def parsef(ts,pos):
    if pos>=len(ts):raise ValueError
    t=ts[pos];pos+=1
    if t==1:return B,pos
    if t==0:
        k=0
        while pos<len(ts) and ts[pos]==3:k+=1;pos+=1
        if pos>=len(ts) or ts[pos]!=4:raise ValueError
        return ('a',k),pos+1
    if t==2:
        a,pos=parsef(ts,pos);b,pos=parsef(ts,pos);return ('i',a,b),pos
    raise ValueError

def encode(tag,f,table):
    return [6 if tag else 5]+encf(f)+sum(([7]+[9 if b else 8 for b in v] for v in table),[])+[10]
def parse(ts):
    if not ts or ts[0] not in [5,6]:raise ValueError
    tag=ts[0]==6;f,pos=parsef(ts,1);table=[]
    while pos<len(ts) and ts[pos]==7:
        pos+=1;row=[]
        while pos<len(ts) and ts[pos] in [8,9]:row.append(ts[pos]==9);pos+=1
        table.append(row)
    if pos!=len(ts)-1 or ts[pos]!=10:raise ValueError
    return tag,f,table

def check(f,table):
    # Must not construct the exponential table until the size guard succeeds.
    if len(table)!=2**nv(f):return False
    return table==rows(nv(f)) and all(ev(f,v) for v in table)
def decode(tag,ts):
    try:t,f,table=parse(ts)
    except (ValueError,IndexError,RecursionError):return TRUTH
    return f if t==tag and check(f,table) else TRUTH

def translate(ts):
    if ts and ts[0] in [5,6]:return [11-ts[0]]+ts[1:]
    return ts.copy()

def verify():
    base=[B,('a',0),('a',1),('a',2)]
    level=base+[('i',a,b) for a in base for b in base]
    forms=base+[('i',a,b) for a in level for b in level]
    ncase=0;ntaut=0
    for f in forms:
        assert nv(f)<=size(f) and len(encf(f))==size(f)
        tt=rows(nv(f));taut=all(ev(f,list(v)) for v in product([False,True],repeat=nv(f)))
        assert check(f,tt)==taut
        ntaut+=taut
        variants=[tt,tt[:-1],tt+[[]],list(reversed(tt)),[v+[False] for v in tt],[]]
        for table in variants:
            for tag in [False,True]:
                ts=encode(tag,f,table)
                assert parse(ts)==(tag,f,table)
                assert len(ts)==2+size(f)+sum(len(v)+1 for v in table)
                assert len(translate(ts))==len(ts)
                assert translate(translate(ts))==ts
                assert decode(False,ts)==decode(True,translate(ts))
                assert decode(True,ts)==decode(False,translate(ts))
                if check(f,table):assert taut
                ncase+=1
    bad=0
    for n in range(5):
        for tup in product(range(11),repeat=n):
            ts=list(tup)
            assert decode(False,ts)==decode(True,translate(ts))
            assert decode(True,ts)==decode(False,translate(ts))
            bad+=1
    rng=random.Random(3980)
    for _ in range(2000):
        ts=encode(bool(rng.getrandbits(1)),rng.choice(forms),[])
        for __ in range(rng.randrange(1,4)):
            if ts:ts[rng.randrange(len(ts))]=rng.randrange(16)
        assert decode(False,ts)==decode(True,translate(ts))
        assert decode(True,ts)==decode(False,translate(ts))
    other=('i',TRUTH,TRUTH);ts=encode(False,other,rows(0))
    assert decode(False,ts)==other and decode(True,ts)==TRUTH and other!=TRUTH
    # Large unary-index invalid certificate must be rejected at guard.
    assert not check(('a',1000),[])
    print(f'PASS {len(forms)} formulas ({ntaut} tautologies), {ncase} structured certificates, '
          f'{bad} exhaustive short token strings, 2000 corrupted strings, distinct-system witness and large-index guard')
if __name__=='__main__':verify()
