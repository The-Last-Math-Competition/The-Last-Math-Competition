"""Independent exact random-graph checks; no oracle is used by Lean."""
from fractions import Fraction
from itertools import combinations, product
import json

def graph_check(n):
    edges=list(combinations(range(n),2))
    labels={e:i for i,e in enumerate(edges)}
    triangles=[sum(1<<labels[e] for e in combinations(v,2))
               for v in combinations(range(n),3)]
    blocks=n//3
    selected=[sum(1<<labels[tuple(sorted(e))] for e in combinations(v,2))
              for v in product(range(blocks),range(blocks,2*blocks),range(2*blocks,n))]
    total=triangle=tripartite=0
    for mask in range(1<<len(edges)):
        weight=(n-1)**(len(edges)-mask.bit_count())
        total+=weight
        if any(mask&t==t for t in triangles):triangle+=weight
        if any(mask&t==t for t in selected):tripartite+=weight
    denominator=n**len(edges)
    assert total==denominator
    p=Fraction(tripartite,denominator)
    assert Fraction(1,50)<=p<=Fraction(triangle,denominator)
    return {'vertices':n,'all_graphs':1<<len(edges),
            'triangle_probability':str(Fraction(triangle,denominator)),
            'tripartite_triangle_probability':str(p)}

def overlap_check(h):
    ts=list(product(range(h),repeat=3))
    def edges(t):
        vs=[(i,t[i]) for i in range(3)]
        return frozenset(frozenset(e) for e in combinations(vs,2))
    sets={t:edges(t) for t in ts}
    shared=disjoint=0
    for t in ts:
        assert len(sets[t])==3
        for s in ts:
            if t==s:continue
            intersection=len(sets[t]&sets[s])
            assert intersection in (0,1)
            assert len(sets[t]|sets[s])==(5 if intersection else 6)
            if intersection:shared+=1
            else:disjoint+=1
    assert shared==3*h**3*(h-1)
    assert disjoint==h**6-h**3-shared
    n=3*h
    single=Fraction(h**3,n**3)
    ordered=Fraction(shared,n**5)+Fraction(disjoint,n**6)
    crude=Fraction(1,27)-Fraction(1,81*h)-Fraction(1,729)
    assert single==Fraction(1,27)
    assert single-ordered>=crude>=Fraction(17,729)>Fraction(1,50)
    return {'block_size':h,'triangles':len(ts),'ordered_shared_edge_pairs':shared,
            'ordered_other_pairs':disjoint,'ordered_Bonferroni_lower':str(single-ordered)}

if __name__=='__main__':
    print(json.dumps({'status':'PASS','full_graph_laws':[graph_check(n) for n in (3,6)],
                      'overlaps':[overlap_check(h) for h in range(1,9)]},indent=2))
