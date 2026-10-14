import itertools, json
V=range(6)
E={frozenset(e) for e in [(0,1),(1,2),(0,2),(0,3),(1,3),(1,4),(2,4),(0,5),(2,5)]}
def adjacent(i,j): return frozenset((i,j)) in E and i!=j
cliques=[frozenset(S) for n in range(7) for S in itertools.combinations(V,n) if all(adjacent(i,j) for i,j in itertools.combinations(S,2))]
maximal=[S for S in cliques if not any(S<T for T in cliques)]
expected=[frozenset(x) for x in [(0,1,2),(0,1,3),(1,2,4),(0,2,5)]]
assert set(maximal)==set(expected)
induced=[]; tested=0
for n in range(4,7):
 for C in itertools.permutations(V,n):
  tested+=1
  if all(adjacent(C[i],C[j]) == ((j-i)%n in (1,n-1)) for i in range(n) for j in range(i+1,n)): induced.append(C)
assert not induced
for v in V:
 bags={i for i,S in enumerate(expected) if v in S}
 assert len(bags)==1 or 0 in bags
result={'vertices':6,'edges':len(E),'maximal_cliques':[sorted(S) for S in maximal],'induced_cycle_orderings_checked':tested,'induced_cycles_length_ge4':0,'running_intersection':True,'scope':'Finite independent test; universal Lean proof is separate.'}
print(json.dumps(result,indent=2))
