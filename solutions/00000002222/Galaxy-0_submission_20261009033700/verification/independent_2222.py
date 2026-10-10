#!/usr/bin/env python3
"""Independent direct arithmetic validation; not part of the Lean trust base."""
import hashlib, importlib.util, json, math, pathlib, sys
root=pathlib.Path(sys.argv[1]).resolve()
spec=importlib.util.spec_from_file_location('certificate_generator',root/'generate.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
counts={'moduli':0,'color_pairs':0,'clique_pairs':0,'annihilator_witnesses':0,'prime_powers':0}
for n in range(1,1001):
 C,K=g.certificate(n)
 V=[x for x in range(1,n) if math.gcd(n,x)>1]
 assert sorted(x for c in C for x in c)==V,(n,'partition')
 assert len(K)==len(set(K))==len(C),(n,'matching cardinality')
 assert all(x in V for x in K),(n,'clique membership')
 for x in V:
  y=n//math.gcd(n,x)
  assert 0<y<n and x*y%n==0,(n,x,'annihilator')
  counts['annihilator_witnesses']+=1
 for c in C:
  for i,x in enumerate(c):
   for y in c[i+1:]:
    assert x!=y and x*y%n!=0,(n,x,y,'color pair')
    counts['color_pairs']+=1
 for i,x in enumerate(K):
  for y in K[i+1:]:
   assert x!=y and x*y%n==0,(n,x,y,'clique pair')
   counts['clique_pairs']+=1
 counts['moduli']+=1
 counts['prime_powers']+=int(len(g.factors(n))==1)
print(json.dumps({'status':'PASS','scope':'positive n=1..1000','counts':counts,'generator_sha256':hashlib.sha256((root/'generate.py').read_bytes()).hexdigest()},indent=2))
