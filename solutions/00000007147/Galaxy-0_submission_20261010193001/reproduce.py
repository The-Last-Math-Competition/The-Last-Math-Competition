from itertools import combinations
from functools import lru_cache
vertices=range(5)
diagonals=[(i,j) for i,j in combinations(vertices,2) if j!=i+1 and (i,j)!=(0,4)]
def crossing(x,y):
 a,b=x;c,d=y
 return a<c<b<d or c<a<d<b
faces=[s for k in range(6) for s in combinations(diagonals,k) if all(not crossing(a,b) for a,b in combinations(s,2))]
@lru_cache(None)
def binary_trees(leaves):
 if leaves==1:return ('x',)
 return tuple((a,b) for k in range(1,leaves) for a in binary_trees(k) for b in binary_trees(leaves-k))
print('diagonals',diagonals)
print('noncrossing partial triangulations',faces)
print('face counts indexed by codimension',[sum(len(x)==k for x in faces) for k in range(3)])
print('binary trees on four leaves',binary_trees(4))
assert len(faces)==11
assert len(binary_trees(4))==5
assert len(faces)!=len(binary_trees(4))
assert len(faces)+1!=len(binary_trees(4))
assert len(faces)-1!=len(binary_trees(4))
print('PASS: 11 nonempty faces; 12 with empty; 10 proper nonempty; 5 binary trees')
