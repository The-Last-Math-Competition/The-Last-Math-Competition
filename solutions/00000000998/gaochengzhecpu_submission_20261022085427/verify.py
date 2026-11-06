"""Integer identities for the standard transpose-amplification witness.

Only checks algebraic identities, not a numerical norm oracle for Lean.
F is unitary; its partial transpose is |Omega><Omega|, with norm n.
"""
import json
def mul(a,b):
    bt=list(zip(*b))
    return [[sum(x*y for x,y in zip(row,col)) for col in bt] for row in a]
def scalar(c,a):return [[c*x for x in row] for row in a]
def matvec(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
rows=[]
for n in [2,8]:
    pairs=[(a,b) for a in range(n) for b in range(n)]
    f=[[int(a==d and b==c) for c,d in pairs] for a,b in pairs]
    identity=[[int(i==j) for j in range(n*n)] for i in range(n*n)]
    assert mul(f,f)==identity
    assert f==[list(col) for col in zip(*f)]
    # Transpose only the second (matrix algebra) index inside each block.
    pt=[[f[a*n+d][c*n+b] for c,d in pairs] for a,b in pairs]
    omega=[int(a==b) for a,b in pairs]
    q=[[x*y for y in omega] for x in omega]
    assert pt==q
    assert sum(x*x for x in omega)==n
    assert matvec(q,omega)==[n*x for x in omega]
    assert mul(q,q)==scalar(n,q)
    assert q==[list(col) for col in zip(*q)]
    rows.append({'matrix_algebra_dimension':n,'amplified_matrix_order':n*n,'swap_unitary':True,'partial_transpose_is_rank_one':True,'omega_squared_norm':n,'q_omega_eigenvalue':n})
print(json.dumps(rows,indent=2))
