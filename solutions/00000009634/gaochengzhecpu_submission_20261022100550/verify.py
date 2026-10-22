"""Supplementary exact check of the four-state HMM counterexample.

This finite check is not a replacement for Lean's all-word rank theorem or
its lower bound against arbitrary nonnegative hidden-state models.
"""
from fractions import Fraction as Q
from itertools import product
from functools import cache
import json

P=tuple(tuple(Q(int(j==i or j==(i+1)%4),2) for j in range(4)) for i in range(4))
pi=(Q(1,4),)*4
assert all(sum(row)==1 for row in P)
assert tuple(sum(pi[i]*P[i][j] for i in range(4)) for j in range(4))==pi

def row_step(row,a):
    return tuple(sum(row[i]*P[i][j] for i in range(4)) if j==a else Q(0) for j in range(4))

@cache
def past(word):
    row=pi
    for a in word:row=row_step(row,a)
    return row

@cache
def future(word):
    vec=(Q(1),)*4
    for a in reversed(word):
        vec=tuple(P[i][a]*vec[a] for i in range(4))
    return vec

@cache
def prob(word):return sum(past(word))

def markov_prob(word):
    if not word:return Q(1)
    z=Q(1,4)
    for i,j in zip(word,word[1:]):z*=P[i][j]
    return z

def words(n):return list(product(range(4),repeat=n))

for n in range(7):
    ws=words(n)
    assert sum(prob(w) for w in ws)==1
    for w in ws:
        assert prob(w)==markov_prob(w)
        assert (prob(w)>0)==all(j==i or j==(i+1)%4 for i,j in zip(w,w[1:]))
        assert sum(pi[i]*future(w)[i] for i in range(4))==prob(w)

short=sum((words(n) for n in range(4)),[])
for v in short:
    f=future(v); assert f[3]==f[0]-f[1]+f[2]
for u in short:
    r=past(u); l=(r[0]+r[3],r[1]-r[3],r[2]+r[3])
    for v in short:
        assert prob(u+v)==sum(l[k]*future(v)[k] for k in range(3))

H=tuple(tuple(prob((i,j)) for j in range(4)) for i in range(4))
assert all(H[i][i]>0 for i in range(4))
assert all(H[i][j]*H[j][i]==0 for i in range(4) for j in range(4) if i!=j)
minor=[list(H[i][:3]) for i in range(3)]
a,b,c=minor
det=a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
assert det==Q(1,512)
print(json.dumps({'stationary_model':True,'word_normalization_checked_through_length':6,'all_word_formula_finite_check':True,'sofic_language_finite_check':True,'hankel_factorization_test_rows_and_columns':len(short),'three_by_three_minor':str(det),'four_diagonal_fooling_set':True,'length_two_probability_matrix':[[str(x) for x in row] for row in H]},indent=2))
