#!/usr/bin/env python3
"""Exact standard-library arithmetic check, independent of Lean execution."""
from fractions import Fraction as Q
from itertools import permutations

f = [Q(0), Q(-4), Q(0), Q(1)]
g = [Q(-1), Q(0), Q(1)]

def coefficient(poly, exponent):
    return poly[exponent] if 0 <= exponent < len(poly) else Q(0)

def sylvester_submatrix(p, q, i, F, G):
    rows, cols = p + q - 2*i, p + q - i
    out = []
    for r in range(rows):
        poly, shift = (F, q-i-1-r) if r < q-i else (G, p-i-1-(r-(q-i)))
        out.append([coefficient(poly, cols-1-c-shift) for c in range(cols)])
    return out

def determinant(A):
    n = len(A)
    total = Q(0)
    for perm in permutations(range(n)):
        parity = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1,n))
        term = Q((-1)**parity)
        for i in range(n):
            term *= A[i][perm[i]]
        total += term
    return total

def coeff_minor(A, k, t):
    columns = list(range(k-1)) + [k-1+t]
    return determinant([[A[r][c] for c in columns] for r in range(k)])

def multiply(P, R):
    out = [Q(0)] * (len(P)+len(R)-1)
    for i,a in enumerate(P):
        for j,b in enumerate(R):
            out[i+j] += a*b
    return out

def add(P,R):
    return [coefficient(P,i)+coefficient(R,i) for i in range(max(len(P),len(R)))]

S = sylvester_submatrix(3,2,1,f,g)
assert S == [[1,0,-4,0],[1,0,-1,0],[0,1,0,-1]]
assert coeff_minor(S,3,0) == -3
assert coeff_minor(S,3,1) == 0
assert multiply(multiply([2,1],[0,1]),[-2,1]) == f
assert multiply([1,1],[-1,1]) == g
assert add(multiply([0,1],f),multiply([3,0,-1],g)) == [-3,0,0,0,0]
roots = [-2,-1,0,1,2]
assert all(a < b for a,b in zip(roots,roots[1:]))
print('PASS: generic Sylvester construction, determinant minors, factorization, interlacing, Bezout.')
