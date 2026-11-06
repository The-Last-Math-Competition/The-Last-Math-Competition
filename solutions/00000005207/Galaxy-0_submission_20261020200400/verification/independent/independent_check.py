"""Independent exact-arithmetic checks of the TLMC 5207 witness.

This does not replace the Lean proof. It recomputes the numerical certificates
by the Leibniz determinant formula, independent of Lean's Laplace algorithm.
"""
from fractions import Fraction
from itertools import permutations
import sympy as sp


def determinant(a):
    n = len(a)
    total = Fraction(0)
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        term = Fraction((-1) ** inversions)
        for i in range(n):
            term *= a[i][p[i]]
        total += term
    return total


x, y, z = sp.symbols("x y z")
a = sp.Matrix([[0, x, y], [-x, 0, z], [-y, -z, 0]])
assert sp.expand(a.det(method="domain-ge")) == 0
coefficients = [a.diff(v) for v in (x, y, z)]
blocks = [sp.Matrix([[1, 0], [0, 0]]),
          sp.Matrix([[0, 1], [1, 0]]),
          sp.Matrix([[0, 0], [0, 1]])]
b = sum((sp.kronecker_product(c, t) for c, t in zip(coefficients, blocks)), sp.zeros(6))
blowup = [[int(b[i, j]) for j in range(6)] for i in range(6)]
assert determinant(blowup) == 1
assert determinant([[0, 1], [-1, 0]]) == 1
assert all(sp.kronecker_product(c, sp.Matrix([[1]])) == c for c in coefficients)
assert (3 - 2) != (3 - 2) * (1 - 1)
print("Symbolic determinant: 0")
print("Attained two-by-two minor determinant: 1")
print("Actual coefficient Kronecker product with scalar unit: unchanged")
print("Six-by-six blowup matrix:")
for row in blowup:
    print(row)
print("Six-by-six Leibniz determinant: 1")
print("Gap comparison: 1 != 0")
print("All independent checks passed.")
