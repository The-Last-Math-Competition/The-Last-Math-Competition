"""Independent exact finite C^3/M2 arithmetic, not a C*-nuclearity or generic proof."""
from fractions import Fraction as F
from itertools import product

ZERO = (F(0), F(0))
ONE = (F(1), F(0))
I = (F(0), F(1))
Z3 = (ZERO, ZERO, ZERO)
U3 = (ONE, ONE, ONE)


def validate_complex(z):
    if not isinstance(z, tuple) or len(z) != 2 or any(type(x) not in (int, F) for x in z):
        raise ValueError("Expected an exact rational real/imaginary pair")


def validate_algebra(a):
    if not isinstance(a, tuple) or len(a) != 3:
        raise ValueError("Expected exactly three complex coordinates")
    for z in a:
        validate_complex(z)


def cadd(z, w):
    return (z[0] + w[0], z[1] + w[1])


def cmul(z, w):
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def cstar(z):
    return (z[0], -z[1])


def norm_sq(z):
    return z[0] ** 2 + z[1] ** 2


def aadd(a, b):
    return tuple(cadd(a[i], b[i]) for i in range(3))


def amul(a, b):
    return tuple(cmul(a[i], b[i]) for i in range(3))


def astar(a):
    return tuple(cstar(z) for z in a)


def coordinate(i, a):
    validate_algebra(a)
    if type(i) is not int or not 0 <= i < 3:
        raise ValueError("Coordinate must be one of0,1,2")
    return a[i]


def atom(i):
    if type(i) is not int or not 0 <= i < 3:
        raise ValueError("Projection index out of bounds")
    return tuple(ONE if j == i else ZERO for j in range(3))


def validate_matrix(X):
    if not isinstance(X, tuple) or len(X) != 2 or any(not isinstance(row, tuple) or len(row) != 2 for row in X):
        raise ValueError("Expected a2-by-2 matrix")
    for row in X:
        for a in row:
            validate_algebra(a)


def mmul(X, Y):
    validate_matrix(X)
    validate_matrix(Y)
    return tuple(tuple(aadd(amul(X[r][0], Y[0][s]), amul(X[r][1], Y[1][s]))
                       for s in range(2)) for r in range(2))


def mstar(X):
    validate_matrix(X)
    return tuple(tuple(astar(X[s][r]) for s in range(2)) for r in range(2))


def corner(a):
    validate_algebra(a)
    return ((a, Z3), (Z3, Z3))


def matrix_identity():
    return ((U3, Z3), (Z3, U3))


def matrix_trace(i, X):
    validate_matrix(X)
    return cadd(coordinate(i, X[0][0]), coordinate(i, X[1][1]))


def matrix_samples():
    samples = [matrix_identity()]
    for r, s, i, z in product(range(2), range(2), range(3), (ONE, I)):
        a = tuple(z if j == i else ZERO for j in range(3))
        samples.append(tuple(tuple(a if (u, v) == (r, s) else Z3 for v in range(2)) for u in range(2)))
    a = ((F(1), F(2)), (-F(1), F(0)), (F(0), F(3)))
    samples.append(((a, astar(a)), (U3, atom(2))))
    return tuple(samples)


def regression():
    alphabet = (ZERO, ONE, (-F(1), F(0)), I)
    vectors = tuple(product(alphabet, repeat=3))
    algebra_pairs = 0
    for a, b in product(vectors, repeat=2):
        for i in range(3):
            assert coordinate(i, aadd(a, b)) == cadd(coordinate(i, a), coordinate(i, b))
            assert coordinate(i, amul(a, b)) == cmul(coordinate(i, a), coordinate(i, b))
            square = coordinate(i, amul(astar(a), a))
            assert square == (norm_sq(a[i]), 0) and square[0] >= 0
            assert norm_sq(coordinate(i, a)) <= max(norm_sq(z) for z in a)
            algebra_pairs += 1
    samples = matrix_samples()
    matrix_pairs = 0
    for X, Y in product(samples, repeat=2):
        XY, YX = mmul(X, Y), mmul(Y, X)
        for i in range(3):
            assert matrix_trace(i, XY) == matrix_trace(i, YX)
            matrix_pairs += 1
    for X in samples:
        square = mmul(mstar(X), X)
        for i in range(3):
            expected = sum(norm_sq(X[r][s][i]) for r in range(2) for s in range(2))
            assert matrix_trace(i, square) == (expected, 0) and expected >= 0
            assert matrix_trace(i, mstar(X)) == cstar(matrix_trace(i, X))
    for i in range(3):
        assert coordinate(i, U3) == ONE
        assert matrix_trace(i, matrix_identity()) == (2, 0)
        for a in vectors:
            assert matrix_trace(i, corner(a)) == coordinate(i, a)
    evaluations = tuple(tuple(coordinate(i, atom(j))[0] for j in range(3)) for i in range(3))
    differences = tuple(tuple(evaluations[i][j] - evaluations[0][j] for j in (1, 2)) for i in (1, 2))
    determinant = differences[0][0] * differences[1][1] - differences[0][1] * differences[1][0]
    assert determinant == 1
    return {"exact_algebra_vectors": len(vectors), "algebra_coordinate_pair_checks": algebra_pairs,
            "matrix_samples": len(samples), "matrix_coordinate_pair_checks": matrix_pairs,
            "affine_minor": str(determinant), "matrix_identity_trace": "2, unnormalized",
            "scope": "Exact bounded arithmetic regression only. No general CPAP/quasitrace/topology/dimension proof, no CStar operator-norm computation, and no Lean or publication clearance."}


if __name__ == "__main__":
    import json
    print(json.dumps(regression(), indent=2))
