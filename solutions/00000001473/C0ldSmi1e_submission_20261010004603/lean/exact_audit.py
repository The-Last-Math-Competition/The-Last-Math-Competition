#!/usr/bin/env python3
"""Supplementary exact arithmetic audit. The Lean proof does not depend on it."""
from fractions import Fraction as F
import json


def solve_square(a, b):
    a = [[F(v) for v in row] + [F(rhs)] for row, rhs in zip(a, b)]
    n = len(a)
    assert all(len(row) == n + 1 for row in a)
    for col in range(n):
        pivot = next(row for row in range(col, n) if a[row][col])
        a[col], a[pivot] = a[pivot], a[col]
        d = a[col][col]
        a[col] = [v / d for v in a[col]]
        for row in range(n):
            if row != col:
                d = a[row][col]
                a[row] = [u - d * v for u, v in zip(a[row], a[col])]
    return [row[-1] for row in a]


def dot(a, x):
    return sum(F(c) * v for c, v in zip(a, x))


def feasible(p, x):
    return (all(dot(a, x) == b for a, b in p['equalities']) and
            all(dot(a, x) <= b for a, b in p['inequalities']) and
            all(b is None or b <= v for b, v in zip(p['lower'], x)) and
            all(b is None or v <= b for b, v in zip(p['upper'], x)))


def data(p):
    out = []
    for a, b in p['equalities'] + p['inequalities']:
        out += a + [b]
    out += [b for b in p['lower'] if b is not None]
    out += [b for b in p['upper'] if b is not None]
    out += p['cost'] + [p['constant']]
    return out


def main():
    mixed = {'equalities': [([-10, 1, 0], 0), ([0, -10, 1], 0)],
             'inequalities': [([-2, 0, 0], -1)],
             'lower': [None] * 3, 'upper': [None] * 3,
             'cost': [1, 0, 0], 'constant': 0}
    ineq = {**mixed, 'equalities': [], 'inequalities': [([-2, 0, 0], -1),
            ([-10, 1, 0], 0), ([10, -1, 0], 0),
            ([0, -10, 1], 0), ([0, 10, -1], 0)]}
    nonneg = {**ineq, 'lower': [0] * 3}
    eq = {'equalities': [([-10, 1, 0, 0], 0), ([0, -10, 1, 0], 0),
                        ([2, 0, 0, -1], 1)],
          'inequalities': [], 'lower': [0] * 4, 'upper': [None] * 4,
          'cost': [1, 0, 0, 0], 'constant': 0}
    a3 = [[2, 0, 0], [-10, 1, 0], [0, -10, 1]]
    real3 = solve_square(a3, [1, 0, 0])
    # The first feasible integer t obeys 2t >= 1, so t = 1.
    t = -(-1 // 2)
    integer3 = [t, 10*t, 100*t]
    a4 = [a for a, _ in eq['equalities']] + [[0, 0, 0, 1]]
    real4 = solve_square(a4, [0, 0, 1, 0])
    integer4 = integer3 + [2*t - 1]
    assert real3 == [F(1, 2), F(5), F(50)]
    assert real4 == real3 + [F(0)]
    outputs = []
    for name, p, xi, xr in [
        ('mixedFree', mixed, integer3, real3),
        ('inequalityFree', ineq, integer3, real3),
        ('inequalityNonnegative', nonneg, integer3, real3),
        ('equalityNonnegative', eq, integer4, real4),
    ]:
        n = len(p['cost'])
        all_data = data(p)
        assert all(isinstance(v, int) for v in all_data)
        delta = max(abs(v) for v in all_data)
        differences = [abs(F(u) - v) for u, v in zip(xi, xr)]
        distance = max(differences)
        assert feasible(p, xi) and feasible(p, xr)
        assert all(isinstance(v, int) for v in xi)
        assert delta == 10 and distance == 50 and distance > n * delta
        # Solving these independent active constraints also checks the vertex.
        active = [(a, b) for a, b in p['equalities']]
        active += [(a, b) for a, b in p['inequalities'] if dot(a, xr) == b]
        active += [([int(i == j) for j in range(n)], b)
                   for i, b in enumerate(p['lower']) if b is not None and xr[i] == b]
        basis = ([(a, b) for a, b in p['equalities']] +
                 [([0, 0, 0, 1], 0)]) if n == 4 else list(zip(a3, [1, 0, 0]))
        assert solve_square([a for a, _ in basis], [b for _, b in basis]) == xr
        for a, b in basis:
            assert any((a == aa and b == bb) or
                       (a == [-v for v in aa] and b == -bb) for aa, bb in active)
        outputs.append({'name': name, 'program': p, 'all_finite_data': all_data,
                        'n': n, 'delta': delta, 'real_optimum': list(map(str, xr)),
                        'integer_optimum': xi,
                        'real_objective': str(dot(p['cost'], xr) + p['constant']),
                        'integer_objective': str(dot(p['cost'], xi) + p['constant']),
                        'coordinate_distances': list(map(str, differences)),
                        'infinity_distance': str(distance), 'claimed_bound': n*delta,
                        'strict_margin': str(distance-n*delta), 'active_rank': n})
    print(json.dumps(outputs, indent=2))


if __name__ == '__main__':
    main()
