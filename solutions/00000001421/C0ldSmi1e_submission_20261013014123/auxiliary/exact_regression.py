#!/usr/bin/env python3
"""Finite exact regression, supplementary to the unbounded Lean proof.

Construct the walk from group increments, then multiply distributions directly.
Check the proposed closed kernel, TV, genuine first threshold times, and a full
real eigenbasis independently. No floating point or symbolic-library dependency.
These finitely many instances do not prove the conjecture's asymptotic negation.
"""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def walk(n):
    states = [(a, b) for a in range(2) for b in range(n)]
    support = {(0, h) for h in range(1, n)} | {(1, 0)}
    p = [[F(x == y, 2) + F(((y[0]-x[0]) % 2,
                            (y[1]-x[1]) % n) in support, 2*n)
          for y in states] for x in states]
    return states, support, p


def apply_row(v, p):
    return [sum((v[i]*p[i][j] for i in range(len(v))), F(0))
            for j in range(len(v))]


def apply_column(p, v):
    return [sum((row[j]*v[j] for j in range(len(v))), F(0))
            for row in p]


def rank(vectors):
    a = [list(map(F, v)) for v in vectors]
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        divisor = a[r][c]
        a[r] = [x/divisor for x in a[r]]
        for i in range(r+1, len(a)):
            factor = a[i][c]
            if factor:
                a[i] = [x-factor*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def kernel(n, t, x, y):
    sign = 1 if x[0] == y[0] else -1
    delta = int(x[1] == y[1])
    q, r, s = F(n-1, n), F(1, 2), F(n-2, 2*n)
    return (1+sign*q**t+(n*delta-1)*(r**t+sign*s**t))/(2*n)


def check_instance(n, last_time=24):
    states, support, p = walk(n)
    size = len(states)
    require(len(support) == n and (0, 0) not in support, 'support size/identity')
    require({((-a) % 2, (-b) % n) for a, b in support} == support,
            'symmetric support')
    reachable = {(0, 0)} | support
    reachable |= {((a+c) % 2, (b+d) % n) for a, b in support for c, d in support}
    require(reachable == set(states), 'support generates whole group in two steps')
    require(all(x >= 0 for row in p for x in row), 'nonnegative kernel')
    require(all(sum(row) == 1 for row in p), 'row sums')
    require(all(sum(p[i][j] for i in range(size)) == 1 for j in range(size)),
            'column sums/uniform stationarity')
    require(all(p[i][i] == F(1, 2) for i in range(size)), 'exact half hold')
    require(all(p[i][j] == p[j][i] for i in range(size) for j in range(size)),
            'symmetry')
    require(all(x > 0 for row in p for x in apply_row(row, p)), 'positive two-step kernel')

    # An independent real eigenbasis, avoiding complex-root numerical arithmetic.
    q, r, s = F(n-1, n), F(1, 2), F(n-2, 2*n)
    basis = [([F(1)]*size, F(1)), ([F((-1)**a) for a, b in states], q)]
    for h in range(1, n):
        basis.append(([F(int(b == h)-int(b == 0)) for a, b in states], r))
        basis.append(([F((-1)**a*(int(b == h)-int(b == 0))) for a, b in states], s))
    require(rank([v for v, eigenvalue in basis]) == size, 'eigenbasis independence')
    require(all(apply_column(p, v) == [eigenvalue*x for x in v]
                for v, eigenvalue in basis), 'actual eigenbasis action')
    require(1 > q > r > s > 0, 'eigenvalue ordering')
    require(sum(e == s for v, e in basis) == n-1, 'smallest eigenvalue multiplicity')
    require(sum(e == q for v, e in basis) == 1, 'gap-mode multiplicity')

    laws = [[F(i == j) for j in range(size)] for i in range(size)]
    first_times = {}
    entry_checks = 0
    for t in range(last_time+1):
        distances = []
        for i, x in enumerate(states):
            require(sum(laws[i]) == 1 and all(v >= 0 for v in laws[i]), 'actual law')
            for j, y in enumerate(states):
                require(laws[i][j] == kernel(n, t, x, y), 'closed kernel vs direct evolution')
                entry_checks += 1
            distance = sum(abs(v-F(1, size)) for v in laws[i])/2
            expected = 1-F(1, size) if t == 0 else q**t/2
            require(distance == expected, 'exact total variation')
            distances.append(distance)
        worst = max(distances)
        for tolerance in (F(1, 4), F(3, 4)):
            if worst <= tolerance and tolerance not in first_times:
                first_times[tolerance] = t
        if t != last_time:
            laws = [apply_row(row, p) for row in laws]
    require(set(first_times) == {F(1, 4), F(3, 4)}, 'finite threshold coverage')
    low, high = first_times[F(1, 4)], first_times[F(3, 4)]
    require(high == 1 and low >= F(n, 2) and low >= 2, 'true mixing-time bounds')
    require(1 < F(low, low-high) <= 2, 'positive genuine window and bounded ratio')
    require(F(n-1)/(1-q) == n*(n-1) and 1/(1-q) == n, 'actual spectral ratios')
    return {'N': n, 'states': size, 'times_checked': last_time+1,
            'kernel_entries_checked': entry_checks,
            'mixing_time_quarter': low, 'mixing_time_three_quarters': high,
            'time_window_ratio': str(F(low, low-high)), 'eigenbasis_rank': size}


def negative_controls():
    states, support, p = walk(4)
    bad = [row[:] for row in p]
    bad[0][0] += F(1, 8)
    rejected = False
    try:
        require(all(sum(row) == 1 for row in bad), 'mutated row normalization')
    except AssertionError:
        rejected = True
    require(rejected, 'negative normalization control did not reject')
    # Changing q in the slow parity eigenvalue breaks the actual action.
    parity = [F((-1)**a) for a, b in states]
    require(apply_column(p, parity) != [F(1, 2)*v for v in parity],
            'negative eigenvalue control did not reject')
    # Time zero must be the point mass, not the t>=1 scalar profile.
    require(1-F(1, len(states)) != F(1, 2), 'negative time-zero control')
    return ['wrong row normalization rejected', 'wrong slow eigenvalue rejected',
            'incorrect time-zero profile rejected']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {'status': 'PASS_EXACT_FINITE_REGRESSION',
              'scope': 'Supplementary finite regression, not an asymptotic proof.',
              'instances': [check_instance(n) for n in (4, 5, 6, 7, 8, 11, 16)],
              'negative_controls': negative_controls()}
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
