#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001756.

1. Builds the S_3 character table (rows sorted by dimension) and computes
   the determinant of every square submatrix: the true maximal unimodular
   (det = +-1) order is 2.
2. Recomputes hook multisets of all partitions of 3 from the hook-length
   formula and counts pairwise-coprime ones: the conjecture's formula
   gives 3.
3. Concludes 3 != 2: the characterization fails.
Exit 0 iff all checks pass.
"""
import sys
from itertools import combinations
from math import gcd


def main():
    # S_3 character table, rows sorted by dimension:
    #   trivial (dim 1): [1, 1, 1]
    #   sign    (dim 1): [1, -1, 1]
    #   standard(dim 2): [2, 0, -1]
    # columns: [e], [(12)], [(123)]
    table = [[1, 1, 1], [1, -1, 1], [2, 0, -1]]
    m = len(table)

    def det(mat):
        if len(mat) == 1:
            return mat[0][0]
        return sum(
            (-1) ** j * mat[0][j] * det([row[:j] + row[j + 1:] for row in mat[1:]])
            for j in range(len(mat))
        )

    max_unimod = 0
    unimod_sub = None
    for k in range(1, m + 1):
        for rows in combinations(range(m), k):
            for cols in combinations(range(m), k):
                sub = [[table[r][c] for c in cols] for r in rows]
                d = det(sub)
                if abs(d) == 1 and k > max_unimod:
                    max_unimod = k
                    unimod_sub = (rows, cols, d)
    full_det = det(table)
    print(f"full 3x3 determinant: {full_det}")
    assert full_det == 6
    print(f"maximal unimodular submatrix order: {max_unimod}, e.g. "
          f"rows {unimod_sub[0]} cols {unimod_sub[1]} det {unimod_sub[2]}")
    assert max_unimod == 2
    d_actual = max_unimod

    # hook lengths from the hook-length formula: for cell (i,j) of the
    # Young diagram (0-indexed), hook = (arm) + (leg) + 1
    def hooks(partition):
        res = []
        for i, row in enumerate(partition):
            for j in range(row):
                arm = partition[i] - j - 1
                leg = sum(1 for r in partition[i + 1:] if r > j)
                res.append(arm + leg + 1)
        return sorted(res, reverse=True)

    parts3 = [(3,), (2, 1), (1, 1, 1)]
    count = 0
    for lam in parts3:
        hs = hooks(lam)
        ok = all(gcd(a, b) == 1 for i, a in enumerate(hs) for b in hs[i + 1:])
        print(f"partition {lam}: hooks {hs}, pairwise coprime = {ok}")
        if ok:
            count += 1
    print(f"hook-coprimality count (conjecture's d(3)): {count}")
    assert count == 3

    print(f"CONCLUSION: formula d(3) = {count} != {d_actual} = true maximal "
          f"unimodular order")
    assert count != d_actual
    print("ALL CHECKS PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
