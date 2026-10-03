#!/usr/bin/env python3
"""Exhaustive search supporting Remark 1 of main.tex (not used in the refutation).

For every length n <= 6, enumerate all binary linear codes C <= F_2^n, group them
into permutation-equivalence classes, and list the groups of classes that share a
weight distribution (A_0, ..., A_n).

* Every subspace of F_2^n has a unique basis in reduced row echelon form, so
  enumerating pivot sets and free entries visits each subspace exactly once. The
  number of subspaces is printed and can be compared with the Gaussian binomial sums
  2, 5, 16, 67, 374, 2825.
* A code is stored as the sorted tuple of its codewords (bitmasks). Its canonical
  form is the minimum of this tuple over all n! coordinate permutations, so two codes
  are permutation equivalent iff their canonical forms coincide.

Standard library only; runs in a few seconds.
"""

import collections
import itertools


def subspaces(n):
    """Yield (k, codewords) for every subspace of F_2^n, each exactly once."""
    for k in range(n + 1):
        for pivots in itertools.combinations(range(n), k):
            free = [[c for c in range(p + 1, n) if c not in pivots] for p in pivots]
            choices = [itertools.product((0, 1), repeat=len(f)) for f in free]
            for bits in itertools.product(*choices):
                rows = []
                for p, f, b in zip(pivots, free, bits):
                    r = 1 << p
                    for c, x in zip(f, b):
                        if x:
                            r |= 1 << c
                    rows.append(r)
                code = {0}
                for r in rows:
                    code |= {c ^ r for c in code}
                yield k, frozenset(code)


def permute(v, perm, n):
    return sum(1 << perm[i] for i in range(n) if v >> i & 1)


def weight_distribution(code, n):
    counts = collections.Counter(bin(c).count("1") for c in code)
    return tuple(counts[w] for w in range(n + 1))


def main():
    for n in range(1, 7):
        perms = list(itertools.permutations(range(n)))
        classes = {}
        total = 0
        for k, code in subspaces(n):
            total += 1
            canon = min(tuple(sorted(permute(c, p, n) for c in code)) for p in perms)
            classes.setdefault(canon, (k, code))
        groups = collections.defaultdict(list)
        for canon, (k, code) in classes.items():
            groups[(k, weight_distribution(code, n))].append(sorted(code))
        hits = {key: v for key, v in groups.items() if len(v) > 1}
        print(f"n={n}: subspaces={total} classes={len(classes)} "
              f"isospectral groups with >1 class: {len(hits)}")
        for (k, dist), codes in hits.items():
            print(f"  k={k} (A_0..A_{n})={dist}")
            for code in codes:
                words = [format(c, f"0{n}b")[::-1] for c in code]
                print("    " + " ".join(words))


if __name__ == "__main__":
    main()
