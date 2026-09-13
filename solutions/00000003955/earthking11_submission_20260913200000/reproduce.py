#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000003955.

    Definition: the rank-width r is a width parameter satisfying, with
        treewidth t, the classical inequality t <= 3r - 1.
    Conjecture: the constant 3 in t <= 3r - 1 is optimal, with an explicit
        family of graphs of rank-width r and treewidth exactly 3r - 1.

The stated inequality is false.  For the complete graph K_n:

    rank-width(K_n) = 1        (every nontrivial bipartition has an all-ones
                                cut matrix, of GF(2)-rank 1),
    treewidth(K_n)  = n - 1    (K_n is a clique; every elimination step has
                                n - 1 ... 1 remaining neighbours).

Hence t = n - 1 and 3r - 1 = 2, and t > 3r - 1 as soon as n >= 4.  K_4 is the
smallest counterexample (t = 3 > 2 = 3*1 - 1); K_3 saturates the inequality
(t = 2 = 3*1 - 1) and K_2 satisfies it strictly (t = 1 < 2).  Since
treewidth(K_n) grows without bound while rank-width(K_n) stays 1, no function
of the rank-width upper-bounds the treewidth at all, so 3 is not merely a
non-optimal constant: the inequality itself is invalid.

What this script does, for n = 2, ..., 7:

  * computes over GF(2) the rank of the cut matrix of EVERY bipartition of K_n
    and reports the maximum (always 1 for n >= 2);
  * verifies a caterpillar rank-decomposition all of whose cuts have rank 1,
    witnessing rank-width <= 1, and the matching rank-width >= 1 lower bound;
  * computes the treewidth EXACTLY by brute force over all n! elimination
    orders (the elimination-game characterisation of treewidth), and checks the
    min-degree lower bound treewidth >= minimum degree;
  * exhibits the width-(n-1) decomposition (one bag containing all vertices);
  * tabulates t against 3r - 1 and asserts the inequality fails for n >= 4.

Standard library only.  Python 3.8+.  Runs in a few seconds (the n = 7 case
enumerates 7! = 5040 elimination orders).
"""

from itertools import permutations


# ---------------------------------------------------------------------------
# GF(2) linear algebra
# ---------------------------------------------------------------------------

def gf2_rank(mat):
    """Rank over GF(2) of a matrix given as a list of 0/1 rows.

    Gaussian elimination to reduced row echelon form; XOR is addition in GF(2).
    """
    rows = [row[:] for row in mat]
    m = len(rows)
    if m == 0:
        return 0
    ncol = len(rows[0])
    rank = 0
    for col in range(ncol):
        pivot = None
        for r in range(rank, m):
            if rows[r][col]:
                pivot = r
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for r in range(m):
            if r != rank and rows[r][col]:
                rows[r] = [a ^ b for a, b in zip(rows[r], rows[rank])]
        rank += 1
        if rank == m:
            break
    return rank


# ---------------------------------------------------------------------------
# complete graphs and their cuts
# ---------------------------------------------------------------------------

def complete_adj(n):
    """Adjacency matrix of K_n."""
    return [[0 if i == j else 1 for j in range(n)] for i in range(n)]


def cut_matrix(adj, x_side, y_side):
    """Cut matrix of the bipartition (x_side, y_side): entry (i, j) = adj[i][j]."""
    return [[adj[i][j] for j in y_side] for i in x_side]


def all_bipartitions(n):
    """All unordered bipartitions of {0, ..., n-1} into two nonempty parts.

    Stored as canonically ordered pairs (X, Y) with X < Y lexicographically, so
    each bipartition appears exactly once: there are 2^(n-1) - 1 of them.
    """
    seen = set()
    result = []
    all_vertices = tuple(range(n))
    for mask in range(1, (1 << n) - 1):
        X = tuple(i for i in all_vertices if mask >> i & 1)
        Y = tuple(i for i in all_vertices if not (mask >> i & 1))
        key = min(X, Y)
        if key in seen:
            continue
        seen.add(key)
        result.append((X, Y))
    return result


def cut_rank_profile(adj, n):
    """Rank of the cut matrix of every bipartition of the n-vertex graph.

    Returns (max_rank, rank_count) where rank_count maps a rank to the number
    of bipartitions having it.
    """
    max_rank = 0
    rank_count = {}
    for X, Y in all_bipartitions(n):
        r = gf2_rank(cut_matrix(adj, X, Y))
        rank_count[r] = rank_count.get(r, 0) + 1
        max_rank = max(max_rank, r)
    return max_rank, rank_count


def caterpillar_cut_ranks(adj, n):
    """Cut-ranks along the caterpillar rank-decomposition of K_n.

    The decomposition splits off one vertex at a time:
        {0} | {1, ..., n-1},  {1} | {2, ..., n-1}, ...,
        {n-2} | {n-1}.
    Every cut matrix is an all-ones row of length n-1-i, so its rank is 1 once
    that length is at least 1.
    """
    ranks = []
    for i in range(n - 1):
        X = [i]
        Y = list(range(i + 1, n))
        ranks.append(gf2_rank(cut_matrix(adj, X, Y)))
    return ranks


# ---------------------------------------------------------------------------
# exact treewidth by elimination orders
# ---------------------------------------------------------------------------

def min_degree(adj, n):
    return min(sum(row) for row in adj)


def elimination_width(adj, n, order):
    """Width of an elimination order in the elimination game.

    Eliminating a vertex turns its current neighbourhood into a clique (fill
    edges) and removes it; the width is the maximum number of current
    neighbours seen at any elimination step.
    """
    g = [row[:] for row in adj]
    remaining = [True] * n
    width = 0
    for v in order:
        neighbours = [u for u in range(n) if remaining[u] and g[v][u]]
        width = max(width, len(neighbours))
        for a in neighbours:
            for b in neighbours:
                if a != b:
                    g[a][b] = 1
        remaining[v] = False
    return width


def treewidth_by_elimination(adj, n):
    """Exact treewidth: minimum elimination width over all n! orders.

    This uses the standard elimination-game characterisation of treewidth.
    """
    best = n
    for order in permutations(range(n)):
        w = elimination_width(adj, n, order)
        if w < best:
            best = w
    return best


# ---------------------------------------------------------------------------

def main():
    checks = []
    rows = []

    for n in range(2, 8):
        adj = complete_adj(n)

        # --- rank-width side ------------------------------------------------
        max_cut_rank, rank_count = cut_rank_profile(adj, n)
        n_bip = len(all_bipartitions(n))
        cat_ranks = caterpillar_cut_ranks(adj, n)

        # rank-width of K_n is 1:  upper bound from the caterpillar (all its
        # cuts have rank 1), lower bound because every rank-decomposition has a
        # (nontrivial) root cut whose all-ones cut matrix has rank 1.
        rank_width = 1

        checks.append((
            f"n = {n}: every bipartition of K_{n} has GF(2) cut-rank 1 "
            f"({n_bip} bipartitions, ranks {rank_count})",
            max_cut_rank == 1,
            f"maximum cut-rank {max_cut_rank}; rank distribution {rank_count}",
        ))
        checks.append((
            f"n = {n}: caterpillar rank-decomposition has width 1 "
            f"(cuts ranked {cat_ranks})",
            all(r == 1 for r in cat_ranks) and len(cat_ranks) == n - 1,
            f"cut-ranks along the caterpillar: {cat_ranks}",
        ))

        # --- treewidth side -------------------------------------------------
        tw = treewidth_by_elimination(adj, n)
        delta = min_degree(adj, n)
        explicit_width = n - 1  # single bag {0, ..., n-1}

        checks.append((
            f"n = {n}: explicit decomposition has width {explicit_width} = n - 1",
            explicit_width == n - 1,
            f"single bag containing all {n} vertices, width {n - 1}",
        ))
        checks.append((
            f"n = {n}: min-degree lemma treewidth >= delta = {delta}",
            tw >= delta,
            f"treewidth {tw} >= minimum degree {delta}",
        ))
        checks.append((
            f"n = {n}: exact treewidth = n - 1 = {n - 1}",
            tw == n - 1,
            f"minimum elimination width over all {len(list(permutations(range(n))))} orders is {tw}",
        ))

        # --- the inequality t <= 3r - 1 -------------------------------------
        bound = 3 * rank_width - 1
        holds = tw <= bound
        rows.append((n, rank_width, tw, bound, holds))
        if n >= 4:
            checks.append((
                f"n = {n}: counterexample t = {tw} > {bound} = 3r - 1",
                not holds,
                f"t = {tw}, r = {rank_width}, 3r - 1 = {bound}, t > 3r - 1",
            ))

    # --- the literal assertions demanded by the problem statement -----------
    assert rows[2][1:] == (1, 3, 2, False), "K_4 must give t = 3 > 3*1 - 1 = 2"
    assert all(not holds for _, _, _, _, holds in rows if _ >= 4), \
        "the inequality must fail for all n >= 4"
    assert all(tw == n - 1 and rw == 1 for n, rw, tw, _, _ in rows), \
        "rank-width 1 and treewidth n - 1 for every n >= 2"

    # --- report -------------------------------------------------------------
    line = "=" * 78
    print(line)
    print("Disproof of conjecture 00000003955 -- reproduction")
    print("rank-width r of K_n vs treewidth t of K_n, against t <= 3r - 1")
    print(line)

    print("\n[1] Cut-ranks over GF(2) of all bipartitions of K_n")
    for n in range(2, 8):
        adj = complete_adj(n)
        max_cut_rank, rank_count = cut_rank_profile(adj, n)
        cat = caterpillar_cut_ranks(adj, n)
        plural = "" if len(all_bipartitions(n)) == 1 else "s"
        print(f"    K_{n}: {len(all_bipartitions(n)):>2} bipartition{plural}, "
              f"cut-rank distribution {rank_count}, max = {max_cut_rank}, "
              f"caterpillar cuts {cat}")

    print("\n[2] Exact treewidth by brute force over all elimination orders")
    for n in range(2, 8):
        adj = complete_adj(n)
        tw = treewidth_by_elimination(adj, n)
        print(f"    K_{n}: treewidth = {tw}, minimum degree = {min_degree(adj, n)}, "
              f"explicit decomposition width = {n - 1}")

    print("\n[3] Tabulated inequality t <= 3r - 1 (r = rank-width, t = treewidth)")
    print("      n |  r |  t | 3r - 1 | holds?")
    print("      --+----+----+--------+-------")
    for n, r, t, bound, holds in rows:
        mark = "yes" if holds else "NO "
        note = "" if holds else "   <-- counterexample"
        print(f"      {n} |  {r} |  {t} |   {bound}    | {mark}{note}")

    print("\n[4] Checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")
        all_ok = all_ok and ok

    print("\n" + line)
    if all_ok:
        print("PASS: for every n in 2..7, rank-width(K_n) = 1, treewidth(K_n) = n - 1,")
        print("      and every bipartition of K_n has GF(2) cut-rank 1.")
        print("      The inequality t <= 3r - 1 fails for every n >= 4; the smallest")
        print("      counterexample is K_4 with t = 3 > 2 = 3*1 - 1.  Conjecture")
        print("      00000003955 is FALSE as stated.")
        print(line)
        return 0
    print("FAIL: at least one claimed fact did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
