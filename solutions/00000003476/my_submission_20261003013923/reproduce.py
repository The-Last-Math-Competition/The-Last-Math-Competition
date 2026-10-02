#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003476.

Floyd-Warshall all-pairs distances from scratch:
  1. W(K5) = 10.
  2. Subdividing ANY edge of K5 increases W to 19 (all 10 edges).
  3. Betweenness of every K5 edge is 0 < 5/4, so the conjecture's
     criterion predicts a decrease in all 10 cases and is wrong in all.
Exit 0 iff all checks pass.
"""
import sys
from itertools import combinations


def wiener(n, edges):
    INF = 99
    dist = [[INF] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for a, b in edges:
        dist[a][b] = dist[b][a] = 1
    for k in range(n):
        for i in range(n):
            for j in range(n):
                dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j])
    return sum(dist[i][j] for i in range(n) for j in range(n) if i < j)


def main():
    n = 5
    edges5 = list(combinations(range(n), 2))
    w0 = wiener(n, edges5)
    print(f"W(K5) = {w0}")
    assert w0 == 10

    wrong = 0
    for e in edges5:
        sub = [(a, b) for a, b in edges5 if (a, b) != e]
        x = n
        sub = sub + [(e[0], x), (x, e[1])]
        w1 = wiener(n + 1, sub)
        assert w1 == 19, (e, w1)
        # betweenness of e in K5: 0 (all pairs adjacent)
        betw = 0
        predicted_decrease = betw * 4 < n  # betweenness < n/4
        actual_decrease = w1 < w0
        assert predicted_decrease and not actual_decrease
        wrong += 1
    print(f"subdividing any of the 10 edges: W goes 10 -> 19 (increase);")
    print(f"criterion predicted decrease in {wrong}/10 cases and is wrong in all")
    assert wrong == 10

    print("ALL CHECKS PASS — betweenness criterion fails on K5")
    return 0


if __name__ == "__main__":
    sys.exit(main())
