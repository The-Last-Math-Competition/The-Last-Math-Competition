# Disproof of conjecture `00000003476`

**Verdict: FALSE — in K₅ the betweenness of every edge is 0 < 5/4, yet
subdividing an edge INCREASES the Wiener index from 10 to 19: the "if"
direction of the criterion fails.**

## The conjecture (verbatim from `conjectures/00000003476.md`)

> Definition: The Wiener index is the sum of all-pairs distances, with
> negativity its decrease under graph transformations. Conjecture:
> Subdividing an edge decreases the Wiener index if and only if the
> betweenness of that edge is below one quarter of the vertex count;
> the criterion is given by the cut-load inequality chain and is exact
> for bipartite graphs.

## The counterexample (K₅, n = 5)

1. **Betweenness of every edge of K₅ is 0**: all pairs are adjacent, so
   no shortest path passes through an intermediate vertex. And
   0 < 5/4 — the criterion's hypothesis HOLDS, predicting that
   subdivision DECREASES the Wiener index.
2. **W(K₅) = 10**: all C(5,2) = 10 pairs at distance 1.
3. **Subdividing the edge {0,1}** (replacing it by 0−x−1, six vertices):
   the 15 pairwise distances are
   d(0,1) = 2; d(0,j) = d(1,j) = 1 (j = 2,3,4); d(0,x) = d(1,x) = 1;
   d(x,j) = 2 (j = 2,3,4); d(i,j) = 1 (2 ≤ i < j ≤ 4) — summing to
   **19 > 10**: the Wiener index INCREASED by 9.

The "if" direction (betweenness < n/4 ⟹ subdivision decreases W) is
therefore false, and the displayed characterization (with its
cut-load chain and bipartite exactness) is refuted. In fact subdivision
of ANY edge of ANY complete graph increases W — the criterion fails on
the most basic family.

## Verification

* `reproduce.py` — Floyd–Warshall all-pairs distances from scratch for
  K₅ and every single-edge-subdivision of K₅: W = 10 → 19 (increase 9)
  for every subdivided edge; betweenness of every K₅ edge = 0; the
  criterion predicts a decrease for all 10 edges and is wrong for all
  10.
* Lean 4 (core, v4.33.1) — `lean4/`: both Wiener sums (closed kernel
  computations), the betweenness bound 0 < 5/4, the increase 19 > 10,
  and the refutation of the criterion's "if" direction. All 6 audited
  theorems report `does not depend on any axioms`.

## Boundary

Only the displayed criterion is refuted (via K₅). The cut-load chain,
the bipartite-exactness clause, and other graph families are not
addressed.
