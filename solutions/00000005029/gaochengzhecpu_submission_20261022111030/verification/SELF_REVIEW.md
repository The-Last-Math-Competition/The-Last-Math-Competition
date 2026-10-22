# Author-agent adversarial self-review: 00000005029

Verdict: PASS

# 5029: critical sparse random graphs do not have the forest axioms as their limiting theory

## Exact scope

The bilingual source is `round5/source/00000005029.md`. Its critical clause says that G(n,c/n) at c=1 has the forest axioms as its convergent limiting theory. We disprove this clause by a single necessary first-order forest axiom: no three vertices form a triangle.

The graph sentence is

    forall x,y,z, not (Adj(x,y) and Adj(y,z) and Adj(z,x)).

In a simple graph these three adjacencies already force distinct vertices. Every forest satisfies this sentence. If the forest axioms formed the limiting theory, its probability would tend to one. We prove it stays at most 49/50 on an unbounded sequence of the genuine models G(n,1/n). This directly contradicts the sentence-level assertion; it does not rely only on acyclicity, which would involve infinitely many cycle exclusions. The separate real Mathlib forest-event bound is also proved. We do not address the source's supercritical giant-component clause, and do not formalize first-order syntax in Lean.

## Complete mathematical argument

Let h >= 1 and n=3h. Partition the actual vertex set into three blocks of h vertices. For each triple t=(a,b,c), with one vertex from each block, let E_t be the event that its three actual graph edges are present. There are h^3 such triangles. In G(n,1/n), P(E_t)=n^(-3), so the sum of their probabilities is 1/27.

Distinct such triples have either no common edge, or precisely one common edge. Their joint event therefore has probability respectively n^(-6) or n^(-5). To bound all ordered distinct pairs, overcount the first kind by all h^6 ordered pairs. Any shared edge is one of the three block-pair types. Fixing the two corresponding coordinates in both triples leaves four freely chosen coordinates overall, so each type has h^4 ordered pairs, including harmless overcounts. Consequently,

    sum_(t != s) P(E_t intersect E_s)
       <= h^6/n^6 + 3 h^4/n^5
        = 1/729 + 1/(81h).

The ordered-pair version of the second Bonferroni bound is

    P(union E_t) >= sum P(E_t) - sum_(t != s) P(E_t intersect E_s).

This version intentionally subtracts both orientations, so there is no missing factor of 1/2. It is weaker than the usual unordered-pair inequality and is sufficient here. The formal proof derives it pointwise from actual event indicators by choosing any witnessed event and charging every other witnessed event to an ordered pair.

Since h >= 1,

    P(at least one selected actual triangle)
       >= 1/27 - 1/729 - 1/(81h)
       >= 17/729 > 1/50.

Thus the probability of an actual triangle anywhere in the graph is at least 1/50, and the probability of the displayed triangle-free sentence is at most 49/50 for every n=3h. The vertex counts tend to infinity. A sequence bounded above by 49/50 cannot converge to one. Hence the claimed forest limiting theory fails.

## Actual Lean model and bridge

`round5/drafts/00000005029/lean/Main.lean` is self-contained and uses Lean 4.19 with official Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- `V m = Fin 3 x Fin (m+1)` is the actual vertex set, with cardinality `Q m = 3*(m+1)`.
- The actual probability mass function starts with uniform assignments `Sym2 (V m) -> Fin (Q m)`, then maps each assignment to a genuine Mathlib `SimpleGraph`. Distinct vertices are adjacent exactly when their unordered-pair coordinate is zero. Auxiliary diagonal coordinates do not affect the graph.
- `graphPMF` is this actual mapped PMF. `graphProbability` is its finite event probability, obtained from the PMF's canonical outer measure and converted to a real number. On finite sets this is the ordinary finite sum. `graphProbability_eq` proves exact equality to normalized counting on the assignment space; counting is not substituted for an unrelated distribution.
- `sample_atom` proves full uniform assignment masses factor as a product of coordinate masses. More strongly, `independent_edge_patterns` proves that EVERY finite family of actual nonloop graph edges, with an ARBITRARY prescribed present/absent Boolean pattern, has the product probability with success parameter exactly `1/Fintype.card(V m)`. Thus this is genuinely G(n,1/n), including absent-edge independence, not a law matching only three-edge marginals.
- The independent-pattern theorem is derived by enumerating all allowed coordinate functions using `Fintype.piFinset`, counting the allowed value sets `{0}` and `univ.erase 0`, and normalizing their actual cardinalities.
- `triangleEdges t` is an actual finite set of three unordered vertex pairs. Its cardinality is proved to be three. `actual_triangle` maps every event witness to three genuine adjacency proofs in the actual random graph.
- `joint_edges_card` computes the actual union of distinct triangles' edge sets as five or six, after exhaustive symbolic cases on the three coordinate equalities. These are arbitrary finite-type coordinates, not a finite-size approximation.
- The three double-sum overlap counts are proved exactly as h^4 by summing true equality indicators over actual triple indices. The upper bound includes all overcount terms and all ordered distinct event pairs.
- `graph_triangle_lower` is the uniform positive lower bound for the actual graph event. `trianglefree_probability_upper` applies to the literal three-adjacency graph property. `triangle_not_acyclic` constructs a genuine Mathlib three-edge cyclic walk and proves it satisfies Mathlib `Walk.IsCycle`; it rules out actual `SimpleGraph.IsAcyclic` and yields `forest_probability_upper`.
- `vertex_card_tends_atTop`, `trianglefree_not_tends_one`, and `forest_not_tends_one` establish the unbounded-size and nonconvergence statements. The subsequence n=3(m+1) suffices: any asserted full-size limit would have the same limit on this unbounded subsequence.

## Adversarial review

1. **Wrong graph law?** No. The proof includes every finite present/absent edge pattern with the exact independent Bernoulli product mass. The edge probability is 1/n, not 1/(n-1), and the sample contains every potential unordered pair.
2. **Unused diagonal randomness changes the model?** It does not: the map enforces no loops, and the proved full pattern probabilities on all nonloop edges characterize the finite Erdos-Renyi law exactly. No conditioning occurs.
3. **Surrogate triangle count?** No. All selected events require three actual original edge coordinates, and every witness is formally converted into three actual graph adjacencies.
4. **Degenerate triangle or parallel edges?** No. The blocks have distinct first coordinates. `triangleEdges_card` and category noncollision lemmas prove the three actual unordered edges are different. Arbitrary `HasTriangle` witnesses are also proved incompatible with real acyclicity by a genuine three-cycle.
5. **Pair count loses multiplicities or a factor of two?** The formal Bonferroni inequality uses ordered pairs and the upper bound uses ordered pairs. This yields the stated weaker constant 1/50. There is no transfer from an unordered estimate.
6. **Can two different selected triangles share two edges?** No. The exact symbolic union-cardinality theorem proves union size five or six for every pair of unequal triple indices. All coordinate-equality cases are checked by Lean.
7. **Can small h invalidate the numerical bound?** No. h=m+1 >= 1 throughout. The weakest bound is 17/729 > 1/50, including the smallest n=3 case.
8. **Rare finite counterexample instead of an asymptotic result?** No. The fixed lower bound holds for every m and actual vertex counts tend to infinity. Both nonconvergence theorems use explicit threshold 99/100 to contradict the universal upper bound 49/50.
9. **Forest probability versus a first-order limiting theory?** We separately bound the single first-order necessary axiom "no triangles"; no exchange of infinite conjunction and limiting probability is used. Actual `IsAcyclic` is an additional bridge, not the sole logical argument.
10. **Claiming to refute every subclause?** No. Refuting the critical forest-theory clause suffices to disprove the conjecture; the supercritical assertion remains outside the submission's scope.
11. **Independent finite check?** The verifier was developed separately by the parent agent and copied unchanged from `round14/parent_checks/5029_exact.py`. It enumerates ALL actual graph edge subsets for n=3 and n=6 with their nonuniform Bernoulli masses, then checks all selected triangle overlaps for block sizes 1 through 8 using exact integers/rationals. It is a consistency check, not an oracle used by Lean.

## Reproducibility

`round14/graph/check5029.py` records actual strict warning-as-error Lean checking, a complete lake build, and the exact verifier run. Raw outputs, timings, commands, working directories, exit codes and Main.lean SHA256 are saved in `5029-result.json` and the three corresponding logs. Key theorem axioms are printed by Lean and must be only propext, Classical.choice, and Quot.sound. No proof holes or custom axioms are permitted.


Reviewed artifact hashes:

- Main.lean: `074bb694afd2a38ceccae366fb4f11796d2f4665be7ec77934f95f90befd2061`
- main.tex: `944c3babc7761a481da09803a350ee16dee317916a583ce9147216d7c2f2a4e6`
- main.pdf: `079fe30f9c7107451cf99ce324539bb0258e3d97422a6f851ca25f4f86b7600a`
- SOURCE.md: `27cb3ea107abf110ebe5467bd3b18d50a53b6d96eb181d77a7eb8ab1af8e4682`
