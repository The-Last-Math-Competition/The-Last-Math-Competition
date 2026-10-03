# Disproof of conjecture `00000004091`

**Verdict: FALSE (polynomial clause) — b₁(Conf₁(Γ)) = b₁(Γ) = E − V + 1 is not a function of the chromatic number at all: the 4-cycle C₄ and the path P₄ are both bipartite (χ = 2) yet b₁(C₄) = 1 ≠ 0 = b₁(P₄).  No polynomial in χ of degree exactly n = 1 — or of any degree — exists.  Moreover the two clauses are jointly incoherent: the barycentric subdivision of C₃ is the 6-cycle, so subdivision-invariance preserves b₁ = 1 while χ drops from 3 to 2, and the bipartite class alone (χ = 2) already carries both b₁ = 0 and b₁ = 1.**

## The conjecture (verbatim from `conjectures/00000004091.md`)

> Definition: The unordered configuration space Conf_n(X) is the
> quotient space of n pairwise distinct points on X. Conjecture: For
> a graph Γ the first Betti number of Conf_n(Γ) is invariant under
> barycentric subdivision and is a polynomial in the chromatic
> number of the graph of degree exactly n. (subdivision invariance
> of graph configuration Betti numbers)

## The refutation

At n = 1 the configuration space of one point is the graph itself:
Conf₁(Γ) = Γ, so b₁(Conf₁(Γ)) = b₁(Γ) = E − V + 1, the cycle rank.
The certified pair:

* **C₄**: E = 4, V = 4, b₁ = 4 + 1 − 4 = 1 (kernel-certified);
* **P₄**: E = 3, V = 4, b₁ = 3 + 1 − 4 = 0 (kernel-certified).

Both graphs are bipartite — every even cycle and every tree is
2-colorable — so both have chromatic number 2.  A polynomial in χ
takes equal values at equal χ; the Betti numbers differ: b₁ is not
a function of the chromatic number, hence not a polynomial of
degree exactly n = 1 nor of any degree.

The subdivision clause makes the situation worse, not better: the
barycentric subdivision of C₃ is the 6-cycle, so subdivision
preserves b₁ = 1 (both are homotopy circles) while the chromatic
number drops from 3 to 2 — the invariant b₁ cannot be a
nonconstant polynomial in a χ that the subdivision itself changes.
And within the fixed class χ = 2, b₁ already varies (0 for trees,
1 for even cycles, unbounded for multi-cyclic bipartite graphs).

## Verification

* `reproduce.py` — the cycle-rank computation, the bipartiteness
  checks, and the C₃ → C₆ subdivision conflict.
* Lean 4 (core, v4.33.1), `lean4/` — `b1_C4` (4+1−4 = 1),
  `b1_P4` (3+1−4 = 0), `betti_differ` (1 ≠ 0), `same_chromatic`,
  `conjecture_refuted`.  All 5 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the cycle ranks and their separation; that C₄
and P₄ are bipartite (χ = 2) is elementary graph theory, cited in
prose and checked by the script's 2-coloring.  The polynomial-in-χ
clause is refuted at n = 1; no claim is made about n ≥ 2 beyond
the incoherence the n = 1 base case already induces.
