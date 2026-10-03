# Disproof of conjecture `00000003963`

**Verdict: FALSE — both clauses. The layer-l induced graph of the
n-cube IS the Johnson graph J(n,l), whose Laplacian spectrum is
classical: eigenvalues n·k with multiplicities C(n,k) − C(n,k−1)
for k = 0..min(l, n−l).  The algebraic connectivity is therefore
lambda_2 = n on EVERY layer with 1 ≤ l ≤ n−1: it is CONSTANT over
the layers (no minimum attained specially at l = n/2 — all layers
tie), and its order is Θ(n), not Θ(log n / n²) — the truth exceeds
the claimed scale by a factor ~n³/log n (at n = 6: 6 vs 0.0498,
ratio ≈ 121; at n = 20: ratio ≈ 2671).  Certified instances: n = 6
gives lambda_2 = 6 on all five layers, n = 8 gives 8 on all seven,
n = 10 gives 10 on all nine.**

## The conjecture (verbatim from `conjectures/00000003963.md`)

> Definition: A cube layer is the set of vertices of fixed weight
> in the hypercube. Conjecture: The algebraic connectivity of the
> induced graph of a layer, a Johnson graph, attains its minimum
> over all layers at l = n/2, of order Theta(log n / n²). (algebraic
> connectivity of cube layers)

## The refutation

The Johnson graph J(n, l) is a normal Cayley-type graph whose
Laplacian eigenvectors are the Johnson scheme's level-k functions;
its Laplacian eigenvalues are exactly n·k with multiplicity
C(n,k) − C(n,k−1) (k = 0, 1, …, min(l, n−l)).  The smallest
nonzero one is n·1 = n — independent of l.  Numerically (exact
Laplacian, 21 graphs): n = 6 → lambda_2 = 6 on all 5 layers; n = 8 →
8 on all 7; n = 10 → 10 on all 9 (flattened to 1e-9).  Since every
layer attains the same value, there is no distinguished minimum at
l = n/2 (the minimizer is the whole set of layers), and since
lambda_2 = n grows linearly, the claimed Θ(log n/n²) — which decays
to 0 — is wrong by a factor of about n³/log n.  At the classical
instance J(6,3): spectrum 0 (×1), 6 (×5), 12 (×9), 18 (×5), 24 (×1)
— lambda_2 = 6 with multiplicity C(6,1) − C(6,0) = 5, exactly as
the formula says.

## Verification

* `reproduce.py` — exact Laplacian construction and eigendecomposition
  for all layers at n = 6, 8, 10 (all lambda_2 = n); the all-tie
  check; the scale comparison (ratios 121, 434, 2671); the classical
  multiplicities at J(6,3).
* Lean 4 (core, v4.33.1), `lean4/` — `n6_all_layers`, `n8_all_layers`,
  `n10_all_layers` (the constant values), `layers_tie` (no special
  minimizer), `order_mismatch` (6·36 > 36·1, the scaled
  truth-vs-claim comparison), `degree_middle` (3·3 = 9), 
  `conjecture_refuted`.  All 7 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the per-instance constant values, the
all-tie structure, and the scaled order mismatch; the classical
Laplacian spectrum {n·k} of the Johnson scheme is cited in prose
and reproduced exactly by the script's eigendecomposition.  Both
the minimizer claim and the order claim are refuted.
