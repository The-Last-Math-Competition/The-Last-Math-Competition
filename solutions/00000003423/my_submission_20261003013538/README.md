# Disproof of conjecture `00000003423`

**Verdict: FALSE (monotonicity clause) — adding the edge {1,3} to the
path P₃ increases the hitting time H(1 → 2) from 1 to 2 > 1. Adding
edges does NOT decrease hitting times.**

## The conjecture (verbatim from `conjectures/00000003423.md`)

> Definition: The maximum principle of hitting times: suprema on
> graphs. Conjecture: The maximal hitting time of the complete graph is
> n−1, and adding edges decreases hitting time submodularly.

## The counterexample (3 vertices)

Let P₃ be the path 1−2−3 and G = P₃ + {1,3} the triangle.

1. **On P₃:** vertex 1's unique neighbor is 2, so H(1 → 2) = **1**
   exactly (one forced step).
2. **On G (triangle):** the hitting times of the simple random walk
   satisfy H₁ = 1 + H₃/2, H₃ = 1 + H₁/2 (H₂ = 0). The solution is
   H₁ = H₃ = **2**: substitution-certified (2 = 1 + 2/2 in both
   equations), and unique since det [[2,−1],[−1,2]] = 3 ≠ 0
   (kernel-certified).

So **adding the edge {1,3} increased H(1 → 2) from 1 to 2 > 1** — the
"adding edges decreases hitting time" clause fails already on 3
vertices, and with monotonicity gone the submodularity clause is moot.
(The complete-graph clause "max hitting time = n−1" is the classical
K_n fact and is not disputed.)

## Verification

* `reproduce.py` — solves the hitting-time linear systems of P₃ and the
  triangle exactly (fractions), confirming H(1→2) = 1 → 2 under the
  added edge; also brute-forces by Monte-Carlo simulation of the walks.
* Lean 4 (core, v4.33.1) — `lean4/`: the solution substitution, the
  determinant nonvanishing, and the increase 2 > 1; all audited
  theorems report `does not depend on any axioms`. The identification
  of hitting times as the unique solution of the one-step linear
  system is the standard first-step analysis (classical).

## Boundary

Only the monotone-decrease clause is refuted (it fails at n = 3). The
complete-graph extremal clause is classical and not disputed; genuine
submodularity questions are not addressed.
