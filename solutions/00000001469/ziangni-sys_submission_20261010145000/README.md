# Binary Unique Game label symmetry

Conjecture 00000001469 literally requires a unique global two-label solution and a counterexample size larger than 2^40. For every genuine binary edge-permutation Unique Game on a nonempty graph, global complementation preserves every edge satisfaction and the score, while giving a distinct labeling. No optimal or score-based near-optimal solution is unique. This applies to every game on the complete two-vertex graph, contradicting the lower bound.

The report distinguishes this literal requirement from standard UGC computational hardness and states the absence of pinned labels or quotienting. Lean verifies actual graph/game objects, inverse edge constraints, binary permutation symmetry, true objective invariance, distinct solutions, universal no-uniqueness and the small graph.

Reproduce using Lean 4.19.0: lake update then lake build inside lean. Public Mathlib pin: c44e0c8ee63ca166450922a373c7409c5d26b00b. Final theorem audits are printed. No sorry/admit/native_decide/custom axioms/unsafe; ignored local junctions are conveniences only.
