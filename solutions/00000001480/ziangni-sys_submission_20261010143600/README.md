# A zero-gap geometric program with duplicate constraints

Conjecture 00000001480 claims log-linear independence is necessary and sufficient for zero duality gap on positive-definite matrix cones. The one-by-one program min x, x>0, subject to x^(-1)≤1 twice has dependent logarithmic constraints and zero gap. Its original primal and dual optima are both 1; after logarithmic transformation both optima are 0. The report derives the genuine unrestricted-coordinate Lagrangian infimum.

Lean verifies actual positive-definite matrices [exp y], monomial/logarithmic bridges, feasibility, the true Lagrangian infimum at the witness, optimal original primal/dual bounds, and linear dependence.

Reproduce using Lean 4.19.0: lake update then lake build inside lean. The public Git requirement and manifest pin Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Printed audits verify standard axioms only. No sorry/admit/native_decide/custom axioms/unsafe. Ignored local package junctions are conveniences only.
