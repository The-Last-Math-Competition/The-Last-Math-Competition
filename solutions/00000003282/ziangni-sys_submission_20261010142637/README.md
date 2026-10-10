# Proof of 00000003282

The positive-real Gamma function is strictly log-convex, and the normalized Bohr–Mollerup hypotheses characterize it uniquely. Every positive log-convex solution of the Gamma recurrence is exactly f(1) times Gamma; normalization at one therefore fixes the multiplicative constant to one.

The strictness argument uses log Gamma(x) = log Gamma(x+1) - log x: translated log Gamma is convex, and negative log is strictly convex. The report gives the complete existence and uniqueness proof, with all characterizing hypotheses explicit.

## Contents

- `report.tex`, `report.pdf`: complete proof and precise positive-real scope.
- `lean/Main.lean`: actual Mathlib Gamma strictness, characterization, uniqueness, and rescaling classification.
- `VERIFICATION.md`: build, axiom, and PDF validation.

## Reproduce

Use Lean 4.19.0 and run `lake build` in `lean/`. The public Mathlib dependency is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The checked-in manifest records public transitive dependency pins. Caches and build outputs are excluded.

Mathlib's proved Bohr–Mollerup theorem is used explicitly; it is not an assumed hypothesis or custom axiom. Strict log-convexity alone is not asserted to imply uniqueness.
