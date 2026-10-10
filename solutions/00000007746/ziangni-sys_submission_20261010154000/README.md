# Disproof of 00000007746

The first-chaos mixed integral X = (S1(1) + S2(1))/(2 sqrt(2)) uses two freely independent Brownian drivers. Its fourth and sixth moments are 1/8 and 5/64. Their difference is -3/64, contradicting the universal sign assertion in both language versions. The source has no unit-variance normalization or exclusion of order one.

The report identifies the full two-letter Fock operator with the actual first-order integral. Lean defines creation, annihilation, the vacuum, and operator powers on all finite words, then computes the actual vacuum moments and the real coefficient involving sqrt(2). No assumed moment table or finite matrix surrogate is used.

Run `lake build` in `lean/`. Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned publicly. Printed theorem audits contain only standard axioms.
