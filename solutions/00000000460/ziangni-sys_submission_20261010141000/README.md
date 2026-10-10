# Constant matching-statistic disproof

Conjecture00000000460 asserts a common asymptotic distribution for all bounded-degree equivariant symmetric-function statistics on uniform perfect matchings. Constants0 and1 are degree-zero equivariant symmetric functions and have deterministic distinct laws at every size. A common bounded continuous coefficient test separates them by1.

The report explains the literal scope, absence of centering/scaling assumptions, actual involutive matching representation, stable symmetric-polynomial realization, and probability laws. Lean verifies these objects, finite uniform PMFs, relabeling equivariance, bounded degrees, pushforward laws and permanent separation.

Reproduction: with Lean4.19.0, run lake update then lake build inside lean. Public Mathlib requirement/manifest pin c44e0c8ee63ca166450922a373c7409c5d26b00b. The build prints final theorem axiom audits. No sorry/admit/native_decide/custom axioms/unsafe. Local ignored junctions are conveniences only.
