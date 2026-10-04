# Disproof of pointwise ceiling sharpness in 00000008822

At two equality constraints, the stated ceiling formula is2. The source simultaneously asserts the actual extreme-point rank law r(r+1)/2≤2, which forces integral rank≤1. Thus no actual SDP instance can attain the stated ceiling value under the source's rank law. The first two assertions are incompatible at m2. The correct integer bound from that inequality uses floor. Attainment at triangular constraint counts is not denied; the scope is pointwise sharpness of the stated function of m. The parked minimal-rank-solution clause is unused.

Lean defines actual SDP feasible sets using Matrix.PosSemidef and matrix traces, actual Set.extremePoints and Matrix.rank. It quantifies over every finite matrix dimension and all constraint coefficients, proves the actual ceiling value and incompatibility, and checks an explicit scalar SDP with two equalities and a genuine rank-one extreme point. It does not claim to reprove Pataki's universal rank theorem; the rank law is one of the source conjuncts being refuted jointly.

Reproduce from lean/ using Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Full build prints axiom audits. No admitted proofs, custom axioms or native decision procedures.

The full report is disproof.tex/disproof.pdf. Native compilation was attempted and returned the known platform-directory failure. Existing Tectonic compiled the one-page PDF, rendered and visually checked with no overflow or clipping.
