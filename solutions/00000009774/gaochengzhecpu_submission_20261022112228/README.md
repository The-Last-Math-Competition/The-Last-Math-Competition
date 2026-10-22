# Conjecture 00000009774 — Disproof

On the smooth unit circle, the positive analytic symbol f(θ)=5/4+cos θ has actual n×n Toeplitz matrices with diagonal 5/4 and adjacent diagonals 1/2. Their determinants are (4/3)(1−(1/4)^(n+1)). Consequently log D_n / n tends to zero while log D_n tends to log(4/3)>0. The smooth secondary term does not vanish, and the normalized determinant has a global factor 4/3 without any corners.

`lean/Main.lean` defines actual Laurent coefficients and Mathlib Toeplitz matrices c(i−j), proves the general tridiagonal determinant recurrence by Laplace expansion, proves the formula for every n and positivity, and establishes both limits. It also proves C∞ smoothness and positivity of the symbol. `SmoothSecondaryVanishes` is the necessary universal smooth-case subclause over this positive Laurent-symbol family; `conjecture9774_false` negates it.

Paper-only bridges are explicitly listed: Fourier coefficient integration, circle Hardy-space compression, the circle's smooth geometry, and the mean-log integral. The latter independently gives L=0, while the normalized logarithmic determinant limit is fully formal. The counterexample is unchanged by n versus n+1 size conventions because L=0.

The direct warning-as-error check and axiom audit are in `verification/strict.log`; only propext, Classical.choice and Quot.sound occur. Parent fresh build and PDF checks are separate. Reproduce in `lean/` with `lake env lean -DwarningAsError=true Main.lean` using Lean 4.19.0 and the pinned Mathlib manifest.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed. No prior submission was found by the parent workflow.
