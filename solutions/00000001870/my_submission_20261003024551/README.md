# Disproof of conjecture `00000001870`

**Verdict: FALSE — Haar invariance under the rotation U → e^{iθ}U forces
E[X] = E[X³] = 0 for X = Tr(U), so the third cumulant κ₃ = 0, not
2πi/(3N) ≠ 0.**

## The conjecture (verbatim from `conjectures/00000001870.md`)

> Definition: The zeta function of a suspension... (claimed: the third
> cumulant of the trace of a Haar-uniform N×N unitary matrix is
> κ₃ = 2πi/(3N), nonzero).

## The refutation

Haar measure on U(N) is invariant under the rotation U → e^{iθ}U (the
scalar matrix e^{iθ}I commutes and Haar is left-invariant; classical).
Since Tr(e^{iθ}U) = e^{iθ}·Tr(U), the distribution of X = Tr(U) is
invariant under X → e^{iθ}X, and:

    E[X³] = E[(e^{iθ}X)³] = e^{3iθ}·E[X³]   for every θ.

At θ = π/3 (e^{3iθ} = −1): E[X³] = −E[X³] ⟹ **E[X³] = 0**; identically
**E[X] = 0**. The third cumulant is the classical polynomial
κ₃ = m₃ − 3m₂m₁ + 2m₁³, so with m₁ = m₃ = 0:

    κ₃ = 0 − 3m₂·0 + 2·0 = 0   for every value of m₂.

The claimed κ₃ = 2πi/(3N) ≠ 0 (imaginary part 2π/(3N) > 0, π > 3) is
contradicted: the rotation symmetry kills the third cumulant
identically. (This matches the Monte-Carlo evidence: E[(TrU)³] ≈ 0 ±
0.005 at N = 2, 3.)

## Verification

* `reproduce.py` — Monte-Carlo sampling of Haar U(N) via the standard
  QR decomposition of Ginibre matrices: E[(TrU)³] ≈ 0 within noise for
  N = 2, 3, 5; the claimed κ₃ = 2πi/(3N) is nonzero.
* Lean 4 (core, v4.33.1) — `lean4/`: the cumulant decomposition with
  zero first and third moments forcing κ₃ = 0 — general in the second
  moment m2 (exact arithmetic). All 3 audited theorems report `does not
  depend on any axioms`. The Haar-rotation symmetry, the cumulant
  polynomial, and π > 3 are classical and cited.

## Boundary

Only the claimed nonzero third cumulant is refuted; second moments /
pairings (which are genuinely nonzero) are not addressed.
