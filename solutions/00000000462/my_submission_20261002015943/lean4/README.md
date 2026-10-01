# lean4 — zero-axiom machine verification for the disproof of 00000000462

Core Lean 4 only (no Mathlib, no external dependencies).

Contents:
- `Main.lean` — the attack, concretized as pure `Nat` facts:
  - exact spanning-tree counts `tau n = n * (L_{2n} - 2*(-1)^n) / 5` for
    n ∈ {5,6,7,8,9,10,12,15,20,24,40,80} (closed form certified against the
    matrix-tree theorem by `../reproduce.py`);
  - `rate80_below_eight : tau 80 < 8^80` and friends — the exponential growth
    rate is below the eigenvalue ceiling 8 at every sampled size;
  - integer skeletons of the irrational comparisons:
    `alpha^2 = 7+4*sqrt(3) ∈ (8,14)` and `phi^2 = (3+sqrt(5))/2 < 3`;
  - `disproof_462` — the decisive sandwich
    `5^80 < tau 80 * 2^80 ∧ tau 80 < 8^80 ∧ 1 < 48 ∧ 48 < 49`.
- `Check.lean` — `#print axioms` audit of every declaration.

Build and audit:

```
lake build
lake env lean Check.lean
```

Every line must print `... does not depend on any axioms` (25 declarations,
zero axioms, zero `sorry`).
