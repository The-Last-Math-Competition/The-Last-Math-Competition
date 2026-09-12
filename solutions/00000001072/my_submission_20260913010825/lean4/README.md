# Lean 4 certificate — disproof of conjecture 00000001072

Core-only Lean 4 project (no Mathlib). It machine-checks both counterexamples.

## Contents

- `Main.lean` — namespace `Tlmc1072`:
  - `G n k q` implementing the conjecture's formula
    `G(n,k,q) = q^((n-k)*k) * [n choose k]_q` (with the Gaussian binomial
    `[n choose k]_q = prod_{i=1..k} (q^(n-k+i) - 1) / (q^i - 1)`);
  - `G212 : G 2 1 2 = 6`, `G213 : G 2 1 3 = 12`, `G312 : G 3 1 2 = 28` (all `rfl`);
  - `refute_I : ¬((2:ℕ) ∣ 2^1 - 1) ∧ ¬((2:ℕ) ∣ 2^2 - 1) ∧ ((2:ℕ) ∣ 6)`
    (counterexample I: the prime 2 divides G(2,1,2)=6 but divides no q^i−1, i ≤ 2);
  - `refute_II : (5:ℕ) ≤ 3^2 - 1 ∧ ¬(5 ∣ 12) ∧ (7:ℕ) ≤ 3^2 - 1 ∧ ¬(7 ∣ 12) ∧ 7 < 3^2 - 1`
    (counterexample II: 5 and 7 are ≤ q^n−1 = 8 but divide neither — spectrum
    is a proper subset, so "exactly" fails).
- `Check.lean` — `#eval` checks of the values and `#print axioms` audit.

## Build and verify

Requires `elan` with toolchain `leanprover/lean4:v4.33.1` (see `lean-toolchain`).

```sh
cd lean4
lake build
lake env lean Check.lean
```

(`lake env lean Check.lean` is needed so that the local module `Main` resolves.)

## Axiom audit result

Every theorem prints `does not depend on any axioms`, e.g.

```
'Tlmc1072.G212' does not depend on any axioms
'Tlmc1072.G213' does not depend on any axioms
'Tlmc1072.G312' does not depend on any axioms
'Tlmc1072.q21' does not depend on any axioms
'Tlmc1072.q22' does not depend on any axioms
'Tlmc1072.refute_I' does not depend on any axioms
'Tlmc1072.refute_II' does not depend on any axioms
```

All proofs are closed without any tactics that rely on classical reasoning:
the values `G212`, `G213`, `G312`, `q21`, `q22` are closed `rfl` computations,
and the two refutations are built from pure constructor logic (case splits on
the divisibility witness with `Nat.succ.inj` and `Nat.noConfusion`, plus
explicit `Nat.le.step`/`Nat.le.refl` terms for the order facts): zero axioms,
zero `sorry`.
