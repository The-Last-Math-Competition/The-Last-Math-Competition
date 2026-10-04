import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# Proof of conjecture 00000000035: a monochromatic Schur triple with `x * y + 1` prime

Conjecture 00000000035 asserts:

> There exists `N` such that any 2-coloring of `[N] = {1, ..., N}` contains a
> monochromatic Schur triple `(x, y, z)` with `x + y = z` and `x * y + 1` prime.

We prove this with the explicit witness `N = 7`. Since `[7]` has only `2^7 = 128`
colorings and only 12 Schur triples (with `x ≤ y` to avoid double counting), the
claim is a finite check, discharged in Lean by `decide`.

Conventions:
- Colors are `Fin 2`.
- Positions are `Fin 7`, with the value `i.val + 1 ∈ [1, 7]`.
- Schur triples allow `x = y` (e.g. `2 + 2 = 4`), following the standard
  combinatorics convention; the conjecture does not require `x ≠ y`.
- The vestigial parameter `k` in the statement's `N(k)` plays no role
  (no `k` appears anywhere else); we read `N(k)` as "some `N`".
-/

namespace Proof35

/-- The finite check at `N = 7`: every 2-coloring of `[7]` contains a monochromatic
Schur triple `x + y = z` (values are `i.val + 1`) with `x * y + 1` prime. -/
theorem schur_prime_7 :
    ∀ c : Fin 7 → Fin 2,
      ∃ x y z : Fin 7,
        (x.val + 1) + (y.val + 1) = z.val + 1 ∧
          c x = c y ∧ c y = c z ∧ Nat.Prime ((x.val + 1) * (y.val + 1) + 1) := by
  decide

/-- Conjecture 00000000035 with the explicit witness `N = 7`. -/
theorem conjecture_00000000035 :
    ∃ N : ℕ, ∀ c : Fin N → Fin 2,
      ∃ x y z : Fin N,
        (x.val + 1) + (y.val + 1) = z.val + 1 ∧
          c x = c y ∧ c y = c z ∧ Nat.Prime ((x.val + 1) * (y.val + 1) + 1) :=
  ⟨7, schur_prime_7⟩

#print axioms conjecture_00000000035

end Proof35
