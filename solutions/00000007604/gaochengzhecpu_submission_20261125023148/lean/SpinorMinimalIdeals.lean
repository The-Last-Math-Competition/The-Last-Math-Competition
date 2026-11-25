/-
  SpinorMinimalIdeals.lean
  Root module for the formal resolution of Conjecture 00000007604
  ("Spinors as elements of minimal left ideals: half-dimension power of two,
   complete spectrum, minimal ideal carrier, and matrix realization of the simple module")
  in Core Lean 4.19.0 (zero external dependencies, zero `sorry`, zero `native_decide`).
-/

import SpinorMinimalIdeals.PolyNorm
import SpinorMinimalIdeals.RatField
import SpinorMinimalIdeals.AlgebraicFramework
import SpinorMinimalIdeals.PositiveSplitCl11
import SpinorMinimalIdeals.Counterexamples

namespace SpinorMinimalIdeals

/--
  **Grand Summary Theorem for Conjecture 00000007604:**
  1. **Positive Non-Vacuity (Even Split Regime, `Cl_{1,1}(ℚ) ≅ M_2(ℚ)`, `n = 2`):**
     There exists a primitive idempotent `e = (1 + e_1)/2` whose minimal nonzero left
     ideal `S_{1,1} = Cl_{1,1} · e` has exact dimension `2 = 2^(2/2)`, acts faithfully
     and surjectively via `Cl_{1,1}(ℚ) ≅ M_2(ℚ)` with carrier equal to the first-column
     subspace of `M_2(ℚ)`, and realizes the complete `{+1, -1}` weight spectrum of `e_1`.
  2. **Refutation I — Odd Dimensions (`n = 2m + 1` and `Cl_{1,0}(ℚ)`, `n = 1`):**
     For every `m : Nat`, no natural dimension `d` satisfies `d^2 = 2^(2m+1)`. Concretely,
     every minimal nonzero left ideal `S` of `Cl_{1,0}(ℚ)` has dimension `1` (`¬ dim 2`),
     is NOT faithful, and misses half of the `{+1, -1}` eigenvalue spectrum of `e_1`.
  3. **Refutation II — Even-Dimensional Division-Algebra Obstruction (`Cl_{0,2}(ℚ) ≅ ℍ_ℚ`, `n = 2`):**
     Even when `n = 2` is even and `Q(x_1, x_2) = -x_1^2 - x_2^2` is nondegenerate, every
     minimal nonzero left ideal `S` of `Cl_{0,2}(ℚ)` has dimension `4` (`¬ dim 2 = 2^(2/2)`),
     `Cl_{0,2}(ℚ)` has only trivial idempotents, and `e_1` has no rational eigenvalues on `S`.
  4. **Refutation III — Even-Dimensional Degenerate Quadratic Form (`Λ(ℚ^2) = Cl2 0 0`, `n = 2`):**
     Even when `n = 2` is even (and identically over any field), every minimal nonzero left
     ideal `S` of the exterior Clifford algebra `Λ(ℚ^2)` has dimension `1` (`¬ dim 2 = 2^(2/2)`),
     is nilpotent (`S^2 = 0`, containing no nonzero idempotent), is NOT faithful, and is
     annihilated by all vectors in `V`.
-/
theorem conjecture_00000007604_complete_resolution :
    -- (1) Positive split witness at n = 2 (`Cl_{1,1} ≅ M_2`)
    (Cl11Alg.IsMinimalLeftIdeal Cl11.SpinorIdeal ∧
     HasQDim Cl11Alg Cl11.SpinorIdeal (2 ^ (2 / 2)) ∧
     Cl11Alg.IsFaithfulLeftIdeal Cl11.SpinorIdeal ∧
     (∀ x, Cl11.SpinorIdeal x ↔ M2Q.FirstColumn (Cl11.phi x))) ∧
    -- (2) Universal odd-dimension arithmetic obstruction (`d^2 ≠ 2^(2m+1)`) + `Cl_{1,0}` refutation
    ((∀ m d : Nat, d * d ≠ 2 ^ (2 * m + 1)) ∧
     (∀ S, Cl10Alg.IsMinimalLeftIdeal S →
        HasQDim Cl10Alg S 1 ∧ ¬ HasQDim Cl10Alg S 2 ∧ ¬ Cl10Alg.IsFaithfulLeftIdeal S)) ∧
    -- (3) Even-dimensional nondegenerate division-algebra refutation (`Cl_{0,2} ≅ ℍ_ℚ`, `n = 2`)
    (∀ S, Cl02Alg.IsMinimalLeftIdeal S →
        HasQDim Cl02Alg S 4 ∧ ¬ HasQDim Cl02Alg S (2 ^ (2 / 2))) ∧
    -- (4) Even-dimensional degenerate exterior refutation (`Λ(ℚ^2)`, `n = 2`)
    (∀ S, Ext2Alg.IsMinimalLeftIdeal S →
        HasQDim Ext2Alg S 1 ∧ ¬ HasQDim Ext2Alg S (2 ^ (2 / 2)) ∧
        Ext2Alg.IsNilpotentIdeal S ∧ ¬ Ext2Alg.IsFaithfulLeftIdeal S) := by
  refine ⟨⟨Cl11.spinorIdeal_isMinimalLeftIdeal,
           Cl11.spinorIdeal_hasDim_two,
           Cl11.spinorIdeal_isFaithful,
           Cl11.spinorIdeal_iff_firstColumn⟩,
          ⟨odd_pow_two_not_nat_sq,
           fun S hS =>
             let ⟨h1, hn2, _, hnf, _⟩ := Cl10.refutation_cl10 S hS
             ⟨h1, hn2, hnf⟩⟩,
          fun S hS =>
            let ⟨h4, hn2, _, _⟩ := Cl02.refutation_cl02 S hS
            ⟨h4, hn2⟩,
          fun S hS =>
            let ⟨h1, hn2, hnil, _, hnf, _⟩ := Ext2.refutation_ext2 S hS
            ⟨h1, hn2, hnil, hnf⟩⟩

end SpinorMinimalIdeals
