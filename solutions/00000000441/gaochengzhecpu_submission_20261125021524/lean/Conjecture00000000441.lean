/-
  Conjecture00000000441.lean
  Complete Core Lean 4.19.0 formalization and disproof of Conjecture 00000000441:
  "Multisymmetric functions form the ring of symmetric functions in several sets of variables.
   Conjecture: The transition matrix of the multisymmetric monomial basis is triangular with
   determinant a power of two; and the exponent is a function of the number of variable sets."
-/

import Conjecture00000000441.LinearAlgebra
import Conjecture00000000441.Multisymmetric
import Conjecture00000000441.Counterexamples

namespace Conjecture00000000441

/-- A transition matrix `M` satisfies the matrix-level claim of Conjecture 00000000441
    (under its most permissive interpretation: triangular up to arbitrary independent
    permutations of row and column bases, and determinant `± 2^k` for some `k ∈ ℕ`). -/
def SatisfiesTriangularPowerOfTwo {N : Nat} (M : Mat N) : Prop :=
  IsPermTriangular M ∧ IsPowerOfTwoUpToSign (det M)

/-! ### 1. Positive / Non-Vacuity Regimes (Explaining Small-Parameter Behavior) -/

/-- Non-vacuity Theorem 1: In `r = 2` variable sets at multidegrees `d = (1, 1)` and `d = (2, 1)`,
    the elementary-to-monomial transition matrices `M(e, m)_{(1,1)}` and `M(e, m)_{(2,1)}`
    genuinely satisfy `SatisfiesTriangularPowerOfTwo` (with `det = -1` and `det = 1`). -/
theorem positive_elementary_low_degrees :
    SatisfiesTriangularPowerOfTwo M_e_11 ∧ SatisfiesTriangularPowerOfTwo M_e_21 := by
  refine ⟨⟨permTri_M_e_11, ?_⟩, ⟨permTri_M_e_21, ?_⟩⟩
  · rw [det_M_e_11]; exact ⟨0, Or.inr rfl⟩
  · rw [det_M_e_21]; exact ⟨0, Or.inl rfl⟩

/-- Non-vacuity Theorem 2: In `r = 2` variable sets at `d = (1, 1)`, `d = (2, 1)`, and `d = (2, 2)`,
    the power-sum-to-monomial transition matrices `M(p, m)_d` are lower triangular with exact
    power-of-two determinants `1 = 2^0`, `2 = 2^1`, and `32 = 2^5`. -/
theorem positive_powerSum_bounded_two :
    (IsLowerTri M_p_11 ∧ det M_p_11 = (2 : Int) ^ 0) ∧
    (IsLowerTri M_p_21 ∧ det M_p_21 = (2 : Int) ^ 1) ∧
    (IsLowerTri M_p_22 ∧ det M_p_22 = (2 : Int) ^ 5) := by
  refine ⟨⟨checkLowerTriBool_sound 2 rows_p_11 (by decide), det_M_p_11⟩,
          ⟨checkLowerTriBool_sound 4 rows_p_21 (by decide), det_M_p_21⟩,
          ⟨checkLowerTriBool_sound 9 rows_p_22 (by decide), det_M_p_22⟩⟩

/-! ### 2. Definitive Disproof Across All Standard Multisymmetric Bases -/

/-- **Disproof for the Elementary Multisymmetric Basis `{e_Λ}`:**
    1. At `r = 3, d = (1, 1, 1)` (`N = 5`), `M(e, m)_{(1,1,1)}` is verified as the exact polynomial
       basis transition matrix with `det = -2` (`|det| = 2^1`), yet `¬IsPermTriangular M_e_111`.
    2. At `r = 2, d = (2, 2)` (`N = 9`), `M(e, m)_{(2,2)}` is verified as the exact polynomial
       basis transition matrix with `det = 3`, refuting BOTH `IsPermTriangular` and
       `IsPowerOfTwoUpToSign`, and showing `|det|` varies with `d` at fixed `r = 2` (`1 ≠ 3`).
    3. Even restricted to multilinear degree `d = (1, ..., 1)`, at `r = 4` (`N = 15`),
       `det M(e, m)_{(1,1,1,1)} = -96 = -2^5 * 3`, refuting BOTH `IsPermTriangular` and
       `IsPowerOfTwoUpToSign`. -/
theorem disproof_elementary_basis :
    (IsBasisTransition 3 3 (fun j => parts_111.getD j.val [])
        (fun i => ePoly 3 3 [1, 1, 1] (parts_111.getD i.val [])) M_e_111 ∧
      det M_e_111 = -2 ∧ ¬IsPermTriangular M_e_111) ∧
    (IsBasisTransition 4 2 (fun j => parts_22.getD j.val [])
        (fun i => ePoly 4 2 [2, 2] (parts_22.getD i.val [])) M_e_22 ∧
      det M_e_22 = 3 ∧ ¬IsPermTriangular M_e_22 ∧ ¬IsPowerOfTwoUpToSign (det M_e_22)) ∧
    (det M_e_1111 = -96 ∧ ¬IsPermTriangular M_e_1111 ∧ ¬IsPowerOfTwoUpToSign (det M_e_1111)) :=
  ⟨⟨basis_e_111, det_M_e_111, not_permTri_M_e_111⟩,
   ⟨basis_e_22, det_M_e_22, not_permTri_M_e_22, not_pow2_M_e_22⟩,
   ⟨det_M_e_1111, not_permTri_M_e_1111, not_pow2_M_e_1111⟩⟩

/-- **Disproof for the Complete Homogeneous Multisymmetric Basis `{h_Λ}`:**
    1. Already at `r = 2, d = (1, 1)` (`N = 2`), `M(h, m)_{(1,1)}` is not permutation-triangular.
    2. At `r = 2, d = (2, 2)` (`N = 9`), `det M(h, m)_{(2,2)} = 3`, refuting both triangularity
       and power-of-two determinant.
    3. In multilinear degree at `r = 4, d = (1, 1, 1, 1)` (`N = 15`), `det M(h, m)_{(1,1,1,1)} = 96`,
       refuting both triangularity and power-of-two determinant. -/
theorem disproof_completeHomogeneous_basis :
    (IsBasisTransition 2 2 (fun j => parts_11.getD j.val [])
        (fun i => hPoly 2 2 [1, 1] (parts_11.getD i.val [])) M_h_11 ∧
      ¬IsPermTriangular M_h_11) ∧
    (IsBasisTransition 4 2 (fun j => parts_22.getD j.val [])
        (fun i => hPoly 4 2 [2, 2] (parts_22.getD i.val [])) M_h_22 ∧
      det M_h_22 = 3 ∧ ¬IsPermTriangular M_h_22 ∧ ¬IsPowerOfTwoUpToSign (det M_h_22)) ∧
    (det M_h_1111 = 96 ∧ ¬IsPermTriangular M_h_1111 ∧ ¬IsPowerOfTwoUpToSign (det M_h_1111)) :=
  ⟨⟨basis_h_11, not_permTri_M_h_11⟩,
   ⟨basis_h_22, det_M_h_22, not_permTri_M_h_22, not_pow2_M_h_22⟩,
   ⟨det_M_h_1111, not_permTri_M_h_1111, not_pow2_M_h_1111⟩⟩

/-- **Disproof for the Power-Sum Multisymmetric Basis `{p_Λ}` (and Augmented Monomial Basis `{m̃_Λ}`):**
    1. Even at fixed `r = 2` among multidegrees with power-of-two determinants, no function `f(r)`
       of `r` alone can govern the exponent (`det M(p, m)_{(1,1)} = 1 = 2^0`,
       `det M(p, m)_{(2,1)} = 2 = 2^1`, `det M(p, m)_{(2,2)} = 32 = 2^5`).
    2. At `r = 2, d = (3, 1)` (`N = 7`), `M(p, m)_{(3,1)}` is lower triangular with `det = 12 = 2^2 * 3`,
       which is NOT a power of two.
    3. Universally for EVERY `r ≥ 1`, on any multidegree containing `starPart r` (in particular
       `d'_r = (3, 1, ..., 1)`), `3` divides `det M(p, m)` and `det M(p, m)` is never `± 2^k`. -/
theorem disproof_powerSum_basis :
    (¬∃ f : Nat → Nat,
        det M_p_11 = (2 : Int) ^ (f 2) ∧ det M_p_21 = (2 : Int) ^ (f 2)) ∧
    (IsBasisTransition 4 2 (fun j => parts_31.getD j.val [])
        (fun i => pPoly 4 2 [3, 1] (parts_31.getD i.val [])) M_p_31 ∧
      IsLowerTri M_p_31 ∧ det M_p_31 = 12 ∧ ¬IsPowerOfTwoUpToSign (det M_p_31)) ∧
    (∀ r : Nat, 1 ≤ r → ∀ {N : Nat} (parts : Fin N → VecPart) (M : Mat N),
      IsLowerTri M → (∀ i : Fin N, M i i = autOrder (parts i)) →
      (∃ k : Fin N, parts k = starPart r) → ¬IsPowerOfTwoUpToSign (det M)) := by
  refine ⟨?_, ⟨basis_p_31, lowerTri_M_p_31, det_M_p_31, not_pow2_M_p_31⟩, ?_⟩
  · rintro ⟨f, h1, h2⟩
    rw [det_M_p_11] at h1
    rw [det_M_p_21] at h2
    omega
  · intro r hr N parts M hlo hdiag hstar
    exact (powerSum_all_r_not_power_of_two r hr parts M hlo hdiag hstar).2

/-- **Master Theorem Resolving Conjecture 00000000441 (FALSE):**
    Across all three canonical multiplicative bases of multisymmetric functions (`{e_Λ}`, `{h_Λ}`,
    `{p_Λ}`), the conjectured simultaneous properties (triangular transition matrix with the
    multisymmetric monomial basis `{m_Λ}`, determinant a power of two, and exponent depending
    solely on the number of variable sets `r`) fail:
    `M(e, m)_{(2,2)}`, `M(h, m)_{(2,2)}`, and `M(p, m)_{(3,1)}` (all in `r = 2` variable sets,
    verified directly from multivariate polynomial expansions) violate `SatisfiesTriangularPowerOfTwo`. -/
theorem conjecture_00000000441_disproved :
    ¬SatisfiesTriangularPowerOfTwo M_e_22 ∧
    ¬SatisfiesTriangularPowerOfTwo M_h_22 ∧
    ¬SatisfiesTriangularPowerOfTwo M_p_31 ∧
    ¬SatisfiesTriangularPowerOfTwo M_e_111 ∧
    ¬SatisfiesTriangularPowerOfTwo M_e_1111 ∧
    ¬SatisfiesTriangularPowerOfTwo M_h_1111 := by
  refine ⟨fun h => not_pow2_M_e_22 h.2,
          fun h => not_pow2_M_h_22 h.2,
          fun h => not_pow2_M_p_31 h.2,
          fun h => not_permTri_M_e_111 h.1,
          fun h => not_pow2_M_e_1111 h.2,
          fun h => not_pow2_M_h_1111 h.2⟩

end Conjecture00000000441
