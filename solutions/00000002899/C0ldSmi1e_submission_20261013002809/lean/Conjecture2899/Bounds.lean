import Conjecture2899.Counting
import Conjecture2899.Minimum

namespace Conjecture2899

theorem family_lt_proposed_bound (F : Type*) [Field F] [Fintype F]
    (htwo : (2 : F) ≠ 0) (n : ℕ) (c : ℝ)
    (hlarge : 2 * (c + 1) < (Fintype.card F : ℝ)) :
    ((family F n).card : ℝ) <
      (Fintype.card F : ℝ)^(n+2) * (1-c/(Fintype.card F : ℝ)) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 := ne_of_gt hq
  rw [family_card_real htwo n]
  have hplane : (((Fintype.card F : ℝ)^2 + 2 * Fintype.card F - 1) / 2) <
      (Fintype.card F : ℝ)^2 - c * Fintype.card F := by
    nlinarith [mul_pos hq (show 0 < (Fintype.card F : ℝ) / 2 - c - 1 by linarith)]
  have hp := mul_lt_mul_of_pos_right hplane (pow_pos hq n)
  convert hp using 1
  rw [pow_add]
  field_simp
  ring

theorem normalized_minimum_upper_bound (F : Type*) [Field F] [Fintype F]
    (htwo : (2 : F) ≠ 0) (n : ℕ) :
    (minimumKakeyaSize F (n+2) : ℝ) / (Fintype.card F : ℝ)^(n+2) ≤
      1/2 + 1/(Fintype.card F : ℝ) - 1/(2*(Fintype.card F : ℝ)^2) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 := ne_of_gt hq
  have hmin : (minimumKakeyaSize F (n+2) : ℝ) ≤ ((family F n).card : ℝ) := by
    exact_mod_cast minimum_le_card (family F n) (family_isKakeya F htwo n)
  calc
    _ ≤ ((family F n).card : ℝ) / (Fintype.card F : ℝ)^(n+2) :=
      div_le_div_of_nonneg_right hmin (le_of_lt (pow_pos hq _))
    _ = _ := by
      rw [family_card_real htwo n, pow_add]
      field_simp
      ring

theorem normalized_minimum_upper_bound_in_each_dimension
    (F : Type*) [Field F] [Fintype F] (htwo : (2 : F) ≠ 0)
    (d : ℕ) (hd : 2 ≤ d) :
    (minimumKakeyaSize F d : ℝ) / (Fintype.card F : ℝ)^d ≤
      1/2 + 1/(Fintype.card F : ℝ) - 1/(2*(Fintype.card F : ℝ)^2) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 2 := ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  exact normalized_minimum_upper_bound F htwo n

end Conjecture2899
