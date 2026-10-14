import Conjecture2899.Bounds
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.ZMod.Basic

namespace Conjecture2899

theorem prime_field_counterexamples (n : ℕ) (c : ℝ) (Q : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      2 < p ∧ Q ≤ p ∧
        ∃ K : Finset (Fin (n + 2) → ZMod p),
          IsKakeya K ∧
          (minimumKakeyaSize (ZMod p) (n + 2) : ℝ) ≤ (K.card : ℝ) ∧
          (K.card : ℝ) < (p : ℝ)^(n + 2) * (1 - c / (p : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (c + 1))
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (max N (max Q 3))
  have hNp : N ≤ p := le_trans (le_max_left _ _) hlarge
  have hQp : Q ≤ p := le_trans (le_trans (le_max_left Q 3) (le_max_right N _)) hlarge
  have h3p : 3 ≤ p := le_trans (le_trans (le_max_right Q 3) (le_max_right N _)) hlarge
  have h2p : 2 < p := lt_of_lt_of_le (by decide) h3p
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h)
    exact (not_le_of_gt h2p) (Nat.le_of_dvd (by decide) hdvd)
  have hcard : 2 * (c + 1) < (Fintype.card (ZMod p) : ℝ) := by
    rw [ZMod.card]
    exact lt_of_lt_of_le hN (by exact_mod_cast hNp)
  refine ⟨p, hp, h2p, hQp, family (ZMod p) n, family_isKakeya (ZMod p) htwo n, ?_, ?_⟩
  · exact_mod_cast minimum_le_card (family (ZMod p) n) (family_isKakeya (ZMod p) htwo n)
  · simpa only [ZMod.card] using family_lt_proposed_bound (ZMod p) htwo n c hcard

theorem counterexamples_in_each_dimension (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (Q : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      2 < p ∧ Q ≤ p ∧
        ∃ K : Finset (Fin d → ZMod p),
          IsKakeya K ∧
          (minimumKakeyaSize (ZMod p) d : ℝ) ≤ (K.card : ℝ) ∧
          (K.card : ℝ) < (p : ℝ)^d * (1 - c / (p : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 2 := ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  exact prime_field_counterexamples n c Q

theorem not_proposedEventualLowerBound (d : ℕ) (hd : 2 ≤ d) :
    ¬ ProposedEventualLowerBound d := by
  rintro ⟨c, Q, hbound⟩
  obtain ⟨p, hp, hcounter⟩ := counterexamples_in_each_dimension d hd c Q
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_hp2, hQp, K, _hK, hmin, hlt⟩ := hcounter
  have hQcard : Q ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using hQp
  have hlower := hbound (ZMod p) hQcard
  simp only [ZMod.card] at hlower
  exact (not_lt_of_ge hlower) (lt_of_le_of_lt hmin hlt)

end Conjecture2899

