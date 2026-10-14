import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

namespace SUnitPrimeBound

def N (m : ℕ) : ℕ := 2 ^ (2 * m)
def primeSet (m : ℕ) : Finset ℕ := Nat.primesLE (2 * N m)
def smallSet (m : ℕ) : Finset ℕ := (primeSet m).filter (fun p => p ≤ 2 ^ m)
def largeSet (m : ℕ) : Finset ℕ := (primeSet m).filter (fun p => 2 ^ m < p)

theorem small_card_bound (m : ℕ) : (smallSet m).card ≤ 2 ^ m + 1 := by
  calc
    (smallSet m).card ≤ (Finset.range (2 ^ m + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      have hle := (Finset.mem_filter.mp hp).2
      exact Finset.mem_range.mpr (by omega)
    _ = 2 ^ m + 1 := Finset.card_range _

theorem partition_card (m : ℕ) :
    (primeSet m).card = (smallSet m).card + (largeSet m).card := by
  have h := Finset.card_filter_add_card_filter_not (s := primeSet m)
    (p := fun p => p ≤ 2 ^ m)
  simpa [smallSet, largeSet, Nat.not_le] using h.symm

theorem large_product_lower (m : ℕ) :
    2 ^ (m * (largeSet m).card) ≤ ∏ p ∈ largeSet m, p := by
  calc
    2 ^ (m * (largeSet m).card) = (2 ^ m) ^ (largeSet m).card := by rw [pow_mul]
    _ = ∏ _p ∈ largeSet m, 2 ^ m := (Finset.prod_const _).symm
    _ ≤ ∏ p ∈ largeSet m, p := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact (Finset.mem_filter.mp hp).2.le

theorem large_product_upper (m : ℕ) :
    (∏ p ∈ largeSet m, p) ≤ 2 ^ (2 * (2 * N m)) := by
  have hsubset : largeSet m ⊆ Nat.primesLE (2 * N m) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  calc
    (∏ p ∈ largeSet m, p) ≤ ∏ p ∈ Nat.primesLE (2 * N m), p := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hsubset
      intro p hp _
      exact (Nat.mem_primesLE.mp hp).2.one_le
    _ = primorial (2 * N m) := (primorial_eq_prod_primesLE _).symm
    _ ≤ 4 ^ (2 * N m) := primorial_le_four_pow _
    _ = 2 ^ (2 * (2 * N m)) := by
      change (2 ^ 2) ^ (2 * N m) = 2 ^ (2 * (2 * N m))
      exact (pow_mul 2 2 (2 * N m)).symm

theorem large_card_bound (m : ℕ) : m * (largeSet m).card ≤ 4 * N m := by
  have h := (large_product_lower m).trans (large_product_upper m)
  have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h
  omega

theorem small_weight_bound (m : ℕ) : m * (smallSet m).card ≤ 2 * N m := by
  have hpow : m ≤ 2 ^ m := m.lt_two_pow_self.le
  have hy : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
  have hn : N m = (2 ^ m) ^ 2 := by
    simp only [N, ← pow_mul]
    congr 1
    omega
  have hle := Nat.mul_le_mul_left m (small_card_bound m)
  rw [hn]
  nlinarith

theorem cardinal_bound (m : ℕ) : m * (primeSet m).card ≤ 6 * N m := by
  rw [partition_card, Nat.mul_add]
  have hlarge := large_card_bound m
  have hsmall := small_weight_bound m
  omega

theorem N_positive (m : ℕ) : 0 < N m := by
  exact pow_pos (by decide) _

end SUnitPrimeBound

#check SUnitPrimeBound.cardinal_bound
#print axioms SUnitPrimeBound.small_card_bound
#print axioms SUnitPrimeBound.partition_card
#print axioms SUnitPrimeBound.large_product_lower
#print axioms SUnitPrimeBound.large_product_upper
#print axioms SUnitPrimeBound.large_card_bound
#print axioms SUnitPrimeBound.small_weight_bound
#print axioms SUnitPrimeBound.cardinal_bound
#print axioms SUnitPrimeBound.N_positive
