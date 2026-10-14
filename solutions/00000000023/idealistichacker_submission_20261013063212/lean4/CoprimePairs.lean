import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

set_option autoImplicit false

/- Standalone square counting only; this is not an S-unit statement bridge. -/
namespace CoprimePairs

def squarePairs (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N).product (Finset.Icc 1 N)

def coprimePairs (N : Nat) : Finset (Nat × Nat) :=
  (squarePairs N).filter (fun p => Nat.Coprime p.1 p.2)

def badPairs (N : Nat) : Finset (Nat × Nat) :=
  (squarePairs N).filter (fun p => ¬ Nat.Coprime p.1 p.2)

def divisorPairs (N d : Nat) : Finset (Nat × Nat) :=
  (squarePairs N).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)

def reciprocalSquareSum (N : Nat) : Rat :=
  (Finset.Icc 2 N).sum (fun d => 1 / (d : Rat) ^ 2)

theorem mem_squarePairs {N a b : Nat} :
    (a, b) ∈ squarePairs N ↔ 1 ≤ a ∧ a ≤ N ∧ 1 ≤ b ∧ b ≤ N := by
  simp only [squarePairs, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem mem_coprimePairs {N a b : Nat} :
    (a, b) ∈ coprimePairs N ↔
      1 ≤ a ∧ a ≤ N ∧ 1 ≤ b ∧ b ≤ N ∧ Nat.Coprime a b := by
  simp only [coprimePairs, Finset.mem_filter, mem_squarePairs]
  tauto

theorem squarePairs_card (N : Nat) : (squarePairs N).card = N ^ 2 := by
  simp [squarePairs, Finset.card_product, Nat.card_Icc, pow_two]

theorem partition_card (N : Nat) :
    (coprimePairs N).card + (badPairs N).card = N ^ 2 := by
  rw [coprimePairs, badPairs, Finset.card_filter_add_card_filter_not, squarePairs_card]

theorem divisorPairs_card (N d : Nat) : (divisorPairs N d).card = (N / d) ^ 2 := by
  have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [divisorPairs, squarePairs, Finset.product_eq_sprod, Finset.filter_product, Finset.card_product,
    hinterval, Nat.Ioc_filter_dvd_card_eq_div]
  ring

theorem badPairs_subset_divisor_union (N : Nat) :
    badPairs N ⊆ (Finset.Icc 2 N).biUnion (divisorPairs N) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp, hbad⟩
  have hbox := mem_squarePairs.mp hp
  have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 (by omega)
  have hgnot : Nat.gcd p.1 p.2 ≠ 1 := by
    simpa only [Nat.coprime_iff_gcd_eq_one] using hbad
  have hgle : Nat.gcd p.1 p.2 ≤ N :=
    (Nat.gcd_le_left p.2 (by omega)).trans hbox.2.1
  apply Finset.mem_biUnion.mpr
  refine ⟨Nat.gcd p.1 p.2, Finset.mem_Icc.mpr ⟨by omega, hgle⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨hp, Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

theorem badPairs_card_le_sum (N : Nat) :
    (badPairs N).card ≤ (Finset.Icc 2 N).sum (fun d => (N / d) ^ 2) := by
  calc
    (badPairs N).card ≤ ((Finset.Icc 2 N).biUnion (divisorPairs N)).card :=
      Finset.card_le_card (badPairs_subset_divisor_union N)
    _ ≤ (Finset.Icc 2 N).sum (fun d => (divisorPairs N d).card) :=
      Finset.card_biUnion_le
    _ = (Finset.Icc 2 N).sum (fun d => (N / d) ^ 2) := by
      simp only [divisorPairs_card]

theorem reciprocal_square_step {x : Rat} (hx : 1 ≤ x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hxpos : 0 < x := by linarith
  have hx1pos : 0 < x + 1 := by linarith
  field_simp
  nlinarith

theorem reciprocalSquareSum_sharp {N : Nat} (hN : 2 ≤ N) :
    reciprocalSquareSum N ≤ 3 / 4 - 1 / (N : Rat) := by
  -- The d = 2 term is 1/4; the remaining upper bound telescopes from 1/2.
  induction N, hN using Nat.le_induction with
  | base => norm_num [reciprocalSquareSum]
  | succ n hn ih =>
    have hnq : (1 : Rat) ≤ (n : Rat) := by exact_mod_cast (show 1 ≤ n by omega)
    have hs := reciprocal_square_step hnq
    rw [reciprocalSquareSum, Finset.sum_Icc_succ_top (by omega)]
    change reciprocalSquareSum n + 1 / ((n + 1 : Nat) : Rat) ^ 2 ≤ _
    push_cast
    linarith

theorem reciprocalSquareSum_le (N : Nat) : reciprocalSquareSum N ≤ 3 / 4 := by
  by_cases hN : 2 ≤ N
  · have h := reciprocalSquareSum_sharp hN
    have hnonneg : (0 : Rat) ≤ 1 / (N : Rat) := by positivity
    linarith
  · interval_cases N <;> norm_num [reciprocalSquareSum]

theorem division_square_le (N d : Nat) :
    ((N / d : Nat) : Rat) ^ 2 ≤ (N : Rat) ^ 2 / (d : Rat) ^ 2 := by
  have hdiv : ((N / d : Nat) : Rat) ≤ (N : Rat) / (d : Rat) := Nat.cast_div_le
  have hnonneg : (0 : Rat) ≤ ((N / d : Nat) : Rat) := by positivity
  have hsq := pow_le_pow_left₀ hnonneg hdiv 2
  simpa only [div_pow] using hsq

theorem badPairs_card_rat_le (N : Nat) :
    ((badPairs N).card : Rat) ≤ (3 / 4) * (N : Rat) ^ 2 := by
  have hcount : ((badPairs N).card : Rat) ≤
      (Finset.Icc 2 N).sum (fun d => ((N / d : Nat) : Rat) ^ 2) := by
    exact_mod_cast badPairs_card_le_sum N
  calc
    ((badPairs N).card : Rat)
        ≤ (Finset.Icc 2 N).sum (fun d => ((N / d : Nat) : Rat) ^ 2) := hcount
    _ ≤ (Finset.Icc 2 N).sum (fun d => (N : Rat) ^ 2 / (d : Rat) ^ 2) :=
      Finset.sum_le_sum (fun d _ => division_square_le N d)
    _ = (N : Rat) ^ 2 * reciprocalSquareSum N := by
      simp only [reciprocalSquareSum, Finset.mul_sum, mul_one_div]
    _ ≤ (N : Rat) ^ 2 * (3 / 4) :=
      mul_le_mul_of_nonneg_left (reciprocalSquareSum_le N) (by positivity)
    _ = (3 / 4) * (N : Rat) ^ 2 := by ring

theorem coprimePairs_card_lower_bound (N : Nat) :
    N ^ 2 ≤ 4 * (coprimePairs N).card := by
  have hpartition : ((coprimePairs N).card : Rat) + ((badPairs N).card : Rat) =
      (N : Rat) ^ 2 := by exact_mod_cast partition_card N
  have hbad := badPairs_card_rat_le N
  have hresult : (N : Rat) ^ 2 ≤ 4 * ((coprimePairs N).card : Rat) := by linarith
  exact_mod_cast hresult

theorem all_positive_square_coprime_pairs :
    ∀ N : Nat, 0 < N →
      N ^ 2 ≤ 4 * (((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card := by
  intro N _
  exact coprimePairs_card_lower_bound N

#check squarePairs
#check coprimePairs
#check badPairs
#check divisorPairs
#check reciprocalSquareSum
#check mem_squarePairs
#check mem_coprimePairs
#check squarePairs_card
#check partition_card
#check divisorPairs_card
#check badPairs_subset_divisor_union
#check badPairs_card_le_sum
#check reciprocal_square_step
#check reciprocalSquareSum_sharp
#check reciprocalSquareSum_le
#check division_square_le
#check badPairs_card_rat_le
#check coprimePairs_card_lower_bound
#check all_positive_square_coprime_pairs

#print axioms squarePairs
#print axioms coprimePairs
#print axioms badPairs
#print axioms divisorPairs
#print axioms reciprocalSquareSum
#print axioms mem_squarePairs
#print axioms mem_coprimePairs
#print axioms squarePairs_card
#print axioms partition_card
#print axioms divisorPairs_card
#print axioms badPairs_subset_divisor_union
#print axioms badPairs_card_le_sum
#print axioms reciprocal_square_step
#print axioms reciprocalSquareSum_sharp
#print axioms reciprocalSquareSum_le
#print axioms division_square_le
#print axioms badPairs_card_rat_le
#print axioms coprimePairs_card_lower_bound
#print axioms all_positive_square_coprime_pairs

end CoprimePairs
