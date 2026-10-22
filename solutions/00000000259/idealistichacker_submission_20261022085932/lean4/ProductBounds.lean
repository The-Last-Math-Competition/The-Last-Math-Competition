import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter

namespace PellConstant259

noncomputable section

def factor (n : Nat) : Real := 1 - (1 / 2 : Real)^(n + 2)

def claimedConstant : Real := 1 - ∏' n : Nat, factor n

theorem factor_bounds (n : Nat) : 0 ≤ factor n ∧ factor n ≤ 1 := by
  have h0 : 0 ≤ (1 / 2 : Real)^(n+2) := by positivity
  have h1 : (1 / 2 : Real)^(n+2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> unfold factor <;> linarith

theorem product_multipliable : Multipliable factor := by
  have hs : Summable (fun n : Nat => (1 / 2 : Real)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have ht : Summable (fun n : Nat => -((1 / 2 : Real)^(n+2))) := by
    simpa only [pow_add] using (hs.mul_right ((1 / 2 : Real)^2)).neg
  change Multipliable (fun n : Nat => 1 - (1 / 2 : Real)^(n+2))
  simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable ht

theorem product_lower_union (f : Nat → Real) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) (n : Nat) :
    1 - ∑ i ∈ Finset.range n, f i ≤ ∏ i ∈ Finset.range n, (1 - f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (∏ i ∈ Finset.range n, (1 - f i)) ≤ 1 :=
      Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hf i).2)
        (fun i _ => by linarith [(hf i).1])
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    nlinarith [(hf n).1, (hf n).2]

theorem tail_sum_le (n : Nat) :
    ∑ i ∈ Finset.range n, (1 / 2 : Real)^(i+3) ≤ 1 / 4 := by
  have hs : Summable (fun n : Nat => (1 / 2 : Real)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := hs.sum_le_tsum (Finset.range n) (fun i _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : Real)) (by norm_num)] at h
  simp_rw [pow_add]
  rw [← Finset.sum_mul]
  norm_num at h ⊢
  linarith

theorem finite_product_bounds (n : Nat) :
    9 / 16 ≤ (∏ i ∈ Finset.range (n+1), factor i) ∧
      (∏ i ∈ Finset.range (n+1), factor i) ≤ (3 / 4 : Real) := by
  let tail : Nat → Real := fun i => (1 / 2 : Real)^(i+3)
  have ht (i : Nat) : 0 ≤ tail i ∧ tail i ≤ 1 := by
    dsimp [tail]
    exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hl := product_lower_union tail ht n
  have hs := tail_sum_le n
  have hu : (∏ i ∈ Finset.range n, (1-tail i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => sub_nonneg.mpr (ht i).2)
      (fun i _ => by linarith [(ht i).1])
  rw [Finset.prod_range_succ']
  have heq : (∏ k ∈ Finset.range n, factor (k+1)) =
      ∏ k ∈ Finset.range n, (1-tail k) := by
    simp [factor, tail, Nat.add_assoc]
  rw [heq]
  norm_num [factor]
  dsimp [tail] at hl hu
  constructor <;> nlinarith

theorem infinite_product_bounds :
    9 / 16 ≤ (∏' n : Nat, factor n) ∧ (∏' n : Nat, factor n) ≤ (3 / 4 : Real) := by
  have h := product_multipliable.tendsto_prod_tprod_nat.comp (tendsto_add_atTop_nat 1)
  constructor
  · exact ge_of_tendsto' h (fun n => (finite_product_bounds n).1)
  · exact le_of_tendsto' h (fun n => (finite_product_bounds n).2)

theorem claimedConstant_bounds : (1 / 4 : Real) ≤ claimedConstant ∧ claimedConstant ≤ 7 / 16 := by
  have h := infinite_product_bounds
  unfold claimedConstant
  constructor <;> linarith

theorem claimedConstant_not_one : claimedConstant ≠ 1 := by
  have h := claimedConstant_bounds
  linarith

end
end PellConstant259
