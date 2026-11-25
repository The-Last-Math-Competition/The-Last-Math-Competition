/-
  Conjecture 00000004763 — Low-Order Symbolic Identities, Nonlinearity,
  First Nontrivial Conversion Coefficients, and Crossing-Graph Counterexamples.

  Proves:
  1. Universal symbolic conversion formulas for orders `n = 1, 2, 3, 4, 5`
     across ALL sequences `c, κ : Nat → Int` (`κ_1=c_1`, `κ_2=c_2`, `κ_3=c_3`,
     `κ_4 = c_4 + c_2^2`, `κ_5 = c_5 + 5 c_3 c_2`, `c_4 = κ_4 - κ_2^2`,
     `c_5 = κ_5 - 5 κ_3 κ_2`), plus centered order-6 (`κ_6`, `c_6`).
  2. Strict nonlinearity of both conversion directions (already at `n = 4`).
  3. Refutation of Subclaim 3: the first two nontrivial conversion coefficients
     are `(1, 5)` in `c ↦ κ` and `(-1, -5)` in `κ ↦ c` (or `(-1, -9, 5)` on
     centered symmetric sequences), never `(1, -1)` in either single direction.
  4. Refutation of Subclaim 2: explicit set partitions of `{1..8}` of identical
     block-size signature `[2, 2, 2, 2]` and identical crossing-pair counts
     (`cr = 3` and `cr = 4`) have different crossing-graph connectivity and
     different Tutte activities `T_G(1, 0)`, proving that no function of block
     sizes and crossing-pair count alone can determine the conversion weights.
-/

import Conjecture00000004763.Basic

namespace Conjecture00000004763

/-!
## 1. Fast Step-by-Step Moment & Cumulant Expansions (`1 ≤ n ≤ 5` and Centered `n = 6`)
-/

theorem clMoment_one (c : Nat → Int) : clMoment c 1 = c 1 := by
  rw [clMoment_succ]
  simp [sumRange, binom, clMoment_zero]

theorem clMoment_two (c : Nat → Int) :
    clMoment c 2 = c 2 + c 1 * c 1 := by
  rw [clMoment_succ]
  change 0 + 1 * c 1 * clMoment c 1 + 1 * c 2 * clMoment c 0 = c 2 + c 1 * c 1
  rw [clMoment_zero, clMoment_one]
  simp only [Int.one_mul, Int.mul_one, Int.zero_add]
  omega

theorem clMoment_three (c : Nat → Int) :
    clMoment c 3 = c 3 + (c 2 * c 1 + c 2 * c 1 + c 2 * c 1) + c 1 * (c 1 * c 1) := by
  rw [clMoment_succ]
  change 0 + 1 * c 1 * clMoment c 2 + (1 + 1) * c 2 * clMoment c 1 + 1 * c 3 * clMoment c 0 =
    c 3 + (c 2 * c 1 + c 2 * c 1 + c 2 * c 1) + c 1 * (c 1 * c 1)
  rw [clMoment_zero, clMoment_one, clMoment_two]
  simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_add, Int.add_zero,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem clMoment_four (c : Nat → Int) :
    clMoment c 4 =
      c 4 + 4 * (c 3 * c 1) + 3 * (c 2 * c 2) +
        6 * (c 2 * (c 1 * c 1)) + c 1 * (c 1 * (c 1 * c 1)) := by
  have h4 : (4 : Int) * (c 3 * c 1) = c 3 * c 1 + c 3 * c 1 + c 3 * c 1 + c 3 * c 1 := by omega
  have h3 : (3 : Int) * (c 2 * c 2) = c 2 * c 2 + c 2 * c 2 + c 2 * c 2 := by omega
  have h6 : (6 : Int) * (c 2 * (c 1 * c 1)) =
      c 2 * (c 1 * c 1) + c 2 * (c 1 * c 1) + c 2 * (c 1 * c 1) +
      c 2 * (c 1 * c 1) + c 2 * (c 1 * c 1) + c 2 * (c 1 * c 1) := by omega
  rw [h4, h3, h6, clMoment_succ]
  change 0 + 1 * c 1 * clMoment c 3 + (1 + (1 + 1)) * c 2 * clMoment c 2 +
      ((1 + 1) + 1) * c 3 * clMoment c 1 + 1 * c 4 * clMoment c 0 = _
  rw [clMoment_zero, clMoment_one, clMoment_two, clMoment_three]
  simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_add, Int.add_zero,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem clMoment_five (c : Nat → Int) :
    clMoment c 5 =
      c 5 + 5 * (c 4 * c 1) + 10 * (c 3 * c 2) + 10 * (c 3 * (c 1 * c 1)) +
        15 * (c 2 * (c 2 * c 1)) + 10 * (c 2 * (c 1 * (c 1 * c 1))) +
        c 1 * (c 1 * (c 1 * (c 1 * c 1))) := by
  rw [clMoment_succ]
  change 0 + binom 4 0 * c 1 * clMoment c 4 + binom 4 1 * c 2 * clMoment c 3 +
      binom 4 2 * c 3 * clMoment c 2 + binom 4 3 * c 4 * clMoment c 1 +
      binom 4 4 * c 5 * clMoment c 0 = _
  rw [clMoment_zero, clMoment_one, clMoment_two, clMoment_three, clMoment_four]
  have expand2 : ∀ x : Int, (2 : Int) * x = x + x := fun _ => by omega
  have expand3 : ∀ x : Int, (3 : Int) * x = x + x + x := fun _ => by omega
  have expand4 : ∀ x : Int, (4 : Int) * x = x + x + x + x := fun _ => by omega
  have expand5 : ∀ x : Int, (5 : Int) * x = x + x + x + x + x := fun _ => by omega
  have expand6 : ∀ x : Int, (6 : Int) * x = x + x + x + x + x + x := fun _ => by omega
  have expand10 : ∀ x : Int, (10 : Int) * x = (5 : Int) * x + (5 : Int) * x := fun _ => by omega
  have expand15 : ∀ x : Int, (15 : Int) * x = (5 : Int) * x + (5 : Int) * x + (5 : Int) * x := fun _ => by omega
  simp only [binom, expand15, expand10, expand6, expand5, expand4, expand3, expand2,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
    Int.zero_add, Int.add_zero, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

/-- Universal low-order forward identities (`1 ≤ n ≤ 5`). -/
theorem classicalToFree_one (c : Nat → Int) :
    classicalToFree c 1 = c 1 := by
  unfold classicalToFree
  rw [frCumulant_succ, clMoment_one]
  simp [sumRange]

theorem classicalToFree_two (c : Nat → Int) :
    classicalToFree c 2 = c 2 := by
  unfold classicalToFree
  rw [frCumulant_succ]
  simp only [sumRange, Int.zero_add]
  change clMoment c 2 - classicalToFree c 1 * momentConv (clMoment c) 1 1 = c 2
  rw [classicalToFree_one, clMoment_two]
  simp only [momentConv, sumRange, clMoment_zero, clMoment_one,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
    Int.add_zero, Int.zero_add]
  omega

theorem classicalToFree_three (c : Nat → Int) :
    classicalToFree c 3 = c 3 := by
  unfold classicalToFree
  rw [frCumulant_succ]
  simp only [sumRange, Int.zero_add]
  change clMoment c 3 -
    (classicalToFree c 1 * momentConv (clMoment c) 1 2 +
     classicalToFree c 2 * momentConv (clMoment c) 2 1) = c 3
  rw [classicalToFree_one, classicalToFree_two]
  simp only [momentConv, sumRange, clMoment_zero, clMoment_one, clMoment_two, clMoment_three,
    Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul, Int.mul_neg,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
    Int.add_zero, Int.zero_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem classicalToFree_four (c : Nat → Int) :
    classicalToFree c 4 = c 4 + c 2 * c 2 := by
  unfold classicalToFree
  rw [frCumulant_succ]
  simp only [sumRange, Int.zero_add]
  change clMoment c 4 -
    (classicalToFree c 1 * momentConv (clMoment c) 1 3 +
     classicalToFree c 2 * momentConv (clMoment c) 2 2 +
     classicalToFree c 3 * momentConv (clMoment c) 3 1) = c 4 + c 2 * c 2
  rw [classicalToFree_one, classicalToFree_two, classicalToFree_three]
  have expand3 : ∀ x : Int, (3 : Int) * x = x + x + x := fun _ => by omega
  have expand4 : ∀ x : Int, (4 : Int) * x = x + x + x + x := fun _ => by omega
  have expand6 : ∀ x : Int, (6 : Int) * x = x + x + x + x + x + x := fun _ => by omega
  simp only [momentConv, sumRange, clMoment_zero, clMoment_one, clMoment_two, clMoment_three, clMoment_four,
    expand6, expand4, expand3,
    Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul, Int.mul_neg,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
    Int.add_zero, Int.zero_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem classicalToFree_five (c : Nat → Int) :
    classicalToFree c 5 = c 5 + 5 * (c 3 * c 2) := by
  unfold classicalToFree
  rw [frCumulant_succ]
  simp only [sumRange, Int.zero_add]
  change clMoment c 5 -
    (classicalToFree c 1 * momentConv (clMoment c) 1 4 +
     classicalToFree c 2 * momentConv (clMoment c) 2 3 +
     classicalToFree c 3 * momentConv (clMoment c) 3 2 +
     classicalToFree c 4 * momentConv (clMoment c) 4 1) = c 5 + 5 * (c 3 * c 2)
  rw [classicalToFree_one, classicalToFree_two, classicalToFree_three, classicalToFree_four]
  have expand3 : ∀ x : Int, (3 : Int) * x = x + x + x := fun _ => by omega
  have expand4 : ∀ x : Int, (4 : Int) * x = x + x + x + x := fun _ => by omega
  have expand5 : ∀ x : Int, (5 : Int) * x = x + x + x + x + x := fun _ => by omega
  have expand6 : ∀ x : Int, (6 : Int) * x = x + x + x + x + x + x := fun _ => by omega
  have expand10 : ∀ x : Int, (10 : Int) * x = (5 : Int) * x + (5 : Int) * x := fun _ => by omega
  have expand15 : ∀ x : Int, (15 : Int) * x = (5 : Int) * x + (5 : Int) * x + (5 : Int) * x := fun _ => by omega
  simp only [momentConv, sumRange, clMoment_zero, clMoment_one, clMoment_two, clMoment_three,
    clMoment_four, clMoment_five,
    expand15, expand10, expand6, expand5, expand4, expand3,
    Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul, Int.mul_neg,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
    Int.add_zero, Int.zero_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

/-- Universal low-order inverse identities (`1 ≤ n ≤ 5`) deduced in 2 lines each from
    `freeToClassical_classicalToFree` / `classicalToFree_freeToClassical`!! -/
theorem freeToClassical_one (κ : Nat → Int) :
    freeToClassical κ 1 = κ 1 := by
  have h := classicalToFree_one (freeToClassical κ)
  rw [classicalToFree_freeToClassical κ 1 (by omega)] at h
  exact h.symm

theorem freeToClassical_two (κ : Nat → Int) :
    freeToClassical κ 2 = κ 2 := by
  have h := classicalToFree_two (freeToClassical κ)
  rw [classicalToFree_freeToClassical κ 2 (by omega)] at h
  exact h.symm

theorem freeToClassical_three (κ : Nat → Int) :
    freeToClassical κ 3 = κ 3 := by
  have h := classicalToFree_three (freeToClassical κ)
  rw [classicalToFree_freeToClassical κ 3 (by omega)] at h
  exact h.symm

theorem freeToClassical_four (κ : Nat → Int) :
    freeToClassical κ 4 = κ 4 - κ 2 * κ 2 := by
  have h := classicalToFree_four (freeToClassical κ)
  rw [classicalToFree_freeToClassical κ 4 (by omega), freeToClassical_two] at h
  omega

theorem freeToClassical_five (κ : Nat → Int) :
    freeToClassical κ 5 = κ 5 - 5 * (κ 3 * κ 2) := by
  have h := classicalToFree_five (freeToClassical κ)
  rw [classicalToFree_freeToClassical κ 5 (by omega),
      freeToClassical_three, freeToClassical_two] at h
  omega

/-- Centered order-6 forward identity: `κ_6 = c_6 + 9 c_4 c_2 + 7 c_3^2 + 4 c_2^3`. -/
theorem classicalToFree_six_centered (c : Nat → Int) (hc1 : c 1 = 0) :
    classicalToFree c 6 =
      c 6 + 9 * (c 4 * c 2) + 7 * (c 3 * c 3) + 4 * (c 2 * (c 2 * c 2)) := by
  have hm1 : clMoment c 1 = 0 := by rw [clMoment_one, hc1]
  have hm2 : clMoment c 2 = c 2 := by rw [clMoment_two, hc1]; simp
  have hm3 : clMoment c 3 = c 3 := by rw [clMoment_three, hc1]; simp
  have hm4 : clMoment c 4 = c 4 + 3 * (c 2 * c 2) := by rw [clMoment_four, hc1]; simp
  have hm5 : clMoment c 5 = c 5 + 10 * (c 3 * c 2) := by rw [clMoment_five, hc1]; simp
  have hm6 : clMoment c 6 =
      c 6 + 15 * (c 4 * c 2) + 10 * (c 3 * c 3) + 15 * (c 2 * (c 2 * c 2)) := by
    rw [clMoment_succ]
    change 0 + binom 5 0 * c 1 * clMoment c 5 + binom 5 1 * c 2 * clMoment c 4 +
        binom 5 2 * c 3 * clMoment c 3 + binom 5 3 * c 4 * clMoment c 2 +
        binom 5 4 * c 5 * clMoment c 1 + binom 5 5 * c 6 * clMoment c 0 = _
    rw [clMoment_zero, hm1, hm2, hm3, hm4, hm5, hc1]
    have expand3 : ∀ x : Int, (3 : Int) * x = x + x + x := fun _ => by omega
    have expand5 : ∀ x : Int, (5 : Int) * x = x + x + x + x + x := fun _ => by omega
    have expand10 : ∀ x : Int, (10 : Int) * x = (5 : Int) * x + (5 : Int) * x := fun _ => by omega
    have expand15 : ∀ x : Int, (15 : Int) * x = (5 : Int) * x + (5 : Int) * x + (5 : Int) * x := fun _ => by omega
    simp only [binom, expand15, expand10, expand5, expand3,
      Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
      Int.zero_add, Int.add_zero, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  unfold classicalToFree
  rw [frCumulant_succ]
  simp only [sumRange, Int.zero_add]
  change clMoment c 6 -
    (classicalToFree c 1 * momentConv (clMoment c) 1 5 +
     classicalToFree c 2 * momentConv (clMoment c) 2 4 +
     classicalToFree c 3 * momentConv (clMoment c) 3 3 +
     classicalToFree c 4 * momentConv (clMoment c) 4 2 +
     classicalToFree c 5 * momentConv (clMoment c) 5 1) =
    c 6 + 9 * (c 4 * c 2) + 7 * (c 3 * c 3) + 4 * (c 2 * (c 2 * c 2))
  rw [classicalToFree_one, classicalToFree_two, classicalToFree_three,
      classicalToFree_four, classicalToFree_five]
  have expand3 : ∀ x : Int, (3 : Int) * x = x + x + x := fun _ => by omega
  have expand4 : ∀ x : Int, (4 : Int) * x = x + x + x + x := fun _ => by omega
  have expand5 : ∀ x : Int, (5 : Int) * x = x + x + x + x + x := fun _ => by omega
  have expand7 : ∀ x : Int, (7 : Int) * x = (4 : Int) * x + (3 : Int) * x := fun _ => by omega
  have expand9 : ∀ x : Int, (9 : Int) * x = (5 : Int) * x + (4 : Int) * x := fun _ => by omega
  have expand10 : ∀ x : Int, (10 : Int) * x = (5 : Int) * x + (5 : Int) * x := fun _ => by omega
  have expand15 : ∀ x : Int, (15 : Int) * x = (5 : Int) * x + (5 : Int) * x + (5 : Int) * x := fun _ => by omega
  simp only [momentConv, sumRange, clMoment_zero, hm1, hm2, hm3, hm4, hm5, hm6, hc1,
    expand15, expand10, expand9, expand7, expand5, expand4, expand3,
    Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul, Int.mul_neg,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
    Int.add_zero, Int.zero_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

/-- Centered order-6 inverse identity: `c_6 = κ_6 - 9 κ_4 κ_2 - 7 κ_3^2 + 5 κ_2^3`. -/
theorem freeToClassical_six_centered (κ : Nat → Int) (hκ1 : κ 1 = 0) :
    freeToClassical κ 6 =
      κ 6 - 9 * (κ 4 * κ 2) - 7 * (κ 3 * κ 3) + 5 * (κ 2 * (κ 2 * κ 2)) := by
  have hc1 : freeToClassical κ 1 = 0 := by rw [freeToClassical_one, hκ1]
  have h := classicalToFree_six_centered (freeToClassical κ) hc1
  rw [classicalToFree_freeToClassical κ 6 (by omega),
      freeToClassical_four, freeToClassical_three, freeToClassical_two] at h
  -- Substitute `freeToClassical κ 4 = κ 4 - κ 2 * κ 2`:
  -- `9 * ((κ 4 - κ 2 * κ 2) * κ 2) + 4 * (κ 2 * (κ 2 * κ 2)) = 9 * (κ 4 * κ 2) - 5 * (κ 2 * (κ 2 * κ 2))`!
  have hdist : 9 * ((κ 4 - κ 2 * κ 2) * κ 2) + 4 * (κ 2 * (κ 2 * κ 2)) =
      9 * (κ 4 * κ 2) - 5 * (κ 2 * (κ 2 * κ 2)) := by
    rw [Int.sub_mul, Int.mul_sub]
    have hassoc : κ 2 * κ 2 * κ 2 = κ 2 * (κ 2 * κ 2) := Int.mul_assoc _ _ _
    rw [hassoc]
    omega
  omega

/-!
## 2. Strict Nonlinearity & Refutation of Subclaim 3 (First Two Nontrivial Coefficients)
-/

/-- Neither `classicalToFree` nor `freeToClassical` is an additive (linear) transformation. -/
theorem conversion_strictly_nonlinear :
    (∃ c1 c2 : Nat → Int,
      classicalToFree (fun n => c1 n + c2 n) 4 ≠ classicalToFree c1 4 + classicalToFree c2 4) ∧
    (∃ κ1 κ2 : Nat → Int,
      freeToClassical (fun n => κ1 n + κ2 n) 4 ≠ freeToClassical κ1 4 + freeToClassical κ2 4) := by
  let e2 : Nat → Int := fun n => if n = 2 then 1 else 0
  refine ⟨⟨e2, e2, ?_⟩, ⟨e2, e2, ?_⟩⟩
  · rw [classicalToFree_four, classicalToFree_four]
    simp [e2]
  · rw [freeToClassical_four, freeToClassical_four]
    simp [e2]

/-- Standard cumulant probe `e_2 + e_3` (`x_2 = 1, x_3 = 1`, other `x_j = 0`). -/
def probe23 : Nat → Int := fun n => if n = 2 ∨ n = 3 then 1 else 0

/-- Refutation of Subclaim 3:
    - For `classicalToFree`, orders `1, 2, 3` are trivial (`κ_n = c_n`), while the first two
      nontrivial conversion coefficients at `n = 4` and `n = 5` are `(1, 5) ≠ (1, -1)`.
    - For `freeToClassical`, orders `1, 2, 3` are trivial (`c_n = κ_n`), while the first two
      nontrivial conversion coefficients at `n = 4` and `n = 5` are `(-1, -5) ≠ (1, -1)`. -/
theorem first_two_nontrivial_coeffs_not_one_and_neg_one :
    (classicalToFree probe23 4 - probe23 4, classicalToFree probe23 5 - probe23 5) = (1, 5) ∧
    (1, (5 : Int)) ≠ (1, -1) ∧
    (freeToClassical probe23 4 - probe23 4, freeToClassical probe23 5 - probe23 5) = (-1, -5) ∧
    ((-1 : Int), (-5 : Int)) ≠ (1, -1) := by
  rw [classicalToFree_four, classicalToFree_five, freeToClassical_four, freeToClassical_five]
  refine ⟨?_, by decide, ?_, by decide⟩
  · simp [probe23]
  · simp [probe23]

/-!
## 3. Set Partitions, Crossing Pair Counts, Crossing Graphs, and Tutte Activity `T_G(1, 0)`
-/

/-- Decidable check that `p` is a valid set partition of `{1, ..., n}`:
    every block is nonempty, and each `x ∈ {1, ..., n}` appears once across `p.flatten`
    with no elements outside `{1, ..., n}`. -/
def isSetPartitionBool (n : Nat) (p : List (List Nat)) : Bool :=
  let flat := p.flatten
  p.all (fun b => !b.isEmpty) &&
  flat.length == n &&
  (List.range n).all (fun i => flat.count (i + 1) == 1)

/-- Check whether there exist `a < b < c < d` with `a, c ∈ X` and `b, d ∈ Y`. -/
def alternatingQuad (X Y : List Nat) : Bool :=
  X.any (fun a =>
    Y.any (fun b =>
      a < b && X.any (fun c =>
        b < c && Y.any (fun d => c < d))))

/-- Two blocks `A` and `B` cross iff they form an alternating quadruple in either order. -/
def blocksCrossBool (A B : List Nat) : Bool :=
  alternatingQuad A B || alternatingQuad B A

/-- Exact list of unordered crossing block-index pairs `(i, j)` with `i < j`. -/
def crossingEdges (p : List (List Nat)) : List (Nat × Nat) :=
  let k := p.length
  ((List.range k).map (fun i =>
    ((List.range k).filter (fun j =>
      i < j && blocksCrossBool (p.getD i []) (p.getD j []))).map (fun j => (i, j)))).flatten

/-- Number of unordered crossing pairs of blocks `cr(π)`. -/
def crossingPairCount (p : List (List Nat)) : Nat :=
  (crossingEdges p).length

/-- Check connectivity of the crossing graph of `p` by iterative neighbor expansion from `{0}`. -/
def expandReach (k : Nat) (edges : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, reached => reached
  | fuel + 1, reached =>
      let next := (List.range k).filter (fun v =>
        reached.contains v ||
        edges.any (fun e =>
          (e.1 == v && reached.contains e.2) || (e.2 == v && reached.contains e.1)))
      expandReach k edges fuel next

def isCrossingConnected (p : List (List Nat)) : Bool :=
  let k := p.length
  if k == 0 then true
  else
    let reached := expandReach k (crossingEdges p) k [0]
    (List.range k).all (fun v => reached.contains v)

/-- Check whether a directed edge list `dirEdges` on `k` vertices is a DAG with `0` as unique source. -/
def isUniqueSourceZeroDAG (k : Nat) (dirEdges : List (Nat × Nat)) : Bool :=
  let sources := (List.range k).filter (fun v => !(dirEdges.any (fun e => e.2 == v)))
  if sources != [0] then false
  else
    let rec peel : Nat → List Nat → Bool
      | 0, visited => (List.range k).all (fun v => visited.contains v)
      | step + 1, visited =>
          let ready := (List.range k).filter (fun v =>
            visited.contains v ||
            dirEdges.all (fun e => if e.2 == v then visited.contains e.1 else true))
          peel step ready
    peel k [0]

/-- Orient `edges` according to bitmask `mask`. -/
def orientByMask : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (u, v) :: rest, mask =>
      let dir := if mask % 2 == 1 then (u, v) else (v, u)
      dir :: orientByMask rest (mask / 2)

/-- Exact Tutte activity `T_{G(p)}(1, 0)` = number of acyclic orientations of the crossing graph
    with block `0` as unique source (Greene-Zaslavsky theorem). -/
def tutteActivityT10 (p : List (List Nat)) : Nat :=
  let k := p.length
  if k <= 1 then 1
  else
    let edges := crossingEdges p
    let numMasks := 2 ^ edges.length
    ((List.range numMasks).filter (fun mask =>
      isUniqueSourceZeroDAG k (orientByMask edges mask))).length

/-- Forward conversion weight of a partition `p` in `κ_n(c)` (`1` if connected, `0` otherwise). -/
def forwardPartitionWeight (p : List (List Nat)) : Int :=
  if isCrossingConnected p then 1 else 0

/-- Inverse conversion weight of a partition `p` in `c_n(κ)`
    (`(-1)^(|p| - 1) * T_{G(p)}(1, 0)` if connected, `0` otherwise). -/
def inversePartitionWeight (p : List (List Nat)) : Int :=
  if isCrossingConnected p then
    powZ (-1) (p.length - 1) * (tutteActivityT10 p : Int)
  else 0

/-- Block-size list `[|B_1|, ..., |B_k|]` of a partition. -/
def blockLengths (p : List (List Nat)) : List Nat :=
  p.map List.length

def pi4_cross : List (List Nat) := [[1, 3], [2, 4]]

/-- Non-vacuity check on `{1, 2, 3, 4}`: the unique crossing pairing `{{1,3},{2,4}}` has
    crossing count `1`, forward weight `+1` (`κ_4 = c_4 + c_2^2`), and inverse weight `-1`
    (`c_4 = κ_4 - κ_2^2`). -/
theorem pi4_cross_weights :
    isSetPartitionBool 4 pi4_cross = true ∧
    crossingPairCount pi4_cross = 1 ∧
    forwardPartitionWeight pi4_cross = 1 ∧
    inversePartitionWeight pi4_cross = -1 := by
  decide

def pi8_disc : List (List Nat) := [[1, 8], [2, 5], [3, 6], [4, 7]]
def pi8_tree : List (List Nat) := [[1, 7], [2, 6], [3, 5], [4, 8]]
def pi8_paw  : List (List Nat) := [[1, 7], [2, 5], [3, 6], [4, 8]]
def pi8_c4   : List (List Nat) := [[1, 6], [2, 5], [3, 8], [4, 7]]

/-- Refutation of Subclaim 2 (Part A — Disconnected vs. Connected at `cr = 3`). -/
theorem crossing_count_three_counterexample :
    isSetPartitionBool 8 pi8_disc = true ∧
    isSetPartitionBool 8 pi8_tree = true ∧
    blockLengths pi8_disc = [2, 2, 2, 2] ∧
    blockLengths pi8_tree = [2, 2, 2, 2] ∧
    crossingPairCount pi8_disc = 3 ∧
    crossingPairCount pi8_tree = 3 ∧
    forwardPartitionWeight pi8_disc = 0 ∧
    forwardPartitionWeight pi8_tree = 1 ∧
    inversePartitionWeight pi8_disc = 0 ∧
    inversePartitionWeight pi8_tree = -1 := by
  decide

/-- Refutation of Subclaim 2 (Part B — Connected Paw vs. `C_4` at `cr = 4`). -/
theorem crossing_count_four_connected_tutte_counterexample :
    isSetPartitionBool 8 pi8_paw = true ∧
    isSetPartitionBool 8 pi8_c4 = true ∧
    isCrossingConnected pi8_paw = true ∧
    isCrossingConnected pi8_c4 = true ∧
    blockLengths pi8_paw = [2, 2, 2, 2] ∧
    blockLengths pi8_c4 = [2, 2, 2, 2] ∧
    crossingPairCount pi8_paw = 4 ∧
    crossingPairCount pi8_c4 = 4 ∧
    inversePartitionWeight pi8_paw = -2 ∧
    inversePartitionWeight pi8_c4 = -3 := by
  decide

/-- Universal impossibility corollary for Subclaim 2:
    No function `W(blockLengths, crossingPairCount)` can reproduce either `forwardPartitionWeight`
    or `inversePartitionWeight` on set partitions of `{1..8}` — not even when restricted to
    connected crossing partitions in the inverse direction. -/
theorem no_weight_function_of_crossing_pair_count :
    (¬ ∃ W : List Nat → Nat → Int,
        ∀ p, isSetPartitionBool 8 p = true →
          forwardPartitionWeight p = W (blockLengths p) (crossingPairCount p)) ∧
    (¬ ∃ W : List Nat → Nat → Int,
        ∀ p, isSetPartitionBool 8 p = true → isCrossingConnected p = true →
          inversePartitionWeight p = W (blockLengths p) (crossingPairCount p)) := by
  have h3 := crossing_count_three_counterexample
  have h4 := crossing_count_four_connected_tutte_counterexample
  refine ⟨?_, ?_⟩
  · intro ⟨W, hW⟩
    have e1 := hW pi8_disc h3.1
    have e2 := hW pi8_tree h3.2.1
    rw [h3.2.2.1, h3.2.2.2.2.1, h3.2.2.2.2.2.2.1] at e1
    rw [h3.2.2.2.1, h3.2.2.2.2.2.1, h3.2.2.2.2.2.2.2.1] at e2
    omega
  · intro ⟨W, hW⟩
    have e1 := hW pi8_paw h4.1 h4.2.2.1
    have e2 := hW pi8_c4 h4.2.1 h4.2.2.2.1
    rw [h4.2.2.2.2.1, h4.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.1] at e1
    rw [h4.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.2] at e2
    omega

end Conjecture00000004763
