/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Decisive counterexample families refuting Conjecture 00000007176 across every
standard tensor eigenvalue definition (`H`-, `Z`-, and complex `E`-eigenvalues)
and every standard normalization, together with concrete `Int` and `RatField`
non-vacuity instantiations in Core Lean 4.19.0.
-/
import Conjecture00000007176.PositiveBounds

namespace Conjecture00000007176

/-! ### Arithmetic Power Helpers -/

private theorem nat_le_pow_self : ∀ {n d : Nat}, n ≥ 1 → d ≥ 1 → n ≤ n ^ d
  | _, 0, _, hd => by omega
  | n, 1, _, _ => by simp
  | n, d + 2, hn, _ => by
    have ih := nat_le_pow_self hn (d := d + 1) (by omega)
    rw [Nat.pow_succ]
    have hmul : n ^ (d + 1) * 1 ≤ n ^ (d + 1) * n := Nat.mul_le_mul_left _ hn
    omega

private theorem pow_three_ge_nine : ∀ k : Nat, 9 ≤ 3 ^ (k + 2)
  | 0 => by decide
  | k + 1 => by
    have ih := pow_three_ge_nine k
    rw [Nat.pow_succ]
    omega

private theorem pow_three_ge_27 : ∀ k : Nat, 27 ≤ 3 ^ (k + 3)
  | 0 => by decide
  | k + 1 => by
    have ih := pow_three_ge_27 k
    rw [Nat.pow_succ]
    omega

private theorem pow_two_ge_16 : ∀ k : Nat, 16 ≤ 2 ^ (k + 4)
  | 0 => by decide
  | k + 1 => by
    have ih := pow_two_ge_16 k
    rw [Nat.pow_succ]
    omega

private theorem fin2_zero_ne_one {h0 : 0 < 2} {h1 : 1 < 2} :
    (⟨0, h0⟩ : Fin 2) ≠ ⟨1, h1⟩ :=
  fun heq => nomatch (congrArg Fin.val heq : (0 : Nat) = 1)

/-! ### 1. Unnormalized Symmetric Tensors Are Spectrally Unbounded -/

/-- Without norm or entry normalization, scaling `A ↦ c A` makes both `H`- and `Z`-eigenvalues
    strictly exceed any proposed bound `M` in every dimension `n ≥ 1` and order `m = d + 1 ≥ 2`. -/
theorem refutation_unnormalized_unbounded {R : Type u} [OrderedDomain R]
    {n d : Nat} (hn : n ≥ 1) (hd : d ≥ 1) (M : R) :
    ∃ (A : Idx n (d + 1) → R) (x : Fin n → R) (lam : R),
      IsSymmetric A ∧ IsHEigenpair A x lam ∧ IsZEigenpair A x lam ∧ ltR M lam := by
  let k0 : Fin n := ⟨0, hn⟩
  let c : R := absR M + 1
  let A : Idx n (d + 1) → R := rankOneTensor c (stdBasisVec k0)
  have hlt : ltR M c := by
    have h1 : leR M (absR M) := leR_absR_self M
    have h2 : ltR (absR M) (absR M + 1) := by
      have hp := add_ltR_add_of_ltR_of_leR (zero_ltR_one (R := R)) (leR_refl (absR M))
      rw [zero_add_eq, CommRing.add_comm] at hp
      exact hp
    exact ltR_of_leR_of_ltR h1 h2
  have hzm := monomial_attains_frob_Z_bound (R := R) n d hn
  refine ⟨A, stdBasisVec k0, c, isSymmetric_rankOneTensor c (stdBasisVec k0), ?_, ?_, hlt⟩
  · -- `IsHEigenpair A (stdBasisVec k0) c`
    refine ⟨⟨k0, by unfold stdBasisVec; rw [if_pos rfl]; exact IntegralDomain.zero_ne_one.symm⟩, ?_⟩
    intro i
    dsimp only [A]
    rw [contract_rankOneTensor]
    have hsum : sumFin (fun j => stdBasisVec (S := R) k0 j * stdBasisVec k0 j) = 1 := hzm.2.2.1
    rw [hsum, rpow_one_base, mul_one_eq]
    unfold stdBasisVec
    by_cases hi : i = k0
    · rw [if_pos hi, rpow_one_base]
    · rw [if_neg hi, rpow_zero_base hd]
  · -- `IsZEigenpair A (stdBasisVec k0) c`
    refine ⟨hzm.2.2.1, ?_⟩
    intro i
    dsimp only [A]
    rw [contract_rankOneTensor, hzm.2.2.1, rpow_one_base, mul_one_eq]

/-! ### 2. Entrywise-Bounded (`|a| ≤ 1`) Spectra Exceed Every Function of Degree Alone -/

/-- Universal refutation of any degree-only `H`-eigenvalue bound: for every fixed order
    `m = d + 1 ≥ 2` (`d ≥ 1`) and every function `F : Nat → Nat` of the degree alone
    (including `m^m`, `m^{m-1}`, `(m-1)^m`, or `m^k`), there exists `n ≥ 2` such that the
    `{0, 1}`-valued symmetric tensor `J_{m, n}` satisfies `|a| ≤ 1` and has an `H`-eigenvalue
    `λ_H = n^{m-1} > F(m)`. -/
theorem refutation_entrywise_H_exceeds_any_degree_bound {R : Type u} [OrderedDomain R]
    {d : Nat} (hd : d ≥ 1) (F : Nat → Nat) :
    ∃ (n : Nat) (A : Idx n (d + 1) → R) (x : Fin n → R) (lam : R),
      n ≥ 2 ∧ IsSymmetric A ∧ EntryBoundedAbs A 1 ∧
      IsHEigenpair A x lam ∧ ltR (natCastR (F (d + 1))) (absR lam) := by
  let n := F (d + 1) + 2
  have hn1 : n ≥ 1 := by omega
  have hJ := allOnes_attains_H_bound (R := R) n d hn1
  refine ⟨n, allOnesTensor n (d + 1), fun _ => 1, rpow (natCastR n) d,
          by omega, hJ.1, hJ.2.1, hJ.2.2, ?_⟩
  have hpos : leR (0 : R) (rpow (natCastR n) d) := rpow_nonneg (natCastR_nonneg n) d
  rw [absR_of_nonneg hpos, ← natCastR_pow]
  apply natCastR_ltR_of_lt
  have hle : n ≤ n ^ d := nat_le_pow_self hn1 hd
  omega

/-- Universal refutation of any degree-only `Z`-eigenvalue bound: over `ℚ` (`RatField`), for
    every fixed order `m = d + 1 ≥ 1` and every function `F : Nat → Nat` of the degree alone,
    there exists `n ≥ 4` such that `J_{m, n}` satisfies `|a| ≤ 1` and has a unit-norm
    `Z`-eigenvalue `λ_Z = n^{m/2} > F(m)`. -/
theorem refutation_entrywise_Z_exceeds_any_degree_bound (d : Nat) (F : Nat → Nat) :
    ∃ (n : Nat) (A : Idx n (d + 1) → RatField) (x : Fin n → RatField) (lam : RatField),
      n ≥ 4 ∧ IsSymmetric A ∧ EntryBoundedAbs A 1 ∧
      IsZEigenpair A x lam ∧ ltR (natCastR (F (d + 1))) (absR lam) := by
  let k := F (d + 1) + 2
  let n := k * k
  have hk1 : k ≥ 1 := by omega
  have hn4 : n ≥ 4 := by
    have : 2 * 2 ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hZ := allOnes_attains_Z_bound_rat k d hk1
  have hJ := allOnes_attains_H_bound (R := RatField) n d (by omega)
  refine ⟨n, allOnesTensor n (d + 1), fun _ => RatField.mk 1 (k : Int) (by omega),
          natCastR (k ^ (d + 1)), hn4, hJ.1, hJ.2.1, hZ.1, ?_⟩
  rw [absR_of_nonneg (natCastR_nonneg _)]
  apply natCastR_ltR_of_lt
  have hle : k ≤ k ^ (d + 1) := nat_le_pow_self hk1 (by omega)
  omega

/-- Concrete counterexample `(m = 3, n = 4)`: `J_{3, 4}` over `ℤ` has `|a_{ijk}| ≤ 1` and
    `H`-eigenvalue `λ_H = 16 > 9 = 3^2`. -/
theorem refutation_J34_H_exceeds_deg_sq :
    let A : Idx 4 3 → Int := allOnesTensor 4 3
    IsSymmetric A ∧ EntryBoundedAbs A 1 ∧
    IsHEigenpair A (fun _ => 1) 16 ∧ ltR (natCastR (3 ^ 2) : Int) 16 := by
  dsimp only
  have hJ := allOnes_attains_H_bound (R := Int) 4 2 (by omega)
  have h16 : (rpow (natCastR 4) 2 : Int) = 16 := by
    rw [← natCastR_pow, int_natCastR_eq]
    decide
  rw [h16] at hJ
  refine ⟨hJ.1, hJ.2.1, hJ.2.2, ?_⟩
  rw [int_natCastR_eq, int_ltR_iff]
  decide

/-- Concrete counterexample `(m = 3, n = 6)`: `J_{3, 6}` over `ℤ` has `|a_{ijk}| ≤ 1` and
    `H`-eigenvalue `λ_H = 36 > 27 = 3^3`. -/
theorem refutation_J36_H_exceeds_deg_cube :
    let A : Idx 6 3 → Int := allOnesTensor 6 3
    IsSymmetric A ∧ EntryBoundedAbs A 1 ∧
    IsHEigenpair A (fun _ => 1) 36 ∧ ltR (natCastR (3 ^ 3) : Int) 36 := by
  dsimp only
  have hJ := allOnes_attains_H_bound (R := Int) 6 2 (by omega)
  have h36 : (rpow (natCastR 6) 2 : Int) = 36 := by
    rw [← natCastR_pow, int_natCastR_eq]
    decide
  rw [h36] at hJ
  refine ⟨hJ.1, hJ.2.1, hJ.2.2, ?_⟩
  rw [int_natCastR_eq, int_ltR_iff]
  decide

/-- Concrete binary cubic counterexample `(m = 3, n = 2)`: the sharp entrywise `H`-spectral
    bound over `|a_{ijk}| ≤ 1` is `2^{3-1} = 4`, which equals `3^k` for NO `k ∈ ℕ` and
    also `4 ≠ (3 - 1)^3 = 8`. -/
theorem refutation_J32_H_not_deg_power :
    (IsHEigenpair (allOnesTensor 2 3 : Idx 2 3 → Int) (fun _ => 1) 4) ∧
    (∀ (A : Idx 2 3 → Int) (x : Fin 2 → Int) (lam : Int),
      EntryBoundedAbs A 1 → IsHEigenpair A x lam → leR (absR lam) 4) ∧
    (∀ k : Nat, 4 ≠ 3 ^ k) ∧ (4 ≠ (3 - 1) ^ 3) := by
  have hJ := allOnes_attains_H_bound (R := Int) 2 2 (by omega)
  have h4 : (rpow (natCastR 2) 2 : Int) = 4 := by
    rw [← natCastR_pow, int_natCastR_eq]
    decide
  refine ⟨?_, ?_, ?_, by decide⟩
  · rw [h4] at hJ; exact hJ.2.2
  · intro A x lam hA heig
    have hb := entrywise_H_bound_real (R := Int) (n := 2) (d := 2) (by omega)
      (zero_ltR_one (R := Int)).1 hA heig
    rw [mul_one_eq, h4] at hb
    exact hb
  · intro k
    cases k with
    | zero => decide
    | succ k' =>
      cases k' with
      | zero => decide
      | succ k'' =>
        have h9 := pow_three_ge_nine k''
        omega

/-- Concrete `Z`-eigenvalue counterexample `(m = 3, n = 16)`: over `ℚ`, `J_{3, 16}` has
    `|a_{ijk}| ≤ 1` and exact unit-norm `Z`-eigenvalue `λ_Z = 64 > 27 = 3^3`. -/
theorem refutation_J3_16_Z_exceeds_deg_cube :
    let A : Idx 16 3 → RatField := allOnesTensor 16 3
    let x : Fin 16 → RatField := fun _ => RatField.mk 1 4 (by omega)
    IsSymmetric A ∧ EntryBoundedAbs A 1 ∧
    IsZEigenpair A x (natCastR 64) ∧ ltR (natCastR (3 ^ 3) : RatField) (natCastR 64) := by
  dsimp only
  have hZ := allOnes_attains_Z_bound_rat 4 2 (by omega)
  have hJ := allOnes_attains_H_bound (R := RatField) 16 2 (by omega)
  have h43 : 4 ^ 3 = 64 := by decide
  change IsZEigenpair (allOnesTensor 16 3) _ (natCastR (4 ^ 3)) ∧ _ at hZ
  rw [h43] at hZ
  exact ⟨hJ.1, hJ.2.1, hZ.1, natCastR_ltR_of_lt (by decide)⟩

/-! ### 3. Refutations of the "Binomial Type" Realization Claim -/

/-- Support-`2` binomial vector `(1, 1, 0, ..., 0)` in dimension `n`. -/
def twoOnesVec {S : Type v} [CommRing S] {n : Nat} : Fin n → S :=
  fun j => if j.val < 2 then 1 else 0

/-- `2`-variable binomial symmetric tensor `(x_1 + x_2)^m` embedded in dimension `n`. -/
def twoVarBinomialTensor {S : Type v} [CommRing S] (n m : Nat) : Idx n m → S :=
  rankOneTensor 1 twoOnesVec

private theorem sumFin_twoOnesVec {S : Type v} [CommRing S] {n : Nat} (hn : n ≥ 2) :
    sumFin (twoOnesVec (S := S) (n := n)) = natCastR 2 := by
  -- Decompose `n = 2 + k`, show tail of `finList` past index 1 vanishes
  cases n with
  | zero => omega
  | succ n1 =>
    cases n1 with
    | zero => omega
    | succ k =>
      change twoOnesVec (⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 2)) +
             (twoOnesVec (Fin.succ (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))) +
              sumList (List.map Fin.succ (List.map Fin.succ (finList k))) twoOnesVec) =
             natCastR 2
      rw [sumList_map, sumList_map]
      have h0 : twoOnesVec (S := S) (⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 2)) = 1 := rfl
      have h1 : twoOnesVec (S := S) (Fin.succ (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))) = 1 := rfl
      have htail : sumList (finList k)
          (fun a : Fin k => twoOnesVec (S := S) (Fin.succ (Fin.succ a))) = 0 := by
        calc
          _ = sumList (finList k) (fun _ => (0 : S)) := by
            apply sumList_congr; intro a _
            unfold twoOnesVec
            have hge : ¬ (a.val + 2 < 2) := by omega
            exact if_neg hge
          _ = 0 := sumList_zero _
      rw [h0, h1, htail, add_zero_eq, natCastR_two]

/-- In every dimension `n ≥ 3` and order `m = d + 1 ≥ 2` (`d ≥ 1`), the `2`-variable binomial
    symmetric tensor `(x_1 + x_2)^m` satisfies `|a| ≤ 1` but has all `H`-eigenvalues bounded by
    `2^{m-1} < n^{m-1}`, strictly suboptimal compared to the `n`-variable all-ones tensor `J_{m, n}`. -/
theorem refutation_two_var_binomial_suboptimal {R : Type u} [OrderedDomain R]
    {n d : Nat} (hn : n ≥ 3) (hd : d ≥ 1) :
    let Abin : Idx n (d + 1) → R := twoVarBinomialTensor n (d + 1)
    IsSymmetric Abin ∧ EntryBoundedAbs Abin 1 ∧
    (∀ (x : Fin n → R) (lam : R), IsHEigenpair Abin x lam →
      leR (absR lam) (rpow (natCastR 2) d)) ∧
    ltR (rpow (natCastR 2 : R) d) (rpow (natCastR n) d) := by
  dsimp only
  have hv0 : ∀ j : Fin n, leR (0 : R) (twoOnesVec j) := by
    intro j; unfold twoOnesVec
    by_cases hj : j.val < 2
    · rw [if_pos hj]; exact zero_ltR_one.1
    · rw [if_neg hj]; exact leR_refl 0
  have hv1 : ∀ j : Fin n, leR (twoOnesVec (S := R) j) 1 := by
    intro j; unfold twoOnesVec
    by_cases hj : j.val < 2
    · rw [if_pos hj]; exact leR_refl 1
    · rw [if_neg hj]; exact zero_ltR_one.1
  have hA_nn : ∀ α : Idx n (d + 1), leR (0 : R) (twoVarBinomialTensor n (d + 1) α) := by
    intro α; unfold twoVarBinomialTensor rankOneTensor
    rw [one_mul_eq]
    exact idxProd_nonneg hv0 α
  refine ⟨isSymmetric_rankOneTensor 1 twoOnesVec, ?_, ?_, ?_⟩
  · intro α
    rw [absR_of_nonneg (hA_nn α)]
    unfold twoVarBinomialTensor rankOneTensor
    rw [one_mul_eq, ← rpow_one_base (d + 1)]
    exact idxProd_leR_rpow_of_leR hv0 hv1 α
  · intro x lam heig
    apply gershgorin_nonneg_row_bound_real (by omega) hA_nn ?_ heig
    intro i
    unfold twoVarBinomialTensor
    rw [contract_rankOneTensor, one_mul_eq]
    have hsum : sumFin (fun j : Fin n => twoOnesVec (S := R) j * 1) = natCastR 2 := by
      have hc : (fun j : Fin n => twoOnesVec (S := R) j * (1 : R)) = twoOnesVec := by
        funext j; exact mul_one_eq _
      rw [hc, sumFin_twoOnesVec (by omega)]
    rw [hsum]
    have h1 := mul_leR_mul_of_nonneg_right
      (rpow_nonneg (natCastR_nonneg 2) d) (hv1 i)
    rw [one_mul_eq] at h1
    exact h1
  · exact rpow_ltR_rpow_of_nonneg (natCastR_nonneg 2) (natCastR_ltR_of_lt hn) hd

/-- Unnormalized binomial-entry tensor `B_{3, 2}` (`a_{ijk} = C(3, #2s)`) violates `|a| ≤ 1`
    (`max a = 3 > 1`) and has exact `H`-spectral radius `C(5, 2) = 10`, which is neither a
    power of `3` nor a power of `2`. -/
theorem refutation_binomial_entry_not_deg_power :
    let B3 : Idx 2 3 → Int := binomialEntryTensor 3
    ltR 1 (B3 (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨1, by omega⟩ Idx.nil)))) ∧
    IsHEigenpair B3 (fun _ => 1) 10 ∧
    (∀ (x : Fin 2 → Int) (lam : Int), IsHEigenpair B3 x lam → leR (absR lam) 10) ∧
    (∀ k : Nat, 10 ≠ 3 ^ k) ∧ (∀ k : Nat, 10 ≠ 2 ^ k) := by
  dsimp only
  have hrad := binomialEntry_exact_H_radius (R := Int) 2
  have h10 : (natCastR (binom 5 2) : Int) = 10 := by
    rw [int_natCastR_eq]
    decide
  change IsSymmetric _ ∧ IsHEigenpair _ _ (natCastR (binom 5 2)) ∧ _ at hrad
  rw [h10] at hrad
  refine ⟨?_, hrad.2.1, hrad.2.2, ?_, ?_⟩
  · unfold binomialEntryTensor
    rw [int_natCastR_eq, int_ltR_iff]
    decide
  · intro k
    cases k with
    | zero => decide
    | succ k1 =>
      cases k1 with
      | zero => decide
      | succ k2 =>
        cases k2 with
        | zero => decide
        | succ k3 =>
          have h27 := pow_three_ge_27 k3
          omega
  · intro k
    cases k with
    | zero => decide
    | succ k1 =>
      cases k1 with
      | zero => decide
      | succ k2 =>
        cases k2 with
        | zero => decide
        | succ k3 =>
          cases k3 with
          | zero => decide
          | succ k4 =>
            have h16 := pow_two_ge_16 k4
            omega

/-- Multi-index in `Idx 2 m` containing exactly `k` ones (`k ≤ m`). -/
private def idxWithOnes : (m k : Nat) → k ≤ m → Idx 2 m
  | 0, 0, _ => Idx.nil
  | 0, _ + 1, h => by omega
  | m + 1, 0, _ => Idx.cons ⟨0, by omega⟩ (idxWithOnes m 0 (by omega))
  | m + 1, k + 1, h => Idx.cons ⟨1, by omega⟩ (idxWithOnes m k (by omega))

private theorem countVal_idxWithOnes : ∀ (m k : Nat) (h : k ≤ m),
    countVal ⟨1, by omega⟩ (idxWithOnes m k h) = k
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | m + 1, 0, _ => by
    unfold idxWithOnes
    rw [countVal_cons]
    have hne : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := fin2_zero_ne_one
    rw [if_neg hne, Nat.zero_add, countVal_idxWithOnes m 0]
  | m + 1, k + 1, h => by
    unfold idxWithOnes
    rw [countVal_cons, if_pos rfl, countVal_idxWithOnes m k (by omega), Nat.add_comm]

private theorem scaled_natSumRange_le {R : Type u} [OrderedDomain R] (c : R) :
    ∀ (m : Nat) (f g : Nat → Nat),
      (∀ j, j < m → leR (c * natCastR (g j)) 1) →
      leR (c * natCastR (natSumRange m (fun j => f j * g j)))
          (natCastR (natSumRange m f))
  | 0, _, _, _ => by
    change leR (c * natCastR 0) (natCastR 0)
    rw [natCastR_zero, mul_zero_eq]
    exact leR_refl 0
  | m + 1, f, g, hle => by
    change leR (c * natCastR (natSumRange m (fun j => f j * g j) + f m * g m))
               (natCastR (natSumRange m f + f m))
    rw [natCastR_add, natCastR_add, CommRing.left_distrib, natCastR_mul]
    have ih := scaled_natSumRange_le c m f g (fun j hj => hle j (by omega))
    have hlast : leR (c * (natCastR (f m) * natCastR (g m))) (natCastR (f m)) := by
      rw [mul_left_comm_eq c (natCastR (f m)) (natCastR (g m))]
      have hm := mul_leR_mul_of_nonneg_left (natCastR_nonneg (f m)) (hle m (by omega))
      rw [mul_one_eq] at hm
      exact hm
    exact add_leR_add ih hlast

/-- Universal refutation of rescaled binomial-entry tensors for ALL orders `m = d + 2 ≥ 2`:
    over any ordered domain `R` (`ℤ`, `ℚ`, `ℝ`), for ANY nonnegative scaling factor `c ≥ 0`
    such that `c * B_{m, 2}` satisfies `|a| ≤ 1` (in particular `c = 1 / C(m, ⌊m/2⌋)`),
    EVERY real `H`-eigenpair `(x, λ)` of `c * B_{m, 2}` satisfies `|λ| < 2^{m-1}` — strictly
    failing to attain the sharp entrywise bound `2^{m-1}` achieved by `J_{m, 2}`! -/
theorem refutation_binomial_entry_rescaled_suboptimal {R : Type u} [OrderedDomain R]
    (d : Nat) {c : R} (hc : leR 0 c)
    (hBound : EntryBoundedAbs (fun α : Idx 2 (d + 2) => c * binomialEntryTensor (d + 2) α) 1)
    {x : Fin 2 → R} {lam : R}
    (heig : IsHEigenpair (fun α : Idx 2 (d + 2) => c * binomialEntryTensor (d + 2) α) x lam) :
    ltR (absR lam) (rpow (natCastR 2) (d + 1)) := by
  -- Step 1: for every `k ≤ d + 2`, `c * C(d + 2, k) ≤ 1`
  have hck : ∀ k : Nat, k ≤ d + 2 → leR (c * natCastR (binom (d + 2) k)) 1 := by
    intro k hk
    let αk := idxWithOnes (d + 2) k hk
    have hb := hBound αk
    dsimp only [binomialEntryTensor] at hb
    rw [countVal_idxWithOnes] at hb
    have hnn : leR 0 (c * natCastR (binom (d + 2) k)) :=
      mul_nonneg_leR hc (natCastR_nonneg _)
    rw [absR_of_nonneg hnn] at hb
    exact hb
  -- Step 2: at `k = 1`, `c * (d + 2) ≤ 1` with `d + 2 ≥ 2`, forcing `c < 1`
  have hc_lt_one : ltR c 1 := by
    have hk1 := hck 1 (by omega)
    rw [binom_one_right] at hk1
    cases leR_total 1 c with
    | inl h1c =>
      have h2_le : leR (natCastR 2 : R) (c * natCastR (d + 2)) := by
        have h_n : leR (natCastR 2 : R) (natCastR (d + 2)) := natCastR_leR_of_le (by omega)
        have hm := mul_leR_mul_nonneg zero_ltR_one.1 (natCastR_nonneg 2) h1c h_n
        rw [one_mul_eq] at hm
        exact hm
      have h2_le_1 := leR_trans h2_le hk1
      have h1_lt_2 : ltR (1 : R) (natCastR 2) := by
        rw [← natCastR_one]
        exact natCastR_ltR_of_lt (by omega)
      exact False.elim (not_leR_of_ltR h1_lt_2 h2_le_1)
    | inr hc1 =>
      by_cases heq : c = 1
      · subst heq
        rw [one_mul_eq, ← natCastR_one] at hk1
        have hlt : ltR (natCastR 1 : R) (natCastR (d + 2)) := natCastR_ltR_of_lt (by omega)
        exact False.elim (not_leR_of_ltR hlt hk1)
      · exact ⟨hc1, heq⟩
  -- Step 3: show row sum `c * C(2d + 3, d + 1) < 2^{d + 1}` via Vandermonde + `binom_row_sum`
  have hrow_lt : ltR (c * natCastR (binom (2 * d + 3) (d + 1)))
      (rpow (natCastR 2) (d + 1)) := by
    have hv := vandermonde_binom_row1 (d + 1)
    have heq2d : 2 * (d + 1) + 1 = 2 * d + 3 := by omega
    rw [heq2d] at hv
    rw [← hv, natSumRange_succ_shift (d + 1), natCastR_add, CommRing.left_distrib]
    rw [binom_succ_zero, binom_succ_zero, Nat.one_mul, natCastR_one, mul_one_eq]
    have htail_le : leR
        (c * natCastR (natSumRange (d + 1)
          (fun j => binom (d + 1) (j + 1) * binom (d + 2) (j + 1))))
        (natCastR (natSumRange (d + 1) (fun j => binom (d + 1) (j + 1)))) :=
      scaled_natSumRange_le c (d + 1)
        (fun j => binom (d + 1) (j + 1))
        (fun j => binom (d + 2) (j + 1))
        (fun j hj => hck (j + 1) (by omega))
    have hsum_lt := add_ltR_add_of_ltR_of_leR hc_lt_one htail_le
    have hpow_eq : (1 : R) + natCastR (natSumRange (d + 1) (fun j => binom (d + 1) (j + 1))) =
        rpow (natCastR 2) (d + 1) := by
      rw [← natCastR_pow, ← binom_row_sum (d + 1), natSumRange_succ_shift (d + 1),
          binom_succ_zero, natCastR_add, natCastR_one]
    rw [hpow_eq] at hsum_lt
    exact hsum_lt
  -- Step 4: apply `gershgorin_nonneg_row_bound_real` to `c * B_{d+2, 2}`
  have hle_rad : leR (absR lam) (c * natCastR (binom (2 * d + 3) (d + 1))) := by
    have hA_nn : ∀ α : Idx 2 (d + 2), leR 0 (c * binomialEntryTensor (d + 2) α) :=
      fun _ => mul_nonneg_leR hc (natCastR_nonneg _)
    apply gershgorin_nonneg_row_bound_real (by omega) hA_nn ?_ heig
    intro i
    have hcont : contract (fun α : Idx 2 (d + 2) => c * binomialEntryTensor (d + 2) α) (fun _ => 1) i =
        c * contract (binomialEntryTensor (d + 2)) (fun _ => 1) i := by
      unfold contract sumIdx
      rw [← sumList_mul_left]
      apply sumList_congr; intro t _
      exact CommRing.mul_assoc c _ _
    rw [hcont, contract_binomialEntryTensor_ones (d + 1) i]
    have heq2d : 2 * (d + 1) + 1 = 2 * d + 3 := by omega
    rw [heq2d]
    exact leR_refl _
  exact ltR_of_leR_of_ltR hle_rad hrow_lt

/-- Even-order sign non-uniqueness (`m = 4, n = 2`): `s^{⊗ 4}` with `s = (1, -1)`
    (`F(x_1, x_2) = (x_1 - x_2)^4`) is symmetric, satisfies `|a| ≤ 1`, attains the sharp
    bound `λ_H = 8 = 2^{4-1}`, and is distinct from both `+J_{4, 2}` and `-J_{4, 2}`. -/
theorem refutation_even_order_sign_nonuniqueness :
    let s : Fin 2 → Int := fun i => if i.val = 0 then 1 else -1
    let A : Idx 2 4 → Int := rankOneTensor 1 s
    IsSymmetric A ∧ EntryBoundedAbs A 1 ∧
    IsHEigenpair A s 8 ∧
    A ≠ allOnesTensor 2 4 ∧ A ≠ (fun α => -(allOnesTensor 2 4 α)) := by
  dsimp only
  let s : Fin 2 → Int := fun i => if i.val = 0 then 1 else -1
  let A : Idx 2 4 → Int := rankOneTensor 1 s
  have hs_abs : ∀ i : Fin 2, absR (s i) = 1 := by
    intro ⟨v, hv⟩
    cases v with
    | zero =>
      change absR (1 : Int) = 1
      exact absR_of_nonneg (zero_ltR_one (R := Int)).1
    | succ v' =>
      cases v' with
      | zero =>
        change absR (-(1 : Int)) = 1
        rw [absR_neg]
        exact absR_of_nonneg (zero_ltR_one (R := Int)).1
      | succ _ => omega
  refine ⟨isSymmetric_rankOneTensor 1 s, ?_, ?_, ?_, ?_⟩
  · intro α
    change leR (absR (rankOneTensor 1 s α)) 1
    unfold rankOneTensor
    rw [one_mul_eq, absR_idxProd]
    have hc : (fun i : Fin 2 => absR (s i)) = (fun _ => (1 : Int)) := funext hs_abs
    rw [hc, idxProd_ones]
    exact leR_refl 1
  · refine ⟨⟨⟨0, by omega⟩, by decide⟩, ?_⟩
    intro i
    change contract (rankOneTensor 1 s) s i = 8 * rpow (s i) 3
    rw [contract_rankOneTensor, one_mul_eq]
    have hsum : sumFin (fun j : Fin 2 => s j * s j) = 2 := by
      rw [sumFin_two]
      rfl
    have hpow : rpow (2 : Int) 3 = 8 := rfl
    rw [hsum, hpow]
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ => omega
  · intro heq
    have hval := congrFun heq
      (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨0, by omega⟩
        (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨1, by omega⟩ Idx.nil))))
    change (-1 : Int) = 1 at hval
    omega
  · intro heq
    have hval := congrFun heq
      (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨0, by omega⟩
        (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨0, by omega⟩ Idx.nil))))
    change (1 : Int) = -1 at hval
    omega

/-! ### 4. Frobenius (`‖A‖_F ≤ 1`) and `ℓ_1` (`‖A‖_1 ≤ 1`) Refutations -/

/-- Under Frobenius normalization `‖A‖_F^2 ≤ 1`, for every order `m = d + 3 ≥ 3` and positive
    exponent `k ≥ 1`, every `Z`-eigenvalue satisfies `|λ_Z| ≤ 1 < m^k`, attained by the
    single-variable monomial tensor `e_0^{⊗ m}`. -/
theorem refutation_frob_Z_bound_lt_deg_pow {R : Type u} [OrderedDomain R]
    {n : Nat} (hn : n ≥ 1) (d : Nat) {k : Nat} (hk : k ≥ 1) :
    (∀ (A : Idx n (d + 3) → R) (x : Fin n → R) (lam : R),
      leR (frobNormSq A) 1 → IsZEigenpair A x lam →
      leR (absR lam) 1 ∧ ltR (absR lam) (natCastR ((d + 3) ^ k))) ∧
    (∃ (A : Idx n (d + 3) → R) (x : Fin n → R),
      IsSymmetric A ∧ frobNormSq A = 1 ∧ IsZEigenpair A x 1) := by
  refine ⟨?_, ?_⟩
  · intro A x lam hf hz
    have hb := leR_trans (frob_Z_bound hz) hf
    rw [← mul_one_eq (1 : R)] at hb
    have habs : leR (absR lam) 1 := (sq_leR_sq_iff_absR_leR zero_ltR_one.1).mp hb
    have hlt_pow : ltR (1 : R) (natCastR ((d + 3) ^ k)) := by
      rw [← natCastR_one]
      apply natCastR_ltR_of_lt
      have hge : d + 3 ≤ (d + 3) ^ k := nat_le_pow_self (by omega) hk
      omega
    exact ⟨habs, ltR_of_leR_of_ltR habs hlt_pow⟩
  · have hm := monomial_attains_frob_Z_bound (R := R) n (d + 2) hn
    exact ⟨monomialTensor (d + 3) ⟨0, hn⟩, stdBasisVec ⟨0, hn⟩, hm.1, hm.2.1, hm.2.2⟩

/-- Under Frobenius normalization `‖A‖_F^2 = 1` over `ℚ`, for every fixed order `m = d + 3 ≥ 3`
    and every function `F : Nat → Nat` of the degree alone, there exists `n = k^2` such that
    `k^{-m} J_{m, k^2}` has `‖A‖_F^2 = 1` and `H`-eigenvalue `λ_H = k^{m-2} > F(m)`. -/
theorem refutation_frob_H_exceeds_any_degree_bound (d : Nat) (F : Nat → Nat) :
    ∃ (n : Nat) (A : Idx n (d + 3) → RatField) (x : Fin n → RatField) (lam : RatField),
      n ≥ 4 ∧ IsSymmetric A ∧ frobNormSq A = 1 ∧
      IsHEigenpair A x lam ∧ ltR (natCastR (F (d + 3))) (absR lam) := by
  let k := F (d + 3) + 2
  let n := k * k
  let c : RatField := RatField.mk 1 ((k ^ (d + 3) : Nat) : Int) (by
    have hk : k ≥ 1 := by omega
    have hp : k ≤ k ^ (d + 3) := nat_le_pow_self (n := k) (d := d + 3) hk (by omega)
    omega)
  let A : Idx n (d + 3) → RatField := fun _ => c
  let lam : RatField := natCastR (k ^ (d + 1))
  have hn4 : n ≥ 4 := by
    have : 2 * 2 ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
    omega
  refine ⟨n, A, fun _ => 1, lam, hn4, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · -- `frobNormSq A = (k^2)^{d+3} * (1 / k^{d+3})^2 = 1`
    unfold frobNormSq
    dsimp only [A]
    rw [sumIdx_const, ← natCastR_pow, RatField.natCastR_eq_mk,
        RatField.mk_mul, RatField.mk_mul]
    change RatField.mk _ _ _ = RatField.mk 1 1 (by omega)
    rw [RatField.mk_eq_iff]
    have hpow_sq : (k * k) ^ (d + 3) = k ^ (d + 3) * k ^ (d + 3) := by
      induction (d + 3) with
      | zero => rfl
      | succ m ih =>
        rw [Nat.pow_succ, Nat.pow_succ, ih]
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hpow_sq]
    simp only [int_ofNat_mul, Int.mul_one, Int.one_mul]
  · -- `IsHEigenpair A (fun _ => 1) (k^{d+1})`
    refine ⟨⟨⟨0, by omega⟩, IntegralDomain.zero_ne_one.symm⟩, ?_⟩
    intro i
    unfold contract
    dsimp only [A, lam]
    have hc : sumIdx (fun t : Idx n (d + 2) => c * idxProd (fun _ => (1 : RatField)) t) =
        rpow (natCastR n) (d + 2) * c := by
      have h1 : (fun t : Idx n (d + 2) => c * idxProd (fun _ => (1 : RatField)) t) =
          (fun _ => c) := by
        funext t; rw [idxProd_ones, mul_one_eq]
      rw [h1, sumIdx_const]
    rw [hc, rpow_one_base, mul_one_eq, ← natCastR_pow,
        RatField.natCastR_eq_mk, RatField.natCastR_eq_mk]
    dsimp only [c]
    rw [RatField.mk_mul, RatField.mk_eq_iff]
    have hpow_rel : (k * k) ^ (d + 2) = k ^ (d + 1) * k ^ (d + 3) := by
      have hsq : ∀ m : Nat, (k * k) ^ m = k ^ m * k ^ m := by
        intro m; induction m with
        | zero => rfl
        | succ m ih =>
          rw [Nat.pow_succ, Nat.pow_succ, ih]
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [hsq (d + 2)]
      have he1 : d + 2 = (d + 1) + 1 := by omega
      have he2 : d + 3 = (d + 2) + 1 := by omega
      rw [he2, Nat.pow_succ k (d + 2), he1, Nat.pow_succ k (d + 1)]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rw [hpow_rel]
    simp only [int_ofNat_mul, Int.mul_one, Int.one_mul]
  · -- `F(d + 3) < k ≤ k^{d+1}`
    dsimp only [lam]
    rw [absR_of_nonneg (natCastR_nonneg _)]
    apply natCastR_ltR_of_lt
    have hle : k ≤ k ^ (d + 1) := nat_le_pow_self (by omega) (by omega)
    omega

/-- Under `ℓ_1` normalization `‖A‖_1 = 1` over `ℚ`, the normalized binomial/all-ones tensor
    `2^{-m} J_{m, 2}` (`m = d + 2 ≥ 2`) achieves `|λ_H| ≤ 1/2 < 1`, whereas the coordinate
    monomial tensor `e_0^{⊗ m}` has `‖A‖_1 = 1` and achieves `λ_H = 1`. -/
theorem refutation_l1_binomial_suboptimal (d : Nat) :
    let c : RatField := RatField.mk 1 ((2 ^ (d + 2) : Nat) : Int) (by
      have hp : 2 ≤ 2 ^ (d + 2) := nat_le_pow_self (n := 2) (d := d + 2) (by omega) (by omega)
      omega)
    let Abin : Idx 2 (d + 2) → RatField := fun _ => c
    let Amon : Idx 2 (d + 2) → RatField := monomialTensor (d + 2) ⟨0, by omega⟩
    l1Norm Abin = 1 ∧
    (∀ (x : Fin 2 → RatField) (lam : RatField),
      IsHEigenpair Abin x lam → leR (absR lam) (RatField.mk 1 2 (by omega))) ∧
    l1Norm Amon = 1 ∧ IsHEigenpair Amon (stdBasisVec ⟨0, by omega⟩) 1 ∧
    ltR (RatField.mk 1 2 (by omega)) 1 := by
  dsimp only
  let c : RatField := RatField.mk 1 ((2 ^ (d + 2) : Nat) : Int) (by
    have hp : 2 ≤ 2 ^ (d + 2) := nat_le_pow_self (n := 2) (d := d + 2) (by omega) (by omega)
    omega)
  have hc_nn : leR 0 c := by
    change leR (RatField.mk 0 1 (by omega)) c
    rw [RatField.leR_mk_iff]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold l1Norm
    have h1 : (fun α : Idx 2 (d + 2) => absR c) = (fun _ => c) := by
      funext _; exact absR_of_nonneg hc_nn
    rw [h1, sumIdx_const, ← natCastR_pow, RatField.natCastR_eq_mk, RatField.mk_mul]
    change RatField.mk _ _ _ = RatField.mk 1 1 (by omega)
    rw [RatField.mk_eq_iff]
    simp only [Int.mul_one, Int.one_mul]
  · intro x lam heig
    apply gershgorin_nonneg_row_bound_real (by omega) (fun _ => hc_nn) ?_ heig
    intro i
    unfold contract
    have h1 : (fun t : Idx 2 (d + 1) => c * idxProd (fun _ => (1 : RatField)) t) =
        (fun _ => c) := by
      funext t; rw [idxProd_ones, mul_one_eq]
    rw [h1, sumIdx_const, ← natCastR_pow, RatField.natCastR_eq_mk, RatField.mk_mul,
        RatField.leR_mk_iff]
    have hp : 2 ^ (d + 2) = 2 ^ (d + 1) * 2 := by rw [Nat.pow_succ]
    rw [hp]
    simp only [int_ofNat_mul, Int.mul_one, Int.one_mul]
    exact Int.le_refl _
  · -- `l1Norm Amon = 1`
    unfold l1Norm monomialTensor rankOneTensor
    let k0 : Fin 2 := ⟨0, by omega⟩
    have hv0 : ∀ j : Fin 2, leR (0 : RatField) (stdBasisVec k0 j) := by
      intro j; unfold stdBasisVec
      by_cases hj : j = k0
      · rw [if_pos hj]; exact zero_ltR_one.1
      · rw [if_neg hj]; exact leR_refl 0
    have hc : (fun α : Idx 2 (d + 2) => absR (1 * idxProd (stdBasisVec (S := RatField) k0) α)) =
        (fun α => idxProd (stdBasisVec (S := RatField) k0) α) := by
      funext α
      rw [one_mul_eq]
      exact absR_of_nonneg (idxProd_nonneg hv0 α)
    rw [hc, sumIdx_idxProd]
    have hsum : sumFin (stdBasisVec (S := RatField) k0) = 1 := by
      rw [sumFin_two]
      unfold stdBasisVec
      have hne : (⟨1, by omega⟩ : Fin 2) ≠ k0 := fin2_zero_ne_one.symm
      rw [if_pos rfl, if_neg hne, add_zero_eq]
    rw [hsum, rpow_one_base]
  · -- `IsHEigenpair Amon (stdBasisVec 0) 1`
    let k0 : Fin 2 := ⟨0, by omega⟩
    refine ⟨⟨k0, by unfold stdBasisVec; rw [if_pos rfl]; exact IntegralDomain.zero_ne_one.symm⟩, ?_⟩
    intro i
    rw [contract_monomialTensor, one_mul_eq]
    have hk0 : stdBasisVec (S := RatField) k0 k0 = 1 := by unfold stdBasisVec; rw [if_pos rfl]
    rw [hk0, rpow_one_base, mul_one_eq]
    unfold stdBasisVec
    by_cases hi : i = k0
    · rw [if_pos hi, rpow_one_base]
    · rw [if_neg hi, rpow_zero_base (k := d + 1) (by omega)]
  · change ltR (RatField.mk 1 2 (by omega)) (RatField.mk 1 1 (by omega))
    rw [RatField.ltR_mk_iff]
    omega

/-! ### 5. Complex `E`-Eigenvalues (`x^T x = 1` in `ℚ[i]`) Are Unbounded at Fixed `(m=3, n=2)` -/

private theorem e_pythag_T (T : Int) :
    (T * T + 1) * (T * T + 1) - (T * T - 1) * (T * T - 1) = (2 * T) * (2 * T) := by
  let U := T * T
  have h1 : (U + 1) * (U + 1) = U * U + 2 * U + 1 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
  have h2 : (U - 1) * (U - 1) = U * U - 2 * U + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_one, Int.one_mul]; omega
  have h3 : (2 * T) * (2 * T) = (2 * 2) * U := by
    dsimp only [U]
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  change (U + 1) * (U + 1) - (U - 1) * (U - 1) = (2 * T) * (2 * T)
  rw [h1, h2, h3]
  omega

private theorem e_rat_norm (P Q D : Int) (hD : 0 < D) (hPQD : P * P - Q * Q = D * D) :
    RatField.mk P D hD * RatField.mk P D hD -
      RatField.mk Q D hD * RatField.mk Q D hD = 1 := by
  rw [RatField.mk_mul, RatField.mk_mul, RatField.mk_sub]
  change RatField.mk _ _ _ = RatField.mk 1 1 (by omega)
  rw [RatField.mk_eq_iff, Int.neg_mul, ← Int.sub_eq_add_neg, ← Int.sub_mul, hPQD]
  simp only [Int.mul_one, Int.one_mul]

private theorem e_rat_mode0 (P Q D W : Int)
    (hD : 0 < D) (h2W : 0 < 2 * W) (hDW : 0 < D * W)
    (hWeq : W = 2 * (P * P) + Q * Q) :
    RatField.mk 1 2 (by omega) * (RatField.mk P D hD * RatField.mk P D hD) -
      RatField.mk (P * P) (2 * W) h2W * (RatField.mk Q D hD * RatField.mk Q D hD) =
      RatField.mk ((P * P) * P) (D * W) hDW * RatField.mk P D hD := by
  rw [RatField.mk_mul, RatField.mk_mul, RatField.mk_mul, RatField.mk_mul,
      RatField.mk_sub, RatField.mk_mul, RatField.mk_eq_iff, Int.neg_mul]
  have hWQ : 2 * W - 2 * (Q * Q) = 4 * (P * P) := by omega
  have hstep : 1 * (P * P) * (2 * W * (D * D)) + -(P * P * (Q * Q) * (2 * (D * D))) =
      (P * P) * (4 * (P * P) * (D * D)) := by
    rw [← hWQ, Int.sub_mul, Int.mul_sub]
    simp only [Int.one_mul, Int.sub_eq_add_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  rw [hstep]
  have h4 : (4 : Int) = 2 * 2 := rfl
  rw [h4]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

private theorem e_rat_mode1 (P Q D W : Int)
    (hD : 0 < D) (h2W : 0 < 2 * W) (hDW : 0 < D * W) :
    RatField.mk (P * P) (2 * W) h2W * (RatField.mk P D hD * RatField.mk Q D hD) +
      RatField.mk (P * P) (2 * W) h2W * (RatField.mk Q D hD * RatField.mk P D hD) =
      RatField.mk ((P * P) * P) (D * W) hDW * RatField.mk Q D hD := by
  rw [RatField.mk_mul, RatField.mk_mul, RatField.mk_mul, RatField.mk_mul,
      RatField.mk_add, RatField.mk_mul, RatField.mk_eq_iff]
  have hdouble : (P * P) * (P * Q) * (2 * W * (D * D)) + (P * P) * (Q * P) * (2 * W * (D * D)) =
      2 * ((P * P) * (P * Q) * (2 * W * (D * D))) := by
    rw [Int.mul_comm Q P]
    omega
  rw [hdouble]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

private theorem e_poly_U (U : Int) (hU : 0 ≤ U) :
    (2 * U) * (2 * ((U + 1) * (U + 1)) + (U - 1) * (U - 1)) <
      6 * (((U + 1) * (U + 1)) * (U + 1)) := by
  have hU2 : 0 ≤ U * U := Int.mul_nonneg hU hU
  have h1 : (U + 1) * (U + 1) = U * U + 2 * U + 1 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
  have h2 : (U - 1) * (U - 1) = U * U - 2 * U + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_one, Int.one_mul]; omega
  have h3 : (2 * U) * (2 * (U * U + 2 * U + 1) + (U * U - 2 * U + 1)) =
      6 * (U * (U * U)) + 4 * (U * U) + 6 * U := by
    have hw : 2 * (U * U + 2 * U + 1) + (U * U - 2 * U + 1) = 3 * (U * U) + 2 * U + 3 := by omega
    rw [hw, Int.mul_add, Int.mul_add]
    have ha : (2 * U) * (3 * (U * U)) = (2 * 3) * (U * (U * U)) := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have hb : (2 * U) * (2 * U) = (2 * 2) * (U * U) := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have hc : (2 * U) * 3 = (2 * 3) * U := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [ha, hb, hc]
    omega
  have h4 : 6 * ((U * U + 2 * U + 1) * (U + 1)) =
      6 * (U * (U * U)) + 18 * (U * U) + 18 * U + 6 := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul, Int.mul_one]
    have hd : (2 * U) * U = 2 * (U * U) := by rw [Int.mul_assoc]
    have he : (U * U) * U = U * (U * U) := Int.mul_comm _ _
    rw [hd, he]
    omega
  rw [h1, h2, h3, h4]
  omega

private def eOrbitVal (a0 a2 : RatField) : Nat → RatField
  | 0 => a0
  | 2 => a2
  | _ => 0

private theorem e_frob_le_one (a0 a2 : RatField)
    (ha0_sq : a0 * a0 = RatField.mk 1 4 (by omega))
    (ha2_nn : leR 0 a2)
    (ha2_le : leR a2 (RatField.mk 1 4 (by omega))) :
    leR (frobNormSq (fun α : Idx 2 3 => eOrbitVal a0 a2 (countVal ⟨1, by omega⟩ α))) 1 := by
  unfold frobNormSq
  rw [sumIdx_succ_ord, sumFin_two]
  have hexp_idx2 : ∀ F : Idx 2 2 → RatField,
      sumIdx F =
        (F (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨0, by omega⟩ Idx.nil)) +
         F (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨1, by omega⟩ Idx.nil))) +
        (F (Idx.cons ⟨1, by omega⟩ (Idx.cons ⟨0, by omega⟩ Idx.nil)) +
         F (Idx.cons ⟨1, by omega⟩ (Idx.cons ⟨1, by omega⟩ Idx.nil))) := by
    intro F
    rw [sumIdx_succ_ord, sumFin_two, sumIdx_succ_ord, sumFin_two,
        sumIdx_succ_ord, sumFin_two,
        sumIdx_zero_ord, sumIdx_zero_ord, sumIdx_zero_ord, sumIdx_zero_ord]
  rw [hexp_idx2, hexp_idx2]
  have h01 : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := fin2_zero_ne_one
  simp only [countVal_cons, countVal_nil, h01, ite_false, ite_true,
             Nat.zero_add, Nat.add_zero, eOrbitVal]
  simp only [zero_mul_eq, add_zero_eq, zero_add_eq]
  have ha0_sq_le : leR (a0 * a0) (RatField.mk 1 4 (by omega)) := by
    rw [ha0_sq]; exact leR_refl _
  have ha2_sq_le : leR (a2 * a2) (RatField.mk 1 16 (by omega)) := by
    have h := mul_leR_mul_nonneg ha2_nn ha2_nn ha2_le ha2_le
    rw [RatField.mk_mul] at h
    exact h
  have hsum_le := add_leR_add
    (add_leR_add ha0_sq_le ha2_sq_le)
    (add_leR_add ha2_sq_le ha2_sq_le)
  apply leR_trans hsum_le
  rw [RatField.mk_add, RatField.mk_add, RatField.mk_add]
  change leR (RatField.mk _ _ _) (RatField.mk 1 1 (by omega))
  rw [RatField.leR_mk_iff]
  omega

private def eComplexVec (C S : RatField) : Fin 2 → ComplexOver RatField :=
  fun i => if i.val = 0 then ⟨C, 0⟩ else ⟨0, S⟩

private theorem eComplexVec_zero (C S : RatField) {h : 0 < 2} :
    eComplexVec C S ⟨0, h⟩ = ⟨C, 0⟩ := rfl

private theorem eComplexVec_one (C S : RatField) {h : 1 < 2} :
    eComplexVec C S ⟨1, h⟩ = ⟨0, S⟩ := rfl

private theorem e_complex_eigenpair (a0 a2 C S lam : RatField)
    (hnorm : C * C - S * S = 1)
    (hmode0 : a0 * (C * C) - a2 * (S * S) = lam * C)
    (hmode1 : a2 * (C * S) + a2 * (S * C) = lam * S) :
    IsComplexEEigenpair
      (fun α : Idx 2 3 => eOrbitVal a0 a2 (countVal ⟨1, by omega⟩ α))
      (eComplexVec C S)
      (ComplexOver.ofReal lam) := by
  have hexp_idx2_c : ∀ F : Idx 2 2 → ComplexOver RatField,
      sumIdx F =
        (F (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨0, by omega⟩ Idx.nil)) +
         F (Idx.cons ⟨0, by omega⟩ (Idx.cons ⟨1, by omega⟩ Idx.nil))) +
        (F (Idx.cons ⟨1, by omega⟩ (Idx.cons ⟨0, by omega⟩ Idx.nil)) +
         F (Idx.cons ⟨1, by omega⟩ (Idx.cons ⟨1, by omega⟩ Idx.nil))) := by
    intro F
    rw [sumIdx_succ_ord, sumFin_two, sumIdx_succ_ord, sumFin_two,
        sumIdx_succ_ord, sumFin_two,
        sumIdx_zero_ord, sumIdx_zero_ord, sumIdx_zero_ord, sumIdx_zero_ord]
  refine ⟨?_, ?_⟩
  · rw [sumFin_two, eComplexVec_zero, eComplexVec_one]
    apply ComplexOver.ext
    · dsimp only [ComplexOver.add_re, ComplexOver.mul_re, ComplexOver.one_re]
      rw [mul_zero_eq, sub_zero_eq, zero_sub_eq, ← CommRing.sub_eq_add_neg]
      exact hnorm
    · dsimp only [ComplexOver.add_im, ComplexOver.mul_im, ComplexOver.one_im]
      simp only [mul_zero_eq, zero_mul_eq, add_zero_eq]
  · intro i
    unfold contract
    rw [hexp_idx2_c]
    have h01 : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := fin2_zero_ne_one
    match i with
    | ⟨0, _⟩ =>
      simp only [countVal_cons, countVal_nil, h01, ite_false, ite_true,
                 Nat.zero_add, Nat.add_zero, eOrbitVal]
      simp only [idxProd_cons, idxProd_nil, eComplexVec_zero, eComplexVec_one,
                 mul_one_eq, ComplexOver.ofReal]
      apply ComplexOver.ext
      · simp only [ComplexOver.add_re, ComplexOver.mul_re, ComplexOver.mul_im,
                   mul_zero_eq, zero_mul_eq, add_zero_eq, zero_add_eq,
                   sub_zero_eq, zero_sub_eq, mul_neg_eq]
        rw [← CommRing.sub_eq_add_neg]
        exact hmode0
      · simp only [ComplexOver.add_im, ComplexOver.mul_re, ComplexOver.mul_im,
                   mul_zero_eq, zero_mul_eq, add_zero_eq, zero_add_eq,
                   sub_zero_eq, zero_sub_eq]
    | ⟨1, _⟩ =>
      simp only [countVal_cons, countVal_nil, h01, ite_false, ite_true,
                 Nat.zero_add, Nat.add_zero, eOrbitVal]
      simp only [idxProd_cons, idxProd_nil, eComplexVec_zero, eComplexVec_one,
                 mul_one_eq, ComplexOver.ofReal]
      apply ComplexOver.ext
      · simp only [ComplexOver.add_re, ComplexOver.mul_re, ComplexOver.mul_im,
                   mul_zero_eq, zero_mul_eq, add_zero_eq, zero_add_eq,
                   sub_zero_eq, zero_sub_eq]
      · simp only [ComplexOver.add_im, ComplexOver.mul_re, ComplexOver.mul_im,
                   mul_zero_eq, zero_mul_eq, add_zero_eq, zero_add_eq,
                   sub_zero_eq, zero_sub_eq]
        exact hmode1
    | ⟨_ + 2, h⟩ => omega

/-- Explicit rational family of `2 × 2 × 2` real symmetric tensors `A^{(t)}` (`t ≥ 2`),
    simultaneously bounded in `ℓ_∞` (`|a_{ijk}| ≤ 1`) and Frobenius norm (`‖A‖_F^2 ≤ 1`),
    whose complex `E`-eigenvalues (`z_1^2 + z_2^2 = 1` in `ℚ[i]`) grow unboundedly (`λ_E > M`). -/
theorem refutation_complex_E_eigenvalue_unbounded (M : RatField) :
    ∃ (A : Idx 2 3 → RatField) (z : Fin 2 → ComplexOver RatField) (lam : RatField),
      IsSymmetric A ∧ EntryBoundedAbs A 1 ∧ leR (frobNormSq A) 1 ∧
      IsComplexEEigenpair A z (ComplexOver.ofReal lam) ∧ ltR M lam := by
  have ⟨B_nat, hM_le⟩ : ∃ B_nat : Nat, leR M (natCastR B_nat) := by
    induction M using Quot.ind with
    | _ r =>
      let B := r.num.natAbs + 1
      refine ⟨B, ?_⟩
      rw [RatField.natCastR_eq_mk]
      change leR (RatField.mk r.num r.den r.den_pos) (RatField.mk (B : Int) 1 (by omega))
      rw [RatField.leR_mk_iff]
      have hd := r.den_pos
      have h1 : r.num ≤ (B : Int) := by omega
      have h2 : (B : Int) * 1 ≤ (B : Int) * r.den :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  let t : Nat := 6 * (B_nat + 1) + 2
  let T : Int := (t : Int)
  have hT_ge : 2 ≤ T := by dsimp only [T, t]; omega
  let P : Int := T * T + 1
  let Q : Int := T * T - 1
  let D : Int := 2 * T
  have hP_pos : 0 < P := by
    have : 0 ≤ T * T := Int.mul_nonneg (by omega) (by omega)
    dsimp only [P]; omega
  have hQ_pos : 0 < Q := by
    have : 4 ≤ T * T := Int.mul_le_mul hT_ge hT_ge (by omega) (by omega)
    dsimp only [Q]; omega
  have hD_pos : 0 < D := by dsimp only [D]; omega
  let W : Int := 2 * (P * P) + Q * Q
  have hW_pos : 0 < W := by
    have hp2 := Int.mul_pos hP_pos hP_pos
    have hq2 := Int.mul_pos hQ_pos hQ_pos
    dsimp only [W]; omega
  have h2W_pos : 0 < 2 * W := by omega
  have hDW_pos : 0 < D * W := Int.mul_pos hD_pos hW_pos
  let a0 : RatField := RatField.mk 1 2 (by omega)
  let a2 : RatField := RatField.mk (P * P) (2 * W) h2W_pos
  let A : Idx 2 3 → RatField := fun α => eOrbitVal a0 a2 (countVal ⟨1, by omega⟩ α)
  let C : RatField := RatField.mk P D hD_pos
  let S : RatField := RatField.mk Q D hD_pos
  let z : Fin 2 → ComplexOver RatField := eComplexVec C S
  let lam : RatField := RatField.mk ((P * P) * P) (D * W) hDW_pos
  have ha2_nn : leR 0 a2 := by
    change leR (RatField.mk 0 1 (by omega)) a2
    rw [RatField.leR_mk_iff]
    have hp2 := Int.mul_pos hP_pos hP_pos
    omega
  have ha2_le_quarter : leR a2 (RatField.mk 1 4 (by omega)) := by
    dsimp only [a2]
    rw [RatField.leR_mk_iff]
    have hq2 := Int.mul_pos hQ_pos hQ_pos
    dsimp only [W]
    omega
  refine ⟨A, z, lam, isSymmetric_of_countVal ⟨1, by omega⟩ (eOrbitVal a0 a2), ?_, ?_, ?_, ?_⟩
  · intro α
    dsimp only [A]
    match countVal ⟨1, by omega⟩ α with
    | 0 =>
      dsimp only [eOrbitVal]
      have ha0_nn : leR 0 a0 := by
        change leR (RatField.mk 0 1 (by omega)) a0; rw [RatField.leR_mk_iff]; omega
      rw [absR_of_nonneg ha0_nn]
      change leR a0 (RatField.mk 1 1 (by omega))
      rw [RatField.leR_mk_iff]; omega
    | 2 =>
      dsimp only [eOrbitVal]
      rw [absR_of_nonneg ha2_nn]
      apply leR_trans ha2_le_quarter
      change leR (RatField.mk 1 4 (by omega)) (RatField.mk 1 1 (by omega))
      rw [RatField.leR_mk_iff]; omega
    | 1 =>
      dsimp only [eOrbitVal]
      rw [absR_of_nonneg (leR_refl 0)]
      exact zero_ltR_one.1
    | _ + 3 =>
      change leR (absR 0) 1
      rw [absR_of_nonneg (leR_refl 0)]
      exact zero_ltR_one.1
  · exact e_frob_le_one a0 a2
      (by dsimp only [a0]; rw [RatField.mk_mul, RatField.mk_eq_iff]; omega)
      ha2_nn ha2_le_quarter
  · exact e_complex_eigenpair a0 a2 C S lam
      (e_rat_norm P Q D hD_pos (e_pythag_T T))
      (e_rat_mode0 P Q D W hD_pos h2W_pos hDW_pos rfl)
      (e_rat_mode1 P Q D W hD_pos h2W_pos hDW_pos)
  · have h1 : ltR M (natCastR (B_nat + 1)) :=
      ltR_of_leR_of_ltR hM_le (natCastR_ltR_of_lt (by omega))
    apply ltR_trans h1
    rw [RatField.natCastR_eq_mk]
    dsimp only [lam]
    rw [RatField.ltR_mk_iff]
    have hpoly : T * (D * W) < 6 * ((P * P) * P) := by
      have hU_nn : 0 ≤ T * T := Int.mul_nonneg (by omega) (by omega)
      have hU := e_poly_U (T * T) hU_nn
      have hTD : T * (D * W) = (2 * (T * T)) * W := by
        dsimp only [D]
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      rw [hTD]
      exact hU
    have hBT : 6 * ((B_nat + 1 : Nat) : Int) < T := by dsimp only [T, t]; omega
    have hmul_BT : 6 * (((B_nat + 1 : Nat) : Int) * (D * W)) < T * (D * W) := by
      have hdiff : 0 < (T - 6 * ((B_nat + 1 : Nat) : Int)) * (D * W) :=
        Int.mul_pos (by omega) hDW_pos
      rw [Int.sub_mul, Int.mul_assoc 6 ((B_nat + 1 : Nat) : Int) (D * W)] at hdiff
      omega
    rw [Int.mul_one]
    omega

/-! ### 6. Concrete Non-Vacuity Instantiations on `Int` and `RatField` -/

/-- Concrete `Int` instantiation of Qi's entrywise `H`-bound and odd-order all-ones rigidity. -/
theorem nonvacuous_int_entrywise_and_odd_rigidity {n k : Nat} (hn : n ≥ 1)
    {A : Idx n (2 * k + 3) → Int} (hSym : IsSymmetric A) (hA : EntryBoundedAbs A 1)
    {x : Fin n → Int} {lam : Int} (heig : IsHEigenpair A x lam) :
    leR (absR lam) (rpow (natCastR n) (2 * k + 2)) ∧
    (absR lam = rpow (natCastR n) (2 * k + 2) →
      (∀ α, A α = 1) ∨ (∀ α, A α = -1)) := by
  refine ⟨?_, ?_⟩
  · have hb := entrywise_H_bound_real (R := Int) hn (zero_ltR_one (R := Int)).1 hA heig
    rw [mul_one_eq] at hb
    exact hb
  · intro heq
    have heq1 : absR lam = rpow (natCastR n) (2 * k + 2) * 1 := by rw [mul_one_eq]; exact heq
    exact entrywise_H_rigidity_odd_real (R := Int) hn (zero_ltR_one (R := Int)) hSym hA heig heq1

/-- Concrete `RatField` instantiation of Banach's Frobenius `Z`-bound and rank-`1` rigidity. -/
theorem nonvacuous_rat_frob_Z_rigidity {n d : Nat}
    {A : Idx n (d + 1) → RatField} {x : Fin n → RatField} {lam : RatField}
    (hz : IsZEigenpair A x lam) :
    leR (lam * lam) (frobNormSq A) ∧
    (lam * lam = frobNormSq A → A = rankOneTensor lam x) :=
  ⟨frob_Z_bound hz, frob_Z_rigidity hz⟩

end Conjecture00000007176
