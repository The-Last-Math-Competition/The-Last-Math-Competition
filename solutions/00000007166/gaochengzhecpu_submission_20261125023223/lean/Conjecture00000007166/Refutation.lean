/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007166 in Core Lean 4.19.0 (zero external dependencies).

Module: Conjecture00000007166.Refutation
Purpose:
  Complete, rigorous refutation of Clause 2 ("and the minimum of the function is
  the harmonic mean") across ALL FOUR standard mathematical readings (Readings A,
  B, C, and D) over every `LinearOrderedField F`.
-/

import Conjecture00000007166.Kantorovich

namespace Conjecture00000007166

section Clause2Refutations

variable {F : Type u} [LinearOrderedField F]

/-!
### Reading A: Minimum of `K(κ) = (κ + 1)^2 / (4κ)` over `κ ≥ 1` (or `κ > 0`)
We prove:
  1. `K(κ) - 1 = (κ - 1)^2 / (4κ)`, so `1 ≤ K(κ)` for all `κ > 0`, `K(1) = 1`,
     and `K(κ) = 1 ↔ κ = 1`. Thus the unique global minimum of `K` is `1`.
  2. For every `κ > 1`, the normalized harmonic mean `HM(κ, 1) = 2κ / (κ + 1)`
     satisfies `1 < HM(κ, 1)`, hence `HM(κ, 1) ≠ 1`.
  3. Concrete rational counterexamples:
     - At `(m, M) = (1, 3)` (`κ = 3`): `min K = 1`, `K(3) = 4/3`, while
       `HM(3, 1) = 3/2`, with `3/2 ≠ 1` and `3/2 ≠ 4/3`.
     - At `(m, M) = (2, 2)` (`κ = 1`): `min K = K(1) = 1`, while `HM(2, 2) = 2 ≠ 1`.
-/

theorem one_lt_twoF : (1 : F) < twoF := by
  unfold twoF
  have ht := add_lt_add_left (LinearOrderedField.zero_lt_one (F := F)) (1 : F)
  rw [lofAddZero] at ht
  exact ht

theorem twoF_lt_threeF : (twoF : F) < threeF := by
  unfold threeF
  have ht := add_lt_add_left (LinearOrderedField.zero_lt_one (F := F)) (twoF : F)
  rw [lofAddZero] at ht
  exact ht

theorem one_lt_threeF : (1 : F) < threeF :=
  lt_trans one_lt_twoF twoF_lt_threeF

theorem twoF_lt_fourF : (twoF : F) < fourF := by
  unfold fourF
  have ht := add_lt_add_left (twoF_pos (F := F)) (twoF : F)
  rw [lofAddZero] at ht
  exact ht

theorem kantorovichConst_sub_one {κ : F} (hκ : κ ≠ 0) :
    kantorovichConst κ - 1 = ((κ - 1) * (κ - 1)) / (fourF * κ) := by
  unfold kantorovichConst
  have h4κ : fourF * κ ≠ 0 := mul_ne_zero fourF_ne_zero hκ
  have hsub : ((κ + 1) * (κ + 1)) / (fourF * κ) - 1 =
      ((κ + 1) * (κ + 1) - fourF * κ) / (fourF * κ) := by
    rw [sub_div, div_self h4κ]
  rw [hsub]
  congr 1
  calc
    (κ + 1) * (κ + 1) - fourF * κ
      = (κ * κ + twoF * κ + 1) - fourF * κ := by
        congr 1
        rw [lofLeftDistrib, lofRightDistrib, lofRightDistrib, lofMulOne, lofOneMul, lofMulOne,
            lofAddAssoc (κ * κ) κ (κ + 1), ← lofAddAssoc κ κ 1,
            ← twoF_mul κ, ← lofAddAssoc (κ * κ) (twoF * κ) 1]
    _ = κ * κ - twoF * κ + 1 := by
        rw [fourF_eq_two_mul_two, lofMulAssoc twoF twoF κ, twoF_mul (twoF * κ),
            lofSubEqAddNeg (_ + 1) _, lofAddAssoc (κ * κ + twoF * κ) 1 _,
            lofAddComm 1 _, ← lofAddAssoc (κ * κ + twoF * κ) _ 1]
        congr 1
        rw [neg_add_rev, lofAddAssoc (κ * κ) (twoF * κ) _,
            ← lofAddAssoc (twoF * κ) (-(twoF * κ)) (-(twoF * κ)),
            add_neg_cancel, lofZeroAdd, ← lofSubEqAddNeg]
    _ = (κ - 1) * (κ - 1) := by
        calc
          κ * κ - twoF * κ + 1
            = κ * κ - (κ + κ) + 1 := by rw [twoF_mul]
          _ = κ * κ - κ - κ + 1 := by rw [← sub_sub]
          _ = (κ * κ - κ) - (κ - 1) := by
              rw [sub_sub_eq_add_sub (κ * κ - κ) κ 1,
                  lofSubEqAddNeg (κ * κ - κ + 1) κ,
                  lofAddAssoc (κ * κ - κ) 1 (-κ),
                  lofAddComm 1 (-κ), ← lofAddAssoc, ← lofSubEqAddNeg]
          _ = κ * (κ - 1) - 1 * (κ - 1) := by
              rw [mul_sub, lofMulOne, lofOneMul]
          _ = (κ - 1) * (κ - 1) := (sub_mul κ 1 (κ - 1)).symm

theorem kantorovichConst_one : kantorovichConst (1 : F) = 1 := by
  have h := kantorovichConst_sub_one (Ne.symm (LinearOrderedField.zero_ne_one (F := F)))
  rw [sub_self, zero_mul, zero_div] at h
  exact sub_eq_zero.mp h

theorem one_le_kantorovichConst {κ : F} (hκ : 0 < κ) :
    1 ≤ kantorovichConst κ := by
  apply sub_nonneg.mp
  rw [kantorovichConst_sub_one (ne_of_gt hκ)]
  exact div_nonneg (sq_nonneg (κ - 1)) (le_of_lt (LinearOrderedField.mul_pos fourF_pos hκ))

theorem kantorovichConst_eq_one_iff {κ : F} (hκ : 0 < κ) :
    kantorovichConst κ = 1 ↔ κ = 1 := by
  have h4κ : 0 < fourF * κ := LinearOrderedField.mul_pos fourF_pos hκ
  constructor
  · intro h
    have h0 : kantorovichConst κ - 1 = 0 := by rw [h, sub_self]
    rw [kantorovichConst_sub_one (ne_of_gt hκ)] at h0
    have hnum : (κ - 1) * (κ - 1) = 0 := by
      have hm := (div_eq_iff (ne_of_gt h4κ)).mp h0
      rw [zero_mul] at hm
      exact hm
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hnum)
  · intro h
    rw [h, kantorovichConst_one]

/-- Predicate that `μ` is the minimum value of `f` on a domain predicate `P`. -/
def IsMinValueOn (f : F → F) (P : F → Prop) (μ : F) : Prop :=
  (∃ x, P x ∧ f x = μ) ∧ (∀ x, P x → μ ≤ f x)

/-- Reading A (Positive identification): The minimum of `K` on `[1, ∞)` AND on `(0, ∞)` is `1`. -/
theorem readingA_min_is_one :
    IsMinValueOn (F := F) kantorovichConst (fun κ => 1 ≤ κ) 1 ∧
    IsMinValueOn (F := F) kantorovichConst (fun κ => 0 < κ) 1 := by
  refine ⟨⟨⟨1, LinearOrderedField.le_refl 1, kantorovichConst_one⟩, ?_⟩,
          ⟨⟨1, LinearOrderedField.zero_lt_one, kantorovichConst_one⟩, ?_⟩⟩
  · intro κ hκ
    exact one_le_kantorovichConst (lt_of_lt_of_le LinearOrderedField.zero_lt_one hκ)
  · intro κ hκ
    exact one_le_kantorovichConst hκ

theorem isMinValueOn_unique {f : F → F} {P : F → Prop} {μ₁ μ₂ : F}
    (h1 : IsMinValueOn f P μ₁) (h2 : IsMinValueOn f P μ₂) : μ₁ = μ₂ := by
  rcases h1 with ⟨⟨x1, hx1, fx1⟩, hle1⟩
  rcases h2 with ⟨⟨x2, hx2, fx2⟩, hle2⟩
  have a : μ₁ ≤ μ₂ := fx2 ▸ hle1 x2 hx2
  have b : μ₂ ≤ μ₁ := fx1 ▸ hle2 x1 hx1
  exact LinearOrderedField.le_antisymm a b

/-- For every `κ > 1`, the normalized harmonic mean `HM(κ, 1)` is strictly greater than `1`. -/
theorem one_lt_harmonicMean_normalized {κ : F} (hκ : 1 < κ) :
    1 < harmonicMean κ 1 := by
  unfold harmonicMean
  have hκ_pos : 0 < κ := lt_trans LinearOrderedField.zero_lt_one hκ
  have hden_pos : 0 < κ + 1 := by
    have h := add_lt_add hκ_pos LinearOrderedField.zero_lt_one
    rw [lofAddZero] at h
    exact h
  rw [lt_div_iff_of_pos hden_pos, lofOneMul, lofMulOne, twoF_mul]
  exact add_lt_add_left hκ κ

/-- Concrete evaluation at `(m, M) = (1, 3)` (`κ = 3`):
    `K(3) = 4/3` whereas `HM(3, 1) = 3/2`, and `3/2 ≠ 1`, `3/2 ≠ 4/3`. -/
theorem counterexample_m1_M3 :
    kantorovichConst (threeF : F) = fourF / threeF ∧
    harmonicMean (threeF : F) 1 = threeF / twoF ∧
    (threeF : F) / twoF ≠ 1 ∧
    (threeF : F) / twoF ≠ fourF / threeF := by
  have h3p1 : (threeF : F) + 1 = fourF := by
    unfold threeF fourF twoF
    rw [lofAddAssoc, lofAddAssoc]
  have hk3 : kantorovichConst (threeF : F) = fourF / threeF := by
    unfold kantorovichConst
    rw [h3p1]
    apply (div_eq_div_iff (mul_ne_zero fourF_ne_zero threeF_ne_zero) threeF_ne_zero).mpr
    exact lofMulAssoc fourF fourF threeF
  have hhm3 : harmonicMean (threeF : F) 1 = threeF / twoF := by
    unfold harmonicMean
    rw [lofMulOne, h3p1]
    apply (div_eq_div_iff fourF_ne_zero twoF_ne_zero).mpr
    rw [fourF_eq_two_mul_two, lofMulComm threeF (twoF * twoF),
        lofMulAssoc twoF twoF threeF, lofMulComm twoF (twoF * threeF)]
  have hne1 : (threeF : F) / twoF ≠ 1 := by
    intro heq
    have hhm_gt : (1 : F) < harmonicMean threeF 1 :=
      one_lt_harmonicMean_normalized (one_lt_threeF (F := F))
    rw [hhm3, heq] at hhm_gt
    exact lt_irrefl 1 hhm_gt
  have hne43 : (threeF : F) / twoF ≠ fourF / threeF := by
    intro heq
    have hm := (div_eq_div_iff twoF_ne_zero threeF_ne_zero).mp heq
    -- 3 * 3 = 9 > 8 = 4 * 2 in any LinearOrderedField
    have hlt : (fourF : F) * twoF < threeF * threeF := by
      have hid : (threeF : F) * threeF - fourF * twoF = 1 := by
        unfold threeF fourF
        calc
          ((twoF : F) + 1) * (twoF + 1) - (twoF + twoF) * twoF
            = (twoF * twoF + (twoF + twoF) + 1) - (twoF * twoF + twoF * twoF) := by
              rw [lofLeftDistrib, lofRightDistrib, lofRightDistrib,
                  lofMulOne, lofOneMul, lofMulOne, lofRightDistrib,
                  lofAddAssoc (twoF * twoF) twoF (twoF + 1),
                  ← lofAddAssoc twoF twoF 1,
                  ← lofAddAssoc (twoF * twoF) (twoF + twoF) 1]
          _ = 1 := by
              have h22 : (twoF : F) + twoF = twoF * twoF := (twoF_mul twoF).symm
              rw [h22, lofAddComm (twoF * twoF + twoF * twoF) 1, add_sub_cancel]
      apply sub_pos.mp
      rw [hid]
      exact LinearOrderedField.zero_lt_one
    exact ne_of_gt hlt hm
  exact ⟨hk3, hhm3, hne1, hne43⟩

/-- Scale-invariance counterexample at `(m, M) = (2, 2)` (`κ = 1`):
    `K(2 / 2) = 1`, whereas `HM(2, 2) = 2 ≠ 1`. -/
theorem counterexample_m2_M2 :
    kantorovichConst ((twoF : F) / twoF) = 1 ∧
    harmonicMean (twoF : F) twoF = twoF ∧
    harmonicMean (twoF : F) twoF ≠ 1 := by
  have hk : kantorovichConst ((twoF : F) / twoF) = 1 := by
    rw [div_self twoF_ne_zero, kantorovichConst_one]
  have hhm : harmonicMean (twoF : F) twoF = twoF := by
    unfold harmonicMean
    have hsum : (twoF : F) + twoF = twoF * twoF := (twoF_mul twoF).symm
    rw [hsum]
    apply (div_eq_iff (mul_ne_zero twoF_ne_zero twoF_ne_zero)).mpr
    exact lofMulAssoc twoF twoF twoF
  rw [hhm]
  exact ⟨hk, rfl, ne_of_gt (one_lt_twoF (F := F))⟩

/-- **Refutation of Clause 2 under Reading A** (both unnormalized `HM(M, m)` and
    normalized `HM(M/m, 1)`): It is FALSE that for all `0 < m ≤ M` (or even `0 < m < M`),
    the minimum of `K` on `[1, ∞)` equals the harmonic mean. -/
theorem readingA_refuted :
    ¬ (∀ M m : F, 0 < m → m ≤ M →
        IsMinValueOn kantorovichConst (fun κ => 1 ≤ κ) (harmonicMean M m)) ∧
    ¬ (∀ M m : F, 0 < m → m < M →
        IsMinValueOn kantorovichConst (fun κ => 1 ≤ κ) (harmonicMean (M / m) 1)) := by
  have hmin1 := (readingA_min_is_one (F := F)).1
  constructor
  · intro hall
    have h := hall threeF 1 LinearOrderedField.zero_lt_one (le_of_lt (one_lt_threeF (F := F)))
    have heq : harmonicMean (threeF : F) 1 = 1 := isMinValueOn_unique h hmin1
    rcases counterexample_m1_M3 (F := F) with ⟨_, hhm3, hne1, _⟩
    rw [hhm3] at heq
    exact hne1 heq
  · intro hall
    have h := hall threeF 1 LinearOrderedField.zero_lt_one (one_lt_threeF (F := F))
    rw [div_one] at h
    have heq : harmonicMean (threeF : F) 1 = 1 := isMinValueOn_unique h hmin1
    rcases counterexample_m1_M3 (F := F) with ⟨_, hhm3, hne1, _⟩
    rw [hhm3] at heq
    exact hne1 heq

/-!
### Reading B: Minimum of the Kantorovich Quotient `x ↦ Q_A(x)` for Fixed SPD Matrix `A`
For every `n ≥ 1` and positive spectrum `λ`, `min_{x ≠ 0} Q_A(x) = 1` (attained at `e_0`),
which is NOT `HM(M, m)` and NOT `HM(M/m, 1)`.
-/

theorem readingB_min_quotient_is_one (n : Nat) (hn : 0 < n) (lam : Fin n → F) {M m : F}
    (hm_pos : 0 < m) (hmM : m ≤ M) (hlam_bounds : ∀ i, m ≤ lam i ∧ lam i ≤ M) :
    let k0 : Fin n := ⟨0, hn⟩
    (∃ i, basisVec (F := F) n k0 i ≠ 0) ∧
    kantorovichQuotient n lam (basisVec n k0) = 1 ∧
    ∀ x : Fin n → F, (∃ i, x i ≠ 0) → 1 ≤ kantorovichQuotient n lam x := by
  intro k0
  have hbz : ∃ i, basisVec (F := F) n k0 i ≠ 0 := by
    refine ⟨k0, ?_⟩
    unfold basisVec
    rw [if_pos rfl]
    exact Ne.symm LinearOrderedField.zero_ne_one
  have hk_pos : 0 < lam k0 := lt_of_lt_of_le hm_pos (hlam_bounds k0).1
  refine ⟨hbz, kantorovichQuotient_basisVec n lam k0 (ne_of_gt hk_pos), ?_⟩
  intro x hx
  exact (kantorovich_bounds_diag n lam x hm_pos hmM hlam_bounds hx).1

/-- **Refutation of Clause 2 under Reading B**:
    For the `2 × 2` SPD matrix `A = diag(1, 3)` (`m = 1, M = 3`), the minimum of
    `x ↦ Q_A(x)` over `x ≠ 0` is `1`, whereas `HM(3, 1) = 3/2 ≠ 1`. -/
theorem readingB_refuted :
    let lam : Fin 2 → F := fun i => if i.val = 0 then 1 else threeF
    (∃ x : Fin 2 → F, (∃ i, x i ≠ 0) ∧ kantorovichQuotient 2 lam x = 1) ∧
    (∀ x : Fin 2 → F, (∃ i, x i ≠ 0) → 1 ≤ kantorovichQuotient 2 lam x) ∧
    harmonicMean (threeF : F) 1 ≠ 1 := by
  intro lam
  have h13 : (1 : F) ≤ threeF := le_of_lt (one_lt_threeF (F := F))
  have hb : ∀ i : Fin 2, (1 : F) ≤ lam i ∧ lam i ≤ threeF := by
    intro i
    dsimp only [lam]
    by_cases hi : i.val = 0
    · rw [if_pos hi]
      exact ⟨LinearOrderedField.le_refl 1, h13⟩
    · rw [if_neg hi]
      exact ⟨h13, LinearOrderedField.le_refl threeF⟩
  have hmin := readingB_min_quotient_is_one (F := F) 2 (by decide) lam
    LinearOrderedField.zero_lt_one h13 hb
  rcases hmin with ⟨hbz, hval, hall⟩
  rcases counterexample_m1_M3 (F := F) with ⟨_, hhm3, hne1, _⟩
  refine ⟨⟨basisVec 2 ⟨0, by decide⟩, hbz, hval⟩, hall, ?_⟩
  rw [hhm3]
  exact hne1

/-!
### Reading C: Reciprocal / Wielandt-Kantorovich Lower-Bound Function `R(κ) = 4κ / (κ + 1)^2`
We prove ALL FOUR obstructions:
  1. `R(M/m) = HM(M, m) / AM(M, m)` is the *ratio* of HM to AM, NOT `HM(M, m)`:
     at `(m, M) = (1, 3)`, `R(3) = 3/4 ≠ 3/2 = HM(3, 1)`.
  2. `R(1) = 1` and `R(κ) ≤ 1` for all `κ > 0`, so `1` is the **maximum** of `R` on `[1, ∞)`.
  3. `R` is strictly decreasing on `[1, ∞)`, hence `R` has **no minimum** on `[1, ∞)`.
  4. `0` is the exact infimum (greatest lower bound) of `{R(κ) : κ ≥ 1}`: for all `κ ≥ 1`,
     `0 < R(κ) < 4 / κ`, and for every `ε > 0`, setting `κ = 1 + 4/ε > 1` yields `R(κ) < ε`.
-/

theorem reciprocalKantorovich_eq_inv {κ : F} (hκ : 0 < κ) :
    reciprocalKantorovichConst κ = (kantorovichConst κ)⁻¹ := by
  unfold reciprocalKantorovichConst kantorovichConst
  have h1 : 0 < κ + 1 := by
    have ht := add_lt_add hκ LinearOrderedField.zero_lt_one
    rw [lofAddZero] at ht
    exact ht
  have hsq : (κ + 1) * (κ + 1) ≠ 0 :=
    mul_ne_zero (ne_of_gt h1) (ne_of_gt h1)
  have h4κ : fourF * κ ≠ 0 := mul_ne_zero fourF_ne_zero (ne_of_gt hκ)
  exact (inv_div hsq h4κ).symm

theorem reciprocalKantorovich_eq_hm_div_am {M m : F} (hm : 0 < m) (hM : 0 < M) :
    reciprocalKantorovichConst (M / m) = harmonicMean M m / arithmeticMean M m := by
  have hκ : 0 < M / m := div_pos hM hm
  rw [reciprocalKantorovich_eq_inv hκ, kantorovichConst_eq_am_div_hm hm hM]
  have hMm : 0 < M + m := by
    have ht := add_lt_add hM hm
    rw [lofAddZero] at ht
    exact ht
  have ham : arithmeticMean M m ≠ 0 :=
    ne_of_gt (div_pos hMm twoF_pos)
  have hhm : harmonicMean M m ≠ 0 :=
    ne_of_gt (div_pos (LinearOrderedField.mul_pos (LinearOrderedField.mul_pos twoF_pos hM) hm) hMm)
  exact inv_div ham hhm

theorem kantorovichConst_strictMono_ge_one {κ₁ κ₂ : F}
    (h1 : 1 ≤ κ₁) (hlt : κ₁ < κ₂) :
    kantorovichConst κ₁ < kantorovichConst κ₂ := by
  have hk1_pos : 0 < κ₁ := lt_of_lt_of_le LinearOrderedField.zero_lt_one h1
  have hk2_pos : 0 < κ₂ := lt_trans hk1_pos hlt
  unfold kantorovichConst
  rw [div_lt_div_iff_of_pos (LinearOrderedField.mul_pos fourF_pos hk1_pos)
        (LinearOrderedField.mul_pos fourF_pos hk2_pos)]
  apply sub_pos.mp
  have hid :
      ((κ₂ + 1) * (κ₂ + 1)) * (fourF * κ₁) - ((κ₁ + 1) * (κ₁ + 1)) * (fourF * κ₂) =
      fourF * ((κ₂ - κ₁) * (κ₁ * κ₂ - 1)) := by
    have hexp (a b : F) :
        ((a + 1) * (a + 1)) * (fourF * b) =
        fourF * (b * (a * a) + twoF * (a * b) + b) := by
      calc
        ((a + 1) * (a + 1)) * (fourF * b)
          = fourF * (((a + 1) * (a + 1)) * b) := by
            rw [lofMulComm _ (fourF * b), lofMulAssoc fourF b _, lofMulComm b _]
        _ = fourF * ((a * a + twoF * a + 1) * b) := by
            congr 2
            rw [lofLeftDistrib, lofRightDistrib, lofRightDistrib,
                lofMulOne, lofOneMul, lofMulOne,
                lofAddAssoc (a * a) a (a + 1), ← lofAddAssoc a a 1,
                ← twoF_mul a, ← lofAddAssoc (a * a) (twoF * a) 1]
        _ = fourF * (b * (a * a) + twoF * (a * b) + b) := by
            congr 1
            rw [lofRightDistrib, lofRightDistrib, lofOneMul, lofMulComm (a * a) b,
                lofMulAssoc twoF a b]
    rw [hexp κ₂ κ₁, hexp κ₁ κ₂, ← mul_sub]
    congr 1
    rw [lofMulComm κ₁ κ₂]
    calc
      (κ₁ * (κ₂ * κ₂) + twoF * (κ₂ * κ₁) + κ₁) - (κ₂ * (κ₁ * κ₁) + twoF * (κ₂ * κ₁) + κ₂)
        = (κ₁ * (κ₂ * κ₂) + κ₁) - (κ₂ * (κ₁ * κ₁) + κ₂) := by
          let X := κ₁ * (κ₂ * κ₂)
          let Y := twoF * (κ₂ * κ₁)
          let Z := κ₁
          let U := κ₂ * (κ₁ * κ₁)
          let V := κ₂
          change (X + Y + Z) - (U + Y + V) = (X + Z) - (U + V)
          have hL : X + Y + Z = (X + Z) + Y := by
            rw [lofAddAssoc X Y Z, lofAddComm Y Z, ← lofAddAssoc X Z Y]
          have hR : U + Y + V = (U + V) + Y := by
            rw [lofAddAssoc U Y V, lofAddComm Y V, ← lofAddAssoc U V Y]
          rw [hL, hR, lofSubEqAddNeg ((X + Z) + Y) ((U + V) + Y),
              neg_add_rev, lofAddAssoc (X + Z) Y (-(U + V) + -Y),
              lofAddComm (-(U + V)) (-Y), ← lofAddAssoc Y (-Y) (-(U + V)),
              add_neg_cancel, lofZeroAdd, ← lofSubEqAddNeg]
      _ = (κ₁ * (κ₂ * κ₂) - κ₂ * (κ₁ * κ₁)) - (κ₂ - κ₁) := by
          calc
            (κ₁ * (κ₂ * κ₂) + κ₁) - (κ₂ * (κ₁ * κ₁) + κ₂)
              = κ₁ * (κ₂ * κ₂) + κ₁ + (-(κ₂ * (κ₁ * κ₁)) + -κ₂) := by
                rw [lofSubEqAddNeg, neg_add_rev]
            _ = (κ₁ * (κ₂ * κ₂) + -(κ₂ * (κ₁ * κ₁))) + (-κ₂ + κ₁) := by
                rw [lofAddAssoc (κ₁ * (κ₂ * κ₂)) κ₁ _,
                    ← lofAddAssoc κ₁ (-(κ₂ * (κ₁ * κ₁))) (-κ₂),
                    lofAddComm κ₁ (-(κ₂ * (κ₁ * κ₁))),
                    lofAddAssoc (-(κ₂ * (κ₁ * κ₁))) κ₁ (-κ₂),
                    lofAddComm κ₁ (-κ₂),
                    ← lofAddAssoc (κ₁ * (κ₂ * κ₂)) _ _]
            _ = (κ₁ * (κ₂ * κ₂) - κ₂ * (κ₁ * κ₁)) - (κ₂ - κ₁) := by
                rw [← lofSubEqAddNeg (κ₁ * (κ₂ * κ₂)) _,
                    lofSubEqAddNeg (_ - _) (κ₂ - κ₁),
                    lofSubEqAddNeg κ₂ κ₁, neg_add_rev, neg_neg]
      _ = (κ₂ - κ₁) * (κ₂ * κ₁) - (κ₂ - κ₁) * 1 := by
          congr 1
          · rw [sub_mul]
            congr 1
            · rw [← lofMulAssoc κ₁ κ₂ κ₂, lofMulComm κ₁ κ₂, lofMulAssoc κ₂ κ₁ κ₂,
                  lofMulComm κ₁ κ₂, ← lofMulAssoc κ₂ κ₂ κ₁]
            · rw [← lofMulAssoc κ₂ κ₁ κ₁, lofMulComm (κ₂ * κ₁) κ₁]
          · rw [lofMulOne]
      _ = (κ₂ - κ₁) * (κ₂ * κ₁ - 1) := (mul_sub (κ₂ - κ₁) (κ₂ * κ₁) 1).symm
  rw [hid]
  have hd1 : 0 < κ₂ - κ₁ := sub_pos.mpr hlt
  have hprod_gt : 1 < κ₁ * κ₂ := by
    have hle1 : (1 : F) ≤ κ₁ * 1 := by
      have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt (LinearOrderedField.zero_lt_one (F := F)))
      rw [lofMulOne 1] at hm
      exact hm
    exact lt_of_le_of_lt hle1 (mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 hlt) hk1_pos)
  have hd2 : 0 < κ₁ * κ₂ - 1 := sub_pos.mpr hprod_gt
  exact LinearOrderedField.mul_pos fourF_pos (LinearOrderedField.mul_pos hd1 hd2)

/-- `R` is strictly decreasing on `[1, ∞)`. -/
theorem reciprocalKantorovich_strictAnti_ge_one {κ₁ κ₂ : F}
    (h1 : 1 ≤ κ₁) (hlt : κ₁ < κ₂) :
    reciprocalKantorovichConst κ₂ < reciprocalKantorovichConst κ₁ := by
  have hk1_pos : 0 < κ₁ := lt_of_lt_of_le LinearOrderedField.zero_lt_one h1
  have hk2_pos : 0 < κ₂ := lt_trans hk1_pos hlt
  rw [reciprocalKantorovich_eq_inv hk2_pos, reciprocalKantorovich_eq_inv hk1_pos]
  have hK1_pos : 0 < kantorovichConst κ₁ :=
    lt_of_lt_of_le LinearOrderedField.zero_lt_one (one_le_kantorovichConst hk1_pos)
  exact inv_lt_inv_of_pos hK1_pos (kantorovichConst_strictMono_ge_one h1 hlt)

/-- **Refutation of Clause 2 under Reading C**:
    1. `R(3) = 3/4 ≠ 3/2 = HM(3, 1)` (value mismatch).
    2. `R` has **no minimum** on `[1, ∞)` (`¬ ∃ μ, IsMinValueOn R (κ ≥ 1) μ`).
    3. `0` is the greatest lower bound (infimum) of `{R(κ) : κ ≥ 1}`:
       `∀ κ ≥ 1, 0 < R(κ)` and `∀ ε > 0, ∃ κ ≥ 1, R(κ) < ε` (hence `inf = 0 ≠ HM`). -/
theorem readingC_refuted :
    (reciprocalKantorovichConst (threeF : F) = threeF / fourF ∧
      reciprocalKantorovichConst (threeF : F) ≠ harmonicMean (threeF : F) 1) ∧
    (¬ ∃ μ : F, IsMinValueOn reciprocalKantorovichConst (fun κ => 1 ≤ κ) μ) ∧
    ((∀ κ : F, 1 ≤ κ → 0 < reciprocalKantorovichConst κ) ∧
     (∀ ε : F, 0 < ε → ∃ κ : F, 1 ≤ κ ∧ reciprocalKantorovichConst κ < ε)) := by
  have hR3 : reciprocalKantorovichConst (threeF : F) = threeF / fourF := by
    rw [reciprocalKantorovich_eq_inv threeF_pos]
    rcases counterexample_m1_M3 (F := F) with ⟨hk3, _, _, _⟩
    rw [hk3, inv_div fourF_ne_zero threeF_ne_zero]
  have hR3_ne : reciprocalKantorovichConst (threeF : F) ≠ harmonicMean (threeF : F) 1 := by
    rcases counterexample_m1_M3 (F := F) with ⟨_, hhm3, _, _⟩
    rw [hR3, hhm3]
    intro heq
    have hm := (div_eq_div_iff fourF_ne_zero twoF_ne_zero).mp heq
    have hlt : (threeF : F) * twoF < threeF * fourF :=
      mul_lt_mul_of_pos_left (twoF_lt_fourF (F := F)) threeF_pos
    exact ne_of_lt hlt hm
  have hno_min : ¬ ∃ μ : F, IsMinValueOn reciprocalKantorovichConst (fun κ => 1 ≤ κ) μ := by
    rintro ⟨μ, ⟨κ₀, hκ₀, hval⟩, hle⟩
    let κ₁ := κ₀ + 1
    have hlt : κ₀ < κ₁ := by
      change κ₀ < κ₀ + 1
      have ht := add_lt_add_left LinearOrderedField.zero_lt_one κ₀
      rw [lofAddZero] at ht
      exact ht
    have h1 : 1 ≤ κ₁ := LinearOrderedField.le_trans hκ₀ (le_of_lt hlt)
    have hdec := reciprocalKantorovich_strictAnti_ge_one hκ₀ hlt
    rw [hval] at hdec
    exact not_le_of_lt hdec (hle κ₁ h1)
  have hpos : ∀ κ : F, 1 ≤ κ → 0 < reciprocalKantorovichConst κ := by
    intro κ hκ
    have hk_pos : 0 < κ := lt_of_lt_of_le LinearOrderedField.zero_lt_one hκ
    unfold reciprocalKantorovichConst
    have hp1 : 0 < κ + 1 := by
      have ht := add_lt_add hk_pos LinearOrderedField.zero_lt_one
      rw [lofAddZero] at ht
      exact ht
    exact div_pos (LinearOrderedField.mul_pos fourF_pos hk_pos)
      (LinearOrderedField.mul_pos hp1 hp1)
  have hinf : ∀ ε : F, 0 < ε → ∃ κ : F, 1 ≤ κ ∧ reciprocalKantorovichConst κ < ε := by
    intro ε hε
    let κ := 1 + fourF / ε
    have h4ε : 0 < fourF / ε := div_pos fourF_pos hε
    have hκ_gt1 : 1 < κ := by
      change 1 < 1 + fourF / ε
      have ht := add_lt_add_left h4ε 1
      rw [lofAddZero] at ht
      exact ht
    have hκ_pos : 0 < κ := lt_trans LinearOrderedField.zero_lt_one hκ_gt1
    refine ⟨κ, le_of_lt hκ_gt1, ?_⟩
    -- Note (κ + 1)^2 > κ^2 for κ > 0, so R(κ) = 4κ / (κ + 1)^2 < 4 / κ < ε
    have hbound1 : reciprocalKantorovichConst κ < fourF / κ := by
      unfold reciprocalKantorovichConst
      have hp1 : 0 < κ + 1 := by
        have ht := add_lt_add hκ_pos LinearOrderedField.zero_lt_one
        rw [lofAddZero] at ht
        exact ht
      rw [div_lt_div_iff_of_pos (LinearOrderedField.mul_pos hp1 hp1) hκ_pos]
      have hsq_gt : κ * κ < (κ + 1) * (κ + 1) := by
        have hlt1 : κ < κ + 1 := by
          have ht := add_lt_add_left LinearOrderedField.zero_lt_one κ
          rw [lofAddZero] at ht
          exact ht
        exact lt_trans (mul_lt_mul_of_pos_left hlt1 hκ_pos)
                       (mul_lt_mul_of_pos_right hlt1 hp1)
      rw [lofMulAssoc fourF κ κ]
      exact mul_lt_mul_of_pos_left hsq_gt fourF_pos
    have hbound2 : fourF / κ < ε := by
      rw [div_lt_iff_of_pos hκ_pos]
      have hκ_gt : fourF / ε < κ := by
        change fourF / ε < 1 + fourF / ε
        rw [lofAddComm 1 (fourF / ε)]
        have ht := add_lt_add_left LinearOrderedField.zero_lt_one (fourF / ε)
        rw [lofAddZero] at ht
        exact ht
      have hm := mul_lt_mul_of_pos_left hκ_gt hε
      rw [lofMulComm ε (fourF / ε), div_mul_cancel fourF (ne_of_gt hε)] at hm
      exact hm
    exact lt_trans hbound1 hbound2
  exact ⟨⟨hR3, hR3_ne⟩, hno_min, ⟨hpos, hinf⟩⟩

/-!
### Reading D: Rayleigh Quotients at the Global Minimum and at the Kantorovich Extremizer
For `0 < m < M`:
  1. `m < HM(M, m) < AM(M, m)`, so neither the minimum Rayleigh quotient `m` nor the
     Kantorovich-extremizer Rayleigh quotient `AM(M, m)` equals `HM(M, m)`.
  2. At `(m, M) = (1, 3)`, the inverse Rayleigh quotient `⟨A⁻¹x*, x*⟩ / ‖x*‖^2 = HM(3,1)⁻¹ = 2/3`
     also differs from `HM(3, 1) = 3/2`.
-/

theorem m_lt_harmonicMean_lt_arithmeticMean {M m : F} (hm : 0 < m) (hlt : m < M) :
    m < harmonicMean M m ∧ harmonicMean M m < arithmeticMean M m := by
  have hM : 0 < M := lt_trans hm hlt
  have hMm : 0 < M + m := by
    have ht := add_lt_add hM hm
    rw [lofAddZero] at ht
    exact ht
  constructor
  · unfold harmonicMean
    rw [lt_div_iff_of_pos hMm]
    apply sub_pos.mp
    have hid : twoF * M * m - m * (M + m) = m * (M - m) := by
      calc
        twoF * M * m - m * (M + m)
          = (M + M) * m - (m * M + m * m) := by
            rw [twoF_mul M, lofLeftDistrib]
        _ = (M * m + M * m) - (M * m + m * m) := by
            rw [lofRightDistrib, lofMulComm m M]
        _ = M * m - m * m := by
            rw [lofSubEqAddNeg, neg_add_rev, lofAddComm (M * m) (M * m),
                lofAddAssoc, ← lofAddAssoc (M * m) (-(M * m)) _,
                add_neg_cancel, lofZeroAdd, ← lofSubEqAddNeg]
        _ = m * (M - m) := by
            rw [mul_sub, lofMulComm m M]
    rw [hid]
    exact LinearOrderedField.mul_pos hm (sub_pos.mpr hlt)
  · unfold harmonicMean arithmeticMean
    rw [div_lt_div_iff_of_pos hMm twoF_pos]
    apply sub_pos.mp
    have hid : (M + m) * (M + m) - (twoF * M * m) * twoF = (M - m) * (M - m) := by
      calc
        (M + m) * (M + m) - (twoF * M * m) * twoF
          = (M * M + twoF * (M * m) + m * m) - fourF * (M * m) := by
            congr 1
            · rw [lofLeftDistrib, lofRightDistrib, lofRightDistrib, lofMulComm m M,
                  lofAddAssoc (M * M) (M * m) (M * m + m * m),
                  ← lofAddAssoc (M * m) (M * m) (m * m),
                  ← twoF_mul (M * m),
                  ← lofAddAssoc (M * M) (twoF * (M * m)) (m * m)]
            · rw [lofMulComm (twoF * M * m) twoF, lofMulAssoc twoF M m,
                  ← lofMulAssoc twoF twoF (M * m), ← fourF_eq_two_mul_two]
        _ = M * M - twoF * (M * m) + m * m := by
            rw [fourF_eq_two_mul_two, lofMulAssoc twoF twoF (M * m),
                twoF_mul (twoF * (M * m)),
                lofSubEqAddNeg (_ + m * m) _,
                lofAddAssoc (M * M + twoF * (M * m)) (m * m) _,
                lofAddComm (m * m) _, ← lofAddAssoc]
            congr 1
            rw [neg_add_rev, lofAddAssoc (M * M) (twoF * (M * m)) _,
                ← lofAddAssoc (twoF * (M * m)) _ _, add_neg_cancel, lofZeroAdd,
                ← lofSubEqAddNeg]
        _ = (M - m) * (M - m) := by
            calc
              M * M - twoF * (M * m) + m * m
                = M * M - (M * m + M * m) + m * m := by rw [twoF_mul]
              _ = (M * M - M * m) - (M * m - m * m) := by
                  rw [← sub_sub, sub_sub_eq_add_sub (M * M - M * m) (M * m) (m * m),
                      lofSubEqAddNeg (M * M - M * m + m * m) (M * m),
                      lofAddAssoc (M * M - M * m) (m * m) (-(M * m)),
                      lofAddComm (m * m) (-(M * m)), ← lofAddAssoc, ← lofSubEqAddNeg]
              _ = M * (M - m) - m * (M - m) := by
                  rw [mul_sub, mul_sub, lofMulComm m M]
              _ = (M - m) * (M - m) := (sub_mul M m (M - m)).symm
    rw [hid]
    exact sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hlt))

/-- **Refutation of Clause 2 under Reading D**:
    1. For every `n ≥ 1`, positive spectrum attaining `m` at `j` with `0 < m < M` and `m ≤ λ_i`,
       the global minimum Rayleigh quotient over `x ≠ 0` is `m < HM(M, m)`, hence `≠ HM(M, m)`.
    2. At `(m, M) = (1, 3)`, `(HM(3, 1))⁻¹ = 2/3 ≠ 3/2 = HM(3, 1)`. -/
theorem readingD_refuted (n : Nat) (lam : Fin n → F) {M m : F} (j : Fin n)
    (hm_pos : 0 < m) (hlt : m < M) (hj : lam j = m) (hm_le : ∀ i, m ≤ lam i) :
    (quadFormDiag n lam (basisVec n j) / normSq n (basisVec n j) = m ∧
     (∀ x : Fin n → F, (∃ i, x i ≠ 0) → m ≤ quadFormDiag n lam x / normSq n x) ∧
     m ≠ harmonicMean M m ∧
     arithmeticMean M m ≠ harmonicMean M m) ∧
    (harmonicMean (threeF : F) 1)⁻¹ ≠ harmonicMean (threeF : F) 1 := by
  have hval : quadFormDiag n lam (basisVec n j) / normSq n (basisVec n j) = m := by
    rw [quadFormDiag_basisVec, normSq_basisVec, div_one, hj]
  have hall : ∀ x : Fin n → F, (∃ i, x i ≠ 0) → m ≤ quadFormDiag n lam x / normSq n x := by
    intro x hx
    let w := fun i => (x i * x i) / normSq n x
    have hn_pos : 0 < normSq n x := normSq_pos_of_ne_zero n hx
    have hw_nonneg : ∀ i, 0 ≤ w i := fun i => div_nonneg (sq_nonneg (x i)) (le_of_lt hn_pos)
    have hw_sum : finSum n w = 1 := by
      change finSum n (fun i => (x i * x i) / normSq n x) = 1
      rw [finSum_div_const]
      exact div_self (ne_of_gt hn_pos)
    have hS : finSum n (fun i => w i * lam i) = quadFormDiag n lam x / normSq n x := by
      have hc : finSum n (fun i => w i * lam i) =
          finSum n (fun i => (lam i * (x i * x i)) / normSq n x) := by
        apply finSum_congr
        intro i
        change ((x i * x i) / normSq n x) * lam i = _
        rw [div_mul_eq_mul_div, lofMulComm (x i * x i) (lam i)]
      rw [hc, finSum_div_const]
      rfl
    rw [← hS]
    exact weighted_sum_ge_min n w lam hw_nonneg hw_sum hm_le
  rcases m_lt_harmonicMean_lt_arithmeticMean hm_pos hlt with ⟨hm_lt, ham_gt⟩
  have hinv_ne : (harmonicMean (threeF : F) 1)⁻¹ ≠ harmonicMean (threeF : F) 1 := by
    rcases counterexample_m1_M3 (F := F) with ⟨_, hhm3, _, _⟩
    rw [hhm3, inv_div threeF_ne_zero twoF_ne_zero]
    intro heq
    have hm := (div_eq_div_iff threeF_ne_zero twoF_ne_zero).mp heq
    have hlt23 : (twoF : F) < threeF := twoF_lt_threeF (F := F)
    have hsq : (twoF : F) * twoF < threeF * threeF :=
      lt_trans (mul_lt_mul_of_pos_left hlt23 twoF_pos)
               (mul_lt_mul_of_pos_right hlt23 threeF_pos)
    exact ne_of_lt hsq hm
  exact ⟨⟨hval, hall, ne_of_lt hm_lt, ne_of_gt ham_gt⟩, hinv_ne⟩

end Clause2Refutations

end Conjecture00000007166
