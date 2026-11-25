/-
  Conjecture 00000007163 — Core Lean 4.19.0 Formalization
  File: Conjecture00000007163/PositiveBounds.lean

  Positive boundary theorems (explaining what IS true and proving non-vacuity):
  1. `pairwise_weight_contraction`: Deutsch–Zenger convex-combination contraction
     lemma over `GaussInt` (ℤ[i]), completely free of division or square roots.
  2. `constantRowSum_gap_ge_doeblin`: Markov–Doeblin spectral gap bound for
     nonnegative constant-row-sum (scaled row-stochastic) matrices (`n ≥ 2`).
  3. `strictlyPositive_gap_gt_posModulus`: Universal strict separation over ALL
     dimensions `n ≥ 2` and ALL strictly positive matrices `A > 0`.
  4. `twoByTwo_gap_ge_two_posModulus`: Sharp `2 × 2` lower bound `2 · m ≤ λ₁ - |λ₂|`.
-/

import Conjecture00000007163.PFMatrix

namespace Conjecture00000007163

/-! ## 1. Maximum Pairwise Squared Distance on `CVec (m + 1)` -/

def maxPairDiffSq {m : Nat} (y : CVec (m + 1)) : Int :=
  finMax (fun i => finMax (fun k => GaussInt.normSq (y i - y k)))

theorem normSq_diff_le_maxPairDiffSq {m : Nat} (y : CVec (m + 1)) (i k : Fin (m + 1)) :
    GaussInt.normSq (y i - y k) ≤ maxPairDiffSq y := by
  unfold maxPairDiffSq
  exact Int.le_trans
    (le_finMax (fun c => GaussInt.normSq (y i - y c)) k)
    (le_finMax (fun r => finMax (fun c => GaussInt.normSq (y r - y c))) i)

theorem maxPairDiffSq_attained {m : Nat} (y : CVec (m + 1)) :
    ∃ i k : Fin (m + 1), maxPairDiffSq y = GaussInt.normSq (y i - y k) := by
  unfold maxPairDiffSq
  rcases finMax_mem (fun i => finMax (fun k => GaussInt.normSq (y i - y k))) with ⟨i₀, hi₀⟩
  rcases finMax_mem (fun k => GaussInt.normSq (y i₀ - y k)) with ⟨k₀, hk₀⟩
  exact ⟨i₀, k₀, Eq.trans hi₀ hk₀⟩

theorem maxPairDiffSq_pos_of_nonconst {m : Nat} {y : CVec (m + 1)}
    (h : ∃ a b : Fin (m + 1), y a ≠ y b) :
    0 < maxPairDiffSq y := by
  rcases h with ⟨a, b, hab⟩
  have hpos : 0 < GaussInt.normSq (y a - y b) :=
    GaussInt.normSq_pos_of_ne_zero (GaussInt.sub_ne_zero_of_ne hab)
  have hle := normSq_diff_le_maxPairDiffSq y a b
  omega

theorem exists_ne_of_not_forall_eq {k : Nat} (f : Fin k → GaussInt) (z : GaussInt)
    (hnot : ¬ ∀ j : Fin k, f j = z) :
    ∃ j : Fin k, f j ≠ z := by
  induction k with
  | zero =>
    exfalso
    exact hnot (fun j => Fin.elim0 j)
  | succ k ih =>
    by_cases hlast : f ⟨k, Nat.lt_succ_self k⟩ = z
    · have hprev : ¬ ∀ j : Fin k, f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = z := by
        intro hall
        apply hnot
        intro j
        by_cases hj : j.val = k
        · have hjeq : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hj
          rw [hjeq]
          exact hlast
        · exact hall ⟨j.val, by omega⟩
      rcases ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hprev with ⟨j₀, hj₀⟩
      exact ⟨⟨j₀.val, Nat.lt_succ_of_lt j₀.isLt⟩, hj₀⟩
    · exact ⟨⟨k, Nat.lt_succ_self k⟩, hlast⟩

/-! ## 2. Deutsch–Zenger Convex-Combination Contraction over `GaussInt` -/

def intMin (a b : Int) : Int := if a ≤ b then a else b

theorem intMin_le_left (a b : Int) : intMin a b ≤ a := by
  unfold intMin; split <;> omega

theorem intMin_le_right (a b : Int) : intMin a b ≤ b := by
  unfold intMin; split <;> omega

theorem le_intMin {c a b : Int} (ha : c ≤ a) (hb : c ≤ b) : c ≤ intMin a b := by
  unfold intMin; split <;> omega

theorem intMin_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ intMin a b :=
  le_intMin ha hb

/-- Core contraction lemma: if `P⁺, P⁻` have equal sum `M`, `W = min(P⁺, P⁻)`,
    and `T = M - ∑ W`, then `normSq (∑ (P⁺ - P⁻) y_j) ≤ T² · maxPairDiffSq y`. -/
theorem pairwise_weight_contraction {m : Nat}
    (Ppos Pneg : Fin (m + 1) → Int) (M : Int) (y : CVec (m + 1))
    (hsum_pos : finSum (m + 1) Ppos = M)
    (hsum_neg : finSum (m + 1) Pneg = M) :
    let W : Fin (m + 1) → Int := fun j => intMin (Ppos j) (Pneg j)
    let T : Int := M - finSum (m + 1) W
    0 ≤ T ∧
      GaussInt.normSq (cFinSum (m + 1) (fun j => GaussInt.scale (Ppos j - Pneg j) (y j))) ≤
        T * T * maxPairDiffSq y := by
  intro W T
  let Rpos : Fin (m + 1) → Int := fun j => Ppos j - W j
  let Rneg : Fin (m + 1) → Int := fun j => Pneg j - W j
  have hRpos_nn : ∀ j, 0 ≤ Rpos j := by
    intro j; dsimp [Rpos, W]; have := intMin_le_left (Ppos j) (Pneg j); omega
  have hRneg_nn : ∀ j, 0 ≤ Rneg j := by
    intro j; dsimp [Rneg, W]; have := intMin_le_right (Ppos j) (Pneg j); omega
  have hsum_Rpos : finSum (m + 1) Rpos = T := by
    dsimp [Rpos, T]; rw [finSum_sub, hsum_pos]
  have hsum_Rneg : finSum (m + 1) Rneg = T := by
    dsimp [Rneg, T]; rw [finSum_sub, hsum_neg]
  have hT_nn : 0 ≤ T := by
    rw [← hsum_Rpos]; exact finSum_nonneg hRpos_nn
  refine ⟨hT_nn, ?_⟩
  let D := maxPairDiffSq y
  have hD_nn : 0 ≤ D := by
    have h0 := normSq_diff_le_maxPairDiffSq y ⟨0, Nat.zero_lt_succ m⟩ ⟨0, Nat.zero_lt_succ m⟩
    have h1 := GaussInt.normSq_nonneg (y ⟨0, Nat.zero_lt_succ m⟩ - y ⟨0, Nat.zero_lt_succ m⟩)
    dsimp [D]; omega
  let Δ := cFinSum (m + 1) (fun j => GaussInt.scale (Ppos j - Pneg j) (y j))
  have hΔ_eq : Δ = cFinSum (m + 1) (fun j => GaussInt.scale (Rpos j - Rneg j) (y j)) := by
    apply cFinSum_congr
    intro j
    have hp : Ppos j - Pneg j = Rpos j - Rneg j := by dsimp [Rpos, Rneg]; omega
    rw [hp]
  by_cases hT0 : T = 0
  · have hRp0 : ∀ j, Rpos j = 0 :=
      finSum_eq_zero_of_nonneg hRpos_nn (by rw [hsum_Rpos, hT0])
    have hRn0 : ∀ j, Rneg j = 0 :=
      finSum_eq_zero_of_nonneg hRneg_nn (by rw [hsum_Rneg, hT0])
    have hΔ_zero : Δ = GaussInt.zero := by
      rw [hΔ_eq]
      have hc : ∀ j : Fin (m + 1), GaussInt.scale (Rpos j - Rneg j) (y j) = GaussInt.zero := by
        intro j
        rw [hRp0 j, hRn0 j]
        apply GaussInt.ext <;> simp [GaussInt.scale, GaussInt.zero]
      rw [cFinSum_congr hc]
      clear hΔ_eq Δ hc hRp0 hRn0 hT0 hT_nn hsum_Rneg hsum_Rpos hRneg_nn hRpos_nn Rpos Rneg T W hD_nn D
      induction (m + 1) with
      | zero => rfl
      | succ k ih =>
        simp only [cFinSum]
        rw [ih]
        apply GaussInt.ext <;> rfl
    change GaussInt.normSq Δ ≤ T * T * D
    rw [hΔ_zero, hT0]
    simp [GaussInt.normSq, GaussInt.zero]
  · have hT_pos : 0 < T := by omega
    have hTΔ : GaussInt.scale T Δ =
        cFinSum (m + 1) (fun j =>
          GaussInt.scale (Rpos j)
            (cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y j - y l)))) := by
      rw [hΔ_eq]
      have hsplit : cFinSum (m + 1) (fun j => GaussInt.scale (Rpos j - Rneg j) (y j)) =
          cFinSum (m + 1) (fun j => GaussInt.scale (Rpos j) (y j)) -
          cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y l)) := by
        have hc : ∀ j, GaussInt.scale (Rpos j - Rneg j) (y j) =
            GaussInt.scale (Rpos j) (y j) - GaussInt.scale (Rneg j) (y j) :=
          fun j => GaussInt.sub_scale (Rpos j) (Rneg j) (y j)
        rw [cFinSum_congr hc, cFinSum_sub]
      rw [hsplit, GaussInt.scale_sub]
      have hleft : GaussInt.scale T (cFinSum (m + 1) (fun j => GaussInt.scale (Rpos j) (y j))) =
          cFinSum (m + 1) (fun j =>
            GaussInt.scale (Rpos j) (cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y j)))) := by
        rw [← cFinSum_scale]
        apply cFinSum_congr
        intro j
        rw [cFinSum_scale_vec, hsum_Rneg, GaussInt.scale_scale, GaussInt.scale_scale,
            Int.mul_comm T (Rpos j)]
      have hright : GaussInt.scale T (cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y l))) =
          cFinSum (m + 1) (fun j =>
            GaussInt.scale (Rpos j) (cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y l)))) := by
        let V := cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y l))
        change GaussInt.scale T V = cFinSum (m + 1) (fun j => GaussInt.scale (Rpos j) V)
        rw [cFinSum_scale_vec, hsum_Rpos]
      rw [hleft, hright, ← cFinSum_sub]
      apply cFinSum_congr
      intro j
      rw [← GaussInt.scale_sub, ← cFinSum_sub]
      apply congrArg (GaussInt.scale (Rpos j))
      apply cFinSum_congr
      intro l
      rw [← GaussInt.scale_sub]
    have hbnd_outer : GaussInt.normSq (GaussInt.scale T Δ) ≤ (T * T) * (T * T * D) := by
      rw [hTΔ]
      have hb := normSq_cFinSum_le (m + 1)
        (fun j => GaussInt.scale (Rpos j)
          (cFinSum (m + 1) (fun l => GaussInt.scale (Rneg l) (y j - y l))))
        Rpos (T * T * D) hRpos_nn
        (Int.mul_nonneg (int_sq_nonneg T) hD_nn)
        (by
          intro j
          rw [GaussInt.normSq_scale]
          apply Int.mul_le_mul (Int.le_refl _) _ (GaussInt.normSq_nonneg _) (int_sq_nonneg _)
          have hinner := normSq_weighted_sum_le (m + 1) Rneg (fun l => y j - y l) D
            hRneg_nn hD_nn (fun l => normSq_diff_le_maxPairDiffSq y j l)
          rw [hsum_Rneg] at hinner
          exact hinner)
      rw [hsum_Rpos] at hb
      exact hb
    rw [GaussInt.normSq_scale] at hbnd_outer
    have hTT_pos : 0 < T * T := Int.mul_pos hT_pos hT_pos
    have hmul_comm1 : (T * T) * GaussInt.normSq Δ = GaussInt.normSq Δ * (T * T) :=
      Int.mul_comm _ _
    have hmul_comm2 : (T * T) * (T * T * D) = (T * T * D) * (T * T) :=
      Int.mul_comm _ _
    rw [hmul_comm1, hmul_comm2] at hbnd_outer
    exact Int.le_of_mul_le_mul_right hbnd_outer hTT_pos

/-! ## 3. Markov–Doeblin Spectral Gap Theorem for Constant-Row-Sum Matrices -/

theorem nonconst_of_constantRowSum_eigenpair {m : Nat} {A : IMat (m + 1)} {R : Int}
    {lam : GaussInt} {v : CVec (m + 1)}
    (hrow : HasConstantRowSum A R)
    (heig : IsComplexEigenpair A lam v)
    (hne : lam ≠ GaussInt.ofInt R) :
    ∃ a b : Fin (m + 1), v a ≠ v b := by
  rcases heig with ⟨⟨i₀, hvi₀⟩, hAv⟩
  by_cases hconst : ∀ j : Fin (m + 1), v j = v i₀
  · exfalso
    have hrow_i₀ : (cMatVec A v) i₀ = GaussInt.scale R (v i₀) := by
      unfold cMatVec
      have hc : ∀ j, GaussInt.scale (A i₀ j) (v j) = GaussInt.scale (A i₀ j) (v i₀) :=
        fun j => by rw [hconst j]
      rw [cFinSum_congr hc, cFinSum_scale_vec]
      change GaussInt.scale (rowSum A i₀) (v i₀) = GaussInt.scale R (v i₀)
      rw [hrow i₀]
    have heig_i₀ : (cMatVec A v) i₀ = lam * v i₀ := congrFun hAv i₀
    rw [hrow_i₀, ← GaussInt.ofInt_mul R (v i₀)] at heig_i₀
    have hdiff : (lam - GaussInt.ofInt R) * v i₀ = GaussInt.zero := by
      rw [GaussInt.sub_mul_left, ← heig_i₀, GaussInt.sub_self]
    have hnorm0 : GaussInt.normSq (lam - GaussInt.ofInt R) * GaussInt.normSq (v i₀) = 0 := by
      rw [← GaussInt.normSq_mul, hdiff]
      rfl
    have hp1 : 0 < GaussInt.normSq (lam - GaussInt.ofInt R) :=
      GaussInt.normSq_pos_of_ne_zero (GaussInt.sub_ne_zero_of_ne hne)
    have hp2 : 0 < GaussInt.normSq (v i₀) :=
      GaussInt.normSq_pos_of_ne_zero hvi₀
    have hprod_pos : 0 < GaussInt.normSq (lam - GaussInt.ofInt R) * GaussInt.normSq (v i₀) :=
      Int.mul_pos hp1 hp2
    omega
  · rcases exists_ne_of_not_forall_eq v (v i₀) hconst with ⟨j, hj⟩
    exact ⟨j, i₀, hj⟩

/-- **Markov–Doeblin Spectral Gap Bound (`n ≥ 2`):**
    For any nonnegative `(m+2) × (m+2)` matrix `A` with constant row sum `R`,
    every complex eigenvalue `lam ≠ R` satisfies
      `0 ≤ R - doeblinModulus A` and `normSq lam ≤ (R - doeblinModulus A)²`. -/
theorem constantRowSum_gap_ge_doeblin {m : Nat} (A : IMat (m + 2)) (R : Int)
    (_hnn : IsNonneg A) (hrow : HasConstantRowSum A R)
    (lam : GaussInt) (v : CVec (m + 2))
    (heig : IsComplexEigenpair A lam v) (hne : lam ≠ GaussInt.ofInt R) :
    0 ≤ R - doeblinModulus A ∧
      GaussInt.normSq lam ≤ (R - doeblinModulus A) * (R - doeblinModulus A) := by
  have hnonconst := nonconst_of_constantRowSum_eigenpair hrow heig hne
  have hD_pos : 0 < maxPairDiffSq v := maxPairDiffSq_pos_of_nonconst hnonconst
  rcases maxPairDiffSq_attained v with ⟨i, k, hD_eq⟩
  have hpair_contr := pairwise_weight_contraction (m := m + 1)
    (fun j => A i j) (fun j => A k j) R v (hrow i) (hrow k)
  let W : Fin (m + 2) → Int := fun j => intMin (A i j) (A k j)
  let T : Int := R - finSum (m + 2) W
  have hT_nn : 0 ≤ T := hpair_contr.1
  have hcontr :
      GaussInt.normSq (cFinSum (m + 2) (fun j => GaussInt.scale (A i j - A k j) (v j))) ≤
        T * T * maxPairDiffSq v := hpair_contr.2
  have hΔ_eig : cFinSum (m + 2) (fun j => GaussInt.scale (A i j - A k j) (v j)) =
      lam * (v i - v k) := by
    have hc : ∀ j, GaussInt.scale (A i j - A k j) (v j) =
        GaussInt.scale (A i j) (v j) - GaussInt.scale (A k j) (v j) :=
      fun j => GaussInt.sub_scale (A i j) (A k j) (v j)
    rw [cFinSum_congr hc, cFinSum_sub]
    change (cMatVec A v) i - (cMatVec A v) k = lam * (v i - v k)
    rw [congrFun heig.2 i, congrFun heig.2 k, ← GaussInt.mul_sub_right]
  rw [hΔ_eig, GaussInt.normSq_mul, ← hD_eq] at hcontr
  have hlam_le_T : GaussInt.normSq lam ≤ T * T :=
    Int.le_of_mul_le_mul_right hcontr hD_pos
  have hdoeblin_le_W : doeblinModulus A ≤ finSum (m + 2) W := by
    unfold doeblinModulus
    apply finSum_le
    intro j
    exact le_intMin (finMin_le (fun r => A r j) i) (finMin_le (fun r => A r j) k)
  have hT_def : T = R - finSum (m + 2) W := rfl
  have hR_sub_doeblin : 0 ≤ R - doeblinModulus A := by omega
  have hT_le : T ≤ R - doeblinModulus A := by omega
  exact ⟨hR_sub_doeblin, Int.le_trans hlam_le_T (int_sq_le_sq hT_nn hT_le)⟩

/-! ## 4. Universal Strict Positivity-Modulus Separation (`n ≥ 2`, `A > 0`) -/

def prodExcept {n : Nat} (u : Fin n → Int) (j : Fin n) : Int :=
  finProd n (fun t => if t = j then 1 else u t)

theorem mul_prodExcept {n : Nat} (u : Fin n → Int) (j : Fin n) :
    u j * prodExcept u j = finProd n u := by
  unfold prodExcept
  induction n with
  | zero => exact Fin.elim0 j
  | succ m ihm =>
    simp only [finProd]
    by_cases hj : j.val = m
    · have hjeq : j = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hj
      subst hjeq
      have hc : ∀ t : Fin m,
          (if (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩
           then (1 : Int) else u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) =
          u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ := by
        intro t
        have hne : (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ : Fin (m + 1)) ≠ ⟨m, Nat.lt_succ_self m⟩ :=
          fun heq => Nat.ne_of_lt t.isLt (Fin.mk.inj heq)
        simp [hne]
      rw [finProd_congr hc]
      simp [Int.mul_comm]
    · have hjlt : j.val < m := by omega
      have hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ≠ j := by
        intro heq
        have hval : m = j.val := congrArg Fin.val heq
        omega
      have hc : ∀ t : Fin m,
          (if (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ : Fin (m + 1)) = j
           then (1 : Int) else u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) =
          (if t = ⟨j.val, hjlt⟩ then 1 else u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) := by
        intro t
        by_cases ht : t.val = j.val
        · have h1 : (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ : Fin (m + 1)) = j := Fin.ext ht
          have h2 : t = ⟨j.val, hjlt⟩ := Fin.ext ht
          simp [h1, h2]
        · have h1 : (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ : Fin (m + 1)) ≠ j :=
            fun heq => ht (congrArg Fin.val heq)
          have h2 : t ≠ ⟨j.val, hjlt⟩ :=
            fun heq => ht (congrArg Fin.val heq)
          simp [h1, h2]
      rw [finProd_congr hc]
      simp only [hlast, ↓reduceIte]
      have hprev := ihm (fun t => u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) ⟨j.val, hjlt⟩
      have huj : u ⟨j.val, Nat.lt_succ_of_lt hjlt⟩ = u j := congrArg u (Fin.ext rfl)
      rw [huj] at hprev
      rw [← Int.mul_assoc, hprev]

theorem prodExcept_pos {n : Nat} {u : Fin n → Int} (hu : ∀ i, 0 < u i) (j : Fin n) :
    0 < prodExcept u j := by
  unfold prodExcept
  apply finProd_pos
  intro t
  by_cases h : t = j
  · simp [h]
  · simp [h]; exact hu t

/-- **Universal Strict Positivity-Modulus Separation (`n ≥ 2`):**
    For EVERY dimension `n = m + 2 ≥ 2` and EVERY strictly positive matrix `A`
    with positive right Perron eigenpair `(A, ρ, u)` (`u > 0`, `ρ > 0`),
    every complex eigenvalue `lam ≠ ρ` satisfies:
      `posModulusMin A < ρ`  and  `normSq lam < (ρ - posModulusMin A)²`. -/
theorem strictlyPositive_gap_gt_posModulus {m : Nat} (A : IMat (m + 2))
    (hposA : IsStrictlyPositive A)
    (rho : Int) (u : IVec (m + 2))
    (_hrho : 0 < rho) (hu : ∀ i, 0 < u i)
    (hPerron : matVec A u = fun i => rho * u i)
    (lam : GaussInt) (x : CVec (m + 2))
    (heig : IsComplexEigenpair A lam x)
    (hne : lam ≠ GaussInt.ofInt rho) :
    posModulusMin A < rho ∧
      GaussInt.normSq lam < (rho - posModulusMin A) * (rho - posModulusMin A) := by
  let pmin := posModulusMin A
  have hpmin_pos : 0 < pmin := by
    rcases finMin_mem (fun i => finMin (fun j => A i j)) with ⟨i₀, hi₀⟩
    rcases finMin_mem (fun j => A i₀ j) with ⟨j₀, hj₀⟩
    dsimp [pmin, posModulusMin]
    rw [hi₀, hj₀]
    exact hposA i₀ j₀
  let U := finProd (m + 2) u
  let y : CVec (m + 2) := fun j => GaussInt.scale (prodExcept u j) (x j)
  have huy : ∀ j, GaussInt.scale (u j) (y j) = GaussInt.scale U (x j) := by
    intro j
    dsimp [y]
    rw [GaussInt.scale_scale, mul_prodExcept u j]
  -- 1. Show `y` is non-constant using Perron similarity row sum
  have hy_nonconst : ∃ a b : Fin (m + 2), y a ≠ y b := by
    rcases heig with ⟨⟨i₀, hxi₀⟩, hAx⟩
    have hyi₀ : y i₀ ≠ GaussInt.zero := by
      intro h0
      have hsc : (prodExcept u i₀ * prodExcept u i₀) * GaussInt.normSq (x i₀) = 0 := by
        rw [← GaussInt.normSq_scale]
        change GaussInt.normSq (y i₀) = 0
        rw [h0]
        rfl
      have hp1 : 0 < prodExcept u i₀ * prodExcept u i₀ :=
        int_sq_pos_of_ne_zero (by have := prodExcept_pos hu i₀; omega)
      have hp2 : 0 < GaussInt.normSq (x i₀) := GaussInt.normSq_pos_of_ne_zero hxi₀
      have hprod_pos : 0 < (prodExcept u i₀ * prodExcept u i₀) * GaussInt.normSq (x i₀) :=
        Int.mul_pos hp1 hp2
      omega
    by_cases hconst : ∀ j : Fin (m + 2), y j = y i₀
    · exfalso
      have hrow1 : GaussInt.scale U ((cMatVec A x) i₀) =
          GaussInt.scale (rho * u i₀) (y i₀) := by
        unfold cMatVec
        rw [← cFinSum_scale]
        have hc : ∀ j, GaussInt.scale U (GaussInt.scale (A i₀ j) (x j)) =
            GaussInt.scale (A i₀ j * u j) (y i₀) := by
          intro j
          rw [GaussInt.scale_scale, Int.mul_comm U (A i₀ j), ← GaussInt.scale_scale,
              ← huy j, hconst j, GaussInt.scale_scale]
        rw [cFinSum_congr hc, cFinSum_scale_vec]
        have hAu : finSum (m + 2) (fun j => A i₀ j * u j) = rho * u i₀ := congrFun hPerron i₀
        rw [hAu]
      have hrow2 : GaussInt.scale U ((cMatVec A x) i₀) =
          lam * GaussInt.scale (u i₀) (y i₀) := by
        rw [congrFun hAx i₀, ← GaussInt.mul_scale_right, ← huy i₀]
      rw [hrow1, ← GaussInt.scale_scale, ← GaussInt.ofInt_mul rho _] at hrow2
      have hdiff : (lam - GaussInt.ofInt rho) * GaussInt.scale (u i₀) (y i₀) = GaussInt.zero := by
        rw [GaussInt.sub_mul_left, hrow2, GaussInt.sub_self]
      have hnorm0 :
          GaussInt.normSq (lam - GaussInt.ofInt rho) *
            ((u i₀ * u i₀) * GaussInt.normSq (y i₀)) = 0 := by
        rw [← GaussInt.normSq_scale, ← GaussInt.normSq_mul, hdiff]
        rfl
      have hp1 : 0 < GaussInt.normSq (lam - GaussInt.ofInt rho) :=
        GaussInt.normSq_pos_of_ne_zero (GaussInt.sub_ne_zero_of_ne hne)
      have hp2 : 0 < u i₀ * u i₀ := Int.mul_pos (hu i₀) (hu i₀)
      have hp3 : 0 < GaussInt.normSq (y i₀) := GaussInt.normSq_pos_of_ne_zero hyi₀
      have hprod_pos :
          0 < GaussInt.normSq (lam - GaussInt.ofInt rho) *
                ((u i₀ * u i₀) * GaussInt.normSq (y i₀)) :=
        Int.mul_pos hp1 (Int.mul_pos hp2 hp3)
      omega
    · rcases exists_ne_of_not_forall_eq y (y i₀) hconst with ⟨j, hj⟩
      exact ⟨j, i₀, hj⟩
  -- 2. Choose pair `(i, k)` attaining `D = maxPairDiffSq y > 0` ordered with `u k ≤ u i`
  have hD_pos : 0 < maxPairDiffSq y := maxPairDiffSq_pos_of_nonconst hy_nonconst
  rcases maxPairDiffSq_attained y with ⟨i₁, k₁, hD_eq₁⟩
  have hord : ∃ i k : Fin (m + 2),
      maxPairDiffSq y = GaussInt.normSq (y i - y k) ∧ u k ≤ u i ∧ i ≠ k := by
    have hne₁ : i₁ ≠ k₁ := by
      intro heq
      subst heq
      rw [GaussInt.sub_self] at hD_eq₁
      have hz : maxPairDiffSq y = 0 := hD_eq₁
      omega
    by_cases huk : u k₁ ≤ u i₁
    · exact ⟨i₁, k₁, hD_eq₁, huk, hne₁⟩
    · refine ⟨k₁, i₁, ?_, by omega, fun h => hne₁ h.symm⟩
      rw [hD_eq₁, GaussInt.normSq_sub_symm]
  rcases hord with ⟨i, k, hD_eq, huk, hik_ne⟩
  -- 3. Apply `pairwise_weight_contraction` to `P⁺_j = u_k A_{ij} u_j` and `P⁻_j = u_i A_{kj} u_j`
  let Ppos : Fin (m + 2) → Int := fun j => u k * (A i j * u j)
  let Pneg : Fin (m + 2) → Int := fun j => u i * (A k j * u j)
  let M : Int := rho * (u i * u k)
  have hPpos_nn : ∀ j, 0 ≤ Ppos j := fun j =>
    Int.mul_nonneg (by have := hu k; omega)
      (Int.mul_nonneg (by have := hposA i j; omega) (by have := hu j; omega))
  have hPneg_nn : ∀ j, 0 ≤ Pneg j := fun j =>
    Int.mul_nonneg (by have := hu i; omega)
      (Int.mul_nonneg (by have := hposA k j; omega) (by have := hu j; omega))
  have hsum_Ppos : finSum (m + 2) Ppos = M := by
    dsimp [Ppos, M]
    rw [finSum_mul_left]
    change u k * matVec A u i = rho * (u i * u k)
    rw [congrFun hPerron i]
    rw [← Int.mul_assoc (u k) rho (u i), Int.mul_comm (u k) rho, Int.mul_assoc rho (u k) (u i),
        Int.mul_comm (u k) (u i)]
  have hsum_Pneg : finSum (m + 2) Pneg = M := by
    dsimp [Pneg, M]
    rw [finSum_mul_left]
    change u i * matVec A u k = rho * (u i * u k)
    rw [congrFun hPerron k]
    rw [← Int.mul_assoc (u i) rho (u k), Int.mul_comm (u i) rho, Int.mul_assoc rho (u i) (u k)]
  have hpair_contr := pairwise_weight_contraction (m := m + 1) Ppos Pneg M y hsum_Ppos hsum_Pneg
  let W : Fin (m + 2) → Int := fun j => intMin (Ppos j) (Pneg j)
  let T : Int := M - finSum (m + 2) W
  have hT_nn : 0 ≤ T := hpair_contr.1
  have hcontr :
      GaussInt.normSq (cFinSum (m + 2) (fun j => GaussInt.scale (Ppos j - Pneg j) (y j))) ≤
        T * T * maxPairDiffSq y := hpair_contr.2
  -- 4. Identify `Δ = lam * scale (u_i * u_k) (y_i - y_k)`
  have hΔ_id : cFinSum (m + 2) (fun j => GaussInt.scale (Ppos j - Pneg j) (y j)) =
      lam * GaussInt.scale (u i * u k) (y i - y k) := by
    have hsplit : ∀ j, GaussInt.scale (Ppos j - Pneg j) (y j) =
        GaussInt.scale (Ppos j) (y j) - GaussInt.scale (Pneg j) (y j) :=
      fun j => GaussInt.sub_scale _ _ _
    rw [cFinSum_congr hsplit, cFinSum_sub]
    have hterm_pos : cFinSum (m + 2) (fun j => GaussInt.scale (Ppos j) (y j)) =
        lam * GaussInt.scale (u i * u k) (y i) := by
      have hc : ∀ j, GaussInt.scale (Ppos j) (y j) =
          GaussInt.scale (u k * U) (GaussInt.scale (A i j) (x j)) := by
        intro j
        dsimp [Ppos]
        rw [← GaussInt.scale_scale (u k) (A i j * u j) (y j),
            ← GaussInt.scale_scale (A i j) (u j) (y j), huy j,
            GaussInt.scale_scale (A i j) U (x j), Int.mul_comm (A i j) U,
            ← GaussInt.scale_scale U (A i j) (x j), GaussInt.scale_scale (u k) U _]
      rw [cFinSum_congr hc, cFinSum_scale]
      change GaussInt.scale (u k * U) ((cMatVec A x) i) = _
      rw [congrFun heig.2 i, ← GaussInt.mul_scale_right, ← GaussInt.scale_scale (u k) U (x i),
          ← huy i, GaussInt.scale_scale (u k) (u i) (y i), Int.mul_comm (u k) (u i)]
    have hterm_neg : cFinSum (m + 2) (fun j => GaussInt.scale (Pneg j) (y j)) =
        lam * GaussInt.scale (u i * u k) (y k) := by
      have hc : ∀ j, GaussInt.scale (Pneg j) (y j) =
          GaussInt.scale (u i * U) (GaussInt.scale (A k j) (x j)) := by
        intro j
        dsimp [Pneg]
        rw [← GaussInt.scale_scale (u i) (A k j * u j) (y j),
            ← GaussInt.scale_scale (A k j) (u j) (y j), huy j,
            GaussInt.scale_scale (A k j) U (x j), Int.mul_comm (A k j) U,
            ← GaussInt.scale_scale U (A k j) (x j), GaussInt.scale_scale (u i) U _]
      rw [cFinSum_congr hc, cFinSum_scale]
      change GaussInt.scale (u i * U) ((cMatVec A x) k) = _
      rw [congrFun heig.2 k, ← GaussInt.mul_scale_right, ← GaussInt.scale_scale (u i) U (x k),
          ← huy k, GaussInt.scale_scale (u i) (u k) (y k)]
    rw [hterm_pos, hterm_neg, ← GaussInt.mul_sub_right, ← GaussInt.scale_sub]
  rw [hΔ_id, GaussInt.normSq_mul, GaussInt.normSq_scale, ← hD_eq, ← Int.mul_assoc] at hcontr
  have hlam_uu_le : GaussInt.normSq lam * ((u i * u k) * (u i * u k)) ≤ T * T :=
    Int.le_of_mul_le_mul_right hcontr hD_pos
  -- 5. Bound `S = finSum W > pmin * (u i * u k)` using terms `j = i` and `j = k`
  have hW_nn : ∀ j, 0 ≤ W j := fun j => intMin_nonneg (hPpos_nn j) (hPneg_nn j)
  have hpair := finSum_ge_pair hW_nn i k hik_ne
  have hWi : pmin * (u i * u k) ≤ W i := by
    apply le_intMin
    · dsimp [Ppos]
      have hm1 : pmin ≤ A i i := posModulusMin_le A i i
      have h1 : pmin * u i ≤ A i i * u i :=
        Int.mul_le_mul hm1 (Int.le_refl _) (by have := hu i; omega) (by have := hposA i i; omega)
      have h2 : u k * (pmin * u i) ≤ u k * (A i i * u i) :=
        Int.mul_le_mul (Int.le_refl _) h1 (Int.mul_nonneg (by omega) (by have := hu i; omega))
          (by have := hu k; omega)
      have hrew : u k * (pmin * u i) = pmin * (u i * u k) := by
        rw [← Int.mul_assoc, Int.mul_comm (u k) pmin, Int.mul_assoc, Int.mul_comm (u k) (u i)]
      rw [← hrew]; exact h2
    · dsimp [Pneg]
      have hm2 : pmin ≤ A k i := posModulusMin_le A k i
      have h1 : pmin * u k ≤ A k i * u i :=
        Int.mul_le_mul hm2 huk (by have := hu k; omega) (by have := hposA k i; omega)
      have h2 : u i * (pmin * u k) ≤ u i * (A k i * u i) :=
        Int.mul_le_mul (Int.le_refl _) h1 (Int.mul_nonneg (by omega) (by have := hu k; omega))
          (by have := hu i; omega)
      have hrew : u i * (pmin * u k) = pmin * (u i * u k) := by
        rw [← Int.mul_assoc, Int.mul_comm (u i) pmin, Int.mul_assoc]
      rw [← hrew]; exact h2
  have hWk_pos : 0 < W k := by
    unfold W intMin
    split
    · exact Int.mul_pos (hu k) (Int.mul_pos (hposA i k) (hu k))
    · exact Int.mul_pos (hu i) (Int.mul_pos (hposA k k) (hu k))
  have hS_gt : pmin * (u i * u k) < finSum (m + 2) W := by omega
  have hT_def : T = rho * (u i * u k) - finSum (m + 2) W := rfl
  have hT_lt : T < (rho - pmin) * (u i * u k) := by
    rw [hT_def, Int.sub_mul]
    omega
  have huu_pos : 0 < u i * u k := Int.mul_pos (hu i) (hu k)
  have hprod_pos : 0 < (rho - pmin) * (u i * u k) := by omega
  have hrho_gt_pmin : pmin < rho := by
    by_cases hle : rho ≤ pmin
    · have hneg1 : 0 ≤ (pmin - rho) * (u i * u k) :=
        Int.mul_nonneg (by omega) (by omega)
      rw [Int.sub_mul] at hneg1
      rw [Int.sub_mul] at hprod_pos
      omega
    · omega
  have hT_sq_lt : T * T < ((rho - pmin) * (rho - pmin)) * ((u i * u k) * (u i * u k)) := by
    rw [int_mul_self_mul_self (rho - pmin) (u i * u k)]
    exact int_sq_lt_sq hT_nn hT_lt
  have hfinal_mul :
      GaussInt.normSq lam * ((u i * u k) * (u i * u k)) <
        ((rho - pmin) * (rho - pmin)) * ((u i * u k) * (u i * u k)) :=
    Int.lt_of_le_of_lt hlam_uu_le hT_sq_lt
  have huu_sq_nn : 0 ≤ (u i * u k) * (u i * u k) := int_sq_nonneg _
  exact ⟨hrho_gt_pmin, Int.lt_of_mul_lt_mul_right hfinal_mul huu_sq_nn⟩

/-- Real-eigenvalue corollary of `strictlyPositive_gap_gt_posModulus`:
    for any real eigenpair `(A, lam, v)` with `lam ≠ rho`, `posModulusMin A < rho - |lam|`. -/
theorem strictlyPositive_real_gap_gt_posModulus {m : Nat} (A : IMat (m + 2))
    (hposA : IsStrictlyPositive A)
    (rho : Int) (u : IVec (m + 2))
    (hrho : 0 < rho) (hu : ∀ i, 0 < u i)
    (hPerron : matVec A u = fun i => rho * u i)
    (lam : Int) (v : IVec (m + 2))
    (heig : IsEigenpair A lam v) (hne : lam ≠ rho) :
    let absLam : Int := if 0 ≤ lam then lam else -lam
    posModulusMin A < rho - absLam := by
  intro absLam
  let cv : CVec (m + 2) := fun j => GaussInt.ofInt (v j)
  have hceig : IsComplexEigenpair A (GaussInt.ofInt lam) cv := by
    rcases heig with ⟨⟨i₀, hvi₀⟩, hAv⟩
    refine ⟨⟨i₀, ?_⟩, ?_⟩
    · intro h0
      exact hvi₀ (congrArg GaussInt.re h0)
    · funext i
      unfold cMatVec cv
      have hc : ∀ j, GaussInt.scale (A i j) (GaussInt.ofInt (v j)) =
          GaussInt.ofInt (A i j * v j) := by
        intro j; apply GaussInt.ext <;> simp [GaussInt.scale, GaussInt.ofInt]
      rw [cFinSum_congr hc]
      have hsum_ofInt : ∀ k : Nat, ∀ f : Fin k → Int,
          cFinSum k (fun j => GaussInt.ofInt (f j)) = GaussInt.ofInt (finSum k f) := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ k ih =>
          intro f
          simp only [cFinSum, finSum]
          rw [ih]
          apply GaussInt.ext <;> rfl
      rw [hsum_ofInt]
      change GaussInt.ofInt (matVec A v i) = GaussInt.ofInt lam * GaussInt.ofInt (v i)
      rw [congrFun hAv i]
      apply GaussInt.ext
      · change lam * v i = lam * v i - 0 * 0; omega
      · change 0 = lam * 0 + 0 * v i; omega
  have hcne : GaussInt.ofInt lam ≠ GaussInt.ofInt rho := by
    intro heq
    exact hne (congrArg GaussInt.re heq)
  rcases strictlyPositive_gap_gt_posModulus A hposA rho u hrho hu hPerron
      (GaussInt.ofInt lam) cv hceig hcne with ⟨hrho_gt, hsq⟩
  have hnorm : GaussInt.normSq (GaussInt.ofInt lam) = absLam * absLam := by
    dsimp [absLam, GaussInt.normSq, GaussInt.ofInt]
    split
    · omega
    · rw [Int.neg_mul_neg]; omega
  rw [hnorm] at hsq
  have hlt : absLam < rho - posModulusMin A :=
    int_lt_of_sq_lt_sq (by omega) hsq
  omega

/-! ## 5. Sharp `2 × 2` Positivity-Modulus Theorem (`λ₁ - |λ₂| ≥ 2 m`) -/

theorem twoByTwo_gap_ge_two_posModulus (a b c d m lam₁ lam₂ : Int)
    (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) (hc : m ≤ c) (hd : m ≤ d)
    (hord : lam₂ ≤ lam₁)
    (htr : lam₁ + lam₂ = a + d)
    (hdisc : (lam₁ - lam₂) * (lam₁ - lam₂) = (a - d) * (a - d) + 4 * (b * c)) :
    let absLam₂ : Int := if 0 ≤ lam₂ then lam₂ else -lam₂
    2 * m ≤ lam₁ - absLam₂ := by
  intro absLam₂
  dsimp [absLam₂]
  split
  · have hbc : m * m ≤ b * c := Int.mul_le_mul hb hc (by omega) (by omega)
    have had : 0 ≤ (a - d) * (a - d) := int_sq_nonneg (a - d)
    have hsq : (2 * m) * (2 * m) ≤ (lam₁ - lam₂) * (lam₁ - lam₂) := by
      have h4m : (2 * m) * (2 * m) = 4 * (m * m) := by
        calc
          (2 * m) * (2 * m) = (2 * 2) * (m * m) := (int_mul_self_mul_self 2 m).symm
          _ = 4 * (m * m) := rfl
      rw [h4m, hdisc]
      omega
    exact int_le_of_sq_le_sq (by omega) hsq
  · omega

theorem twoByTwo_gap_sharp_families (K m : Int) (hm : 0 < m) (hK : m ≤ K) :
    (let lam₁ := K + m
     let lam₂ := K - m
     let absLam₂ := if 0 ≤ lam₂ then lam₂ else -lam₂
     lam₁ - absLam₂ = 2 * m) ∧
    (let lam₁ := K + m
     let lam₂ := m - K
     let absLam₂ := if 0 ≤ lam₂ then lam₂ else -lam₂
     lam₁ - absLam₂ = 2 * m) := by
  have _ := hm
  constructor
  · dsimp; split <;> omega
  · dsimp; split <;> omega

end Conjecture00000007163
