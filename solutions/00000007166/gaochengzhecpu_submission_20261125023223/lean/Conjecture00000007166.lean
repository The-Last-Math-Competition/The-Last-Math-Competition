/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007166 in Core Lean 4.19.0 (zero external dependencies).

Root Module: Conjecture00000007166
Conjecture 00000007166:
  "Definition: The Kantorovich inequality with the multiplicative bound of the quotient.
   Conjecture: The optimal constant is an explicit function of the condition ratio, and
   the minimum of the function is the harmonic mean. (harmonic-mean Kantorovich constant)"

Verdict: FALSE (Clause 1 is TRUE; Clause 2 is FALSE across all candidate readings A, B, C, D).
-/

import Conjecture00000007166.OrderedField
import Conjecture00000007166.Kantorovich
import Conjecture00000007166.Refutation

namespace Conjecture00000007166

/-- **Master Theorem 1 (Clause 1 — Positive Theorem over any `LinearOrderedField F`)**:
    For every dimension `n ≥ 2`, orthogonal matrix `Q` (`Q^T Q = Q Q^T = I_n`), and
    spectrum `0 < m ≤ λ_i ≤ M` attaining `m` and `M` at distinct indices `j ≠ k`:
      1. `K(M/m) = ((M/m + 1)^2) / (4(M/m)) = (M + m)^2 / (4Mm) = AM(M, m) / HM(M, m)`.
      2. Every nonzero vector `x` satisfies `1 ≤ Q_A(x) ≤ K(M/m)`.
      3. `K(M/m)` is attained explicitly at `x* = q_j + q_k` (`Q^T x* = e_j + e_k`),
         so `K(κ) = (κ + 1)^2 / (4κ)` is the exact optimal multiplicative constant. -/
theorem conjecture_00000007166_clause1_true
    {F : Type u} [LinearOrderedField F]
    (n : Nat) (lam : Fin n → F) {M m : F} {j k : Fin n}
    (hjk : j ≠ k) (hm_pos : 0 < m) (hmM : m ≤ M)
    (hlam_bounds : ∀ i, m ≤ lam i ∧ lam i ≤ M)
    (hj : lam j = m) (hk : lam k = M) :
    kantorovichConst (M / m) = ((M + m) * (M + m)) / (fourF * M * m) ∧
    kantorovichConst (M / m) = arithmeticMean M m / harmonicMean M m ∧
    (∀ x : Fin n → F, (∃ i, x i ≠ 0) →
      1 ≤ kantorovichQuotient n lam x ∧
      kantorovichQuotient n lam x ≤ kantorovichConst (M / m)) ∧
    (∃ x : Fin n → F, (∃ i, x i ≠ 0) ∧
      kantorovichQuotient n lam x = kantorovichConst (M / m)) := by
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  refine ⟨kantorovichConst_ratio (ne_of_gt hm_pos),
          kantorovichConst_eq_am_div_hm hm_pos hM_pos,
          fun x hx => kantorovich_bounds_diag n lam x hm_pos hmM hlam_bounds hx,
          ⟨pairVec n j k, pairVec_nonzero n hjk,
           (kantorovich_tightness_pairVec n lam hjk hm_pos hM_pos hj hk).2.2.2⟩⟩

/-- **Master Theorem 2 (Clause 2 — Complete Refutation over any `LinearOrderedField F`)**:
    Clause 2 ("and the minimum of the function is the harmonic mean") is FALSE under
    all four mathematical readings (Readings A, B, C, and D). -/
theorem conjecture_00000007166_clause2_false
    {F : Type u} [LinearOrderedField F] :
    -- Reading A: Unique minimum of K on [1, ∞) is 1, NOT HM(M, m) and NOT HM(M/m, 1)
    IsMinValueOn (F := F) kantorovichConst (fun κ => 1 ≤ κ) 1 ∧
    ¬ (∀ M m : F, 0 < m → m ≤ M →
        IsMinValueOn kantorovichConst (fun κ => 1 ≤ κ) (harmonicMean M m)) ∧
    ¬ (∀ M m : F, 0 < m → m < M →
        IsMinValueOn kantorovichConst (fun κ => 1 ≤ κ) (harmonicMean (M / m) 1)) ∧
    -- Reading B: Minimum of x ↦ Q_A(x) for A = diag(1, 3) is 1 ≠ 3/2 = HM(3, 1)
    ((let lam : Fin 2 → F := fun i => if i.val = 0 then 1 else threeF
      (∃ x : Fin 2 → F, (∃ i, x i ≠ 0) ∧ kantorovichQuotient 2 lam x = 1) ∧
      (∀ x : Fin 2 → F, (∃ i, x i ≠ 0) → 1 ≤ kantorovichQuotient 2 lam x) ∧
      harmonicMean (threeF : F) 1 ≠ 1)) ∧
    -- Reading C: Reciprocal R(κ) = 4κ/(κ+1)^2 has R(3) = 3/4 ≠ HM(3,1) and NO minimum on [1, ∞)
    (reciprocalKantorovichConst (threeF : F) ≠ harmonicMean (threeF : F) 1 ∧
     ¬ ∃ μ : F, IsMinValueOn reciprocalKantorovichConst (fun κ => 1 ≤ κ) μ) ∧
    -- Reading D: Rayleigh extremum values m < HM(M, m) < AM(M, m) and HM(3,1)⁻¹ ≠ HM(3,1)
    (∀ M m : F, 0 < m → m < M →
      m < harmonicMean M m ∧ harmonicMean M m < arithmeticMean M m) ∧
    (harmonicMean (threeF : F) 1)⁻¹ ≠ harmonicMean (threeF : F) 1 := by
  refine ⟨(readingA_min_is_one (F := F)).1,
          (readingA_refuted (F := F)).1,
          (readingA_refuted (F := F)).2,
          readingB_refuted (F := F),
          ⟨(readingC_refuted (F := F)).1.2, (readingC_refuted (F := F)).2.1⟩,
          fun _ _ hm hlt => m_lt_harmonicMean_lt_arithmeticMean hm hlt,
          ?_⟩
  rcases counterexample_m1_M3 (F := F) with ⟨_, hhm3, _, _⟩
  rw [hhm3, inv_div threeF_ne_zero twoF_ne_zero]
  intro heq
  have hm := (div_eq_div_iff threeF_ne_zero twoF_ne_zero).mp heq
  have hlt23 : (twoF : F) < threeF := twoF_lt_threeF (F := F)
  have hsq : (twoF : F) * twoF < threeF * threeF :=
    lt_trans (mul_lt_mul_of_pos_left hlt23 twoF_pos)
             (mul_lt_mul_of_pos_right hlt23 threeF_pos)
  exact ne_of_lt hsq hm

/-- **Master Theorem 3 (Unconditional Resolution over Concrete Exact Rationals `Q`)**:
    Instantiating `F = Q` removes all typeclass hypotheses, proving unconditionally
    in Core Lean 4 that Clause 1 holds over `Q` while the compound conjecture (requiring
    Clause 2) is FALSE over `Q`. -/
theorem conjecture_00000007166_resolved_over_Q :
    -- Clause 1 holds over Q for all n ≥ 2 and all bounded positive rational spectra:
    (∀ (n : Nat) (lam : Fin n → Q) (M m : Q) (j k : Fin n),
      j ≠ k → 0 < m → m ≤ M →
      (∀ i, m ≤ lam i ∧ lam i ≤ M) → lam j = m → lam k = M →
      (∀ x : Fin n → Q, (∃ i, x i ≠ 0) →
        1 ≤ kantorovichQuotient n lam x ∧
        kantorovichQuotient n lam x ≤ kantorovichConst (M / m)) ∧
      (∃ x : Fin n → Q, (∃ i, x i ≠ 0) ∧
        kantorovichQuotient n lam x = kantorovichConst (M / m))) ∧
    -- Compound conjecture fails over Q (Clause 2 refuted):
    ¬ ((∀ (n : Nat) (lam : Fin n → Q) (M m : Q),
          0 < m → m ≤ M → (∀ i, m ≤ lam i ∧ lam i ≤ M) →
          ∀ x : Fin n → Q, (∃ i, x i ≠ 0) →
            kantorovichQuotient n lam x ≤ kantorovichConst (M / m)) ∧
       (∀ M m : Q, 0 < m → m ≤ M →
          IsMinValueOn kantorovichConst (fun κ => 1 ≤ κ) (harmonicMean M m))) := by
  refine ⟨?_, ?_⟩
  · intro n lam M m j k hjk hm_pos hmM hbounds hj hk
    have hc1 := conjecture_00000007166_clause1_true n lam hjk hm_pos hmM hbounds hj hk
    exact ⟨hc1.2.2.1, hc1.2.2.2⟩
  · rintro ⟨_, hc2⟩
    exact (readingA_refuted (F := Q)).1 hc2

end Conjecture00000007166
