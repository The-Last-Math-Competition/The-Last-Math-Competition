import Mathlib
import Conjecture1463.Statement

/-! # Conjecture 1463: sup of projection constants of ell_p^n is c sqrt n, attained by ell_1^n and ell_infty^n

We refute it: the absolute projection constant of ell_infty^n is at most 1 (in fact 1), so it is not
asymptotic to `c * sqrt n` for any real `c`; nor does it grow like `kappa * sqrt n` for any `kappa > 0`.
Scalars: real and complex. -/

-- (formal statement: see Statement.lean)

namespace C1463

open Filter Topology ENNReal

variable {𝕜 : Type} [RCLike 𝕜]

/-- The projection constant relative to any embedding of `ℓ∞ⁿ` is at most `1`. -/
lemma relProj_le_one {n : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (j : PiLp ∞ (fun _ : Fin n => 𝕜) →ₗᵢ[𝕜] X) : relProj 𝕜 j ≤ 1 := by
  let e : PiLp ∞ (fun _ : Fin n => 𝕜) ≃ₗᵢ[𝕜] LinearMap.range j.toLinearMap := j.equivRange
  -- coordinate functionals on the copy
  have hψ : ∀ i : Fin n, ∃ ψ : StrongDual 𝕜 (LinearMap.range j.toLinearMap),
      (∀ y : PiLp ∞ (fun _ : Fin n => 𝕜), ψ (e y) = y i) ∧ ‖ψ‖ ≤ 1 := by
    intro i
    refine ⟨LinearMap.mkContinuous
      ((PiLp.proj ∞ (fun _ : Fin n => 𝕜) i).toLinearMap ∘ₗ e.symm.toLinearEquiv.toLinearMap) 1 ?_,
      ?_, ?_⟩
    · intro z
      simp only [LinearMap.coe_comp, Function.comp_apply, one_mul]
      exact (PiLp.norm_apply_le _ i).trans (by simp)
    · intro y; simp
    · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  choose ψ hψ1 hψ2 using hψ
  have hg : ∀ i : Fin n, ∃ g : StrongDual 𝕜 X, (∀ z : LinearMap.range j.toLinearMap, g z = ψ i z) ∧
      ‖g‖ = ‖ψ i‖ := fun i => exists_extension_norm_eq _ (ψ i)
  choose g hg1 hg2 using hg
  let L : X →ₗ[𝕜] PiLp ∞ (fun _ : Fin n => 𝕜) :=
    { toFun := fun x => WithLp.toLp ∞ (fun i => g i x)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  have hL : ∀ x, ‖L x‖ ≤ 1 * ‖x‖ := by
    intro x
    show ‖WithLp.toLp ∞ (fun i => g i x)‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_toLp, one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
    exact ((g i).le_opNorm x).trans (by nlinarith [hg2 i, hψ2 i, norm_nonneg x, norm_nonneg (g i)])
  let T : X →L[𝕜] PiLp ∞ (fun _ : Fin n => 𝕜) := L.mkContinuous 1 hL
  have hT : ∀ x, ‖T x‖ ≤ ‖x‖ := fun x => by have := hL x; rw [one_mul] at this; exact this
  have hTj : ∀ y, T (j y) = y := by
    intro y; ext i
    show g i (j y) = y.ofLp i
    exact (hg1 i ⟨j y, ⟨y, rfl⟩⟩).trans (hψ1 i y)
  let P : X →L[𝕜] X := j.toContinuousLinearMap.comp T
  have hP : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => by simpa [P] using hT x
  refine (ciInf_le ⟨0, ?_⟩ (⟨P, ?_, ?_⟩ : {P : X →L[𝕜] X // (∀ y, P (j y) = j y) ∧
    ∀ x, ∃ y, P x = j y})).trans ?_
  · rintro _ ⟨Q, rfl⟩; exact norm_nonneg _
  · intro y; simp [P, hTj]
  · intro x; exact ⟨T x, rfl⟩
  · exact P.opNorm_le_bound zero_le_one (by simpa using hP)

lemma lam_infty_le_one (n : ℕ) : lam 𝕜 ∞ n ≤ 1 := by
  unfold lam absProj
  refine Real.sSup_le ?_ zero_le_one
  rintro _ ⟨X, _, _, _, j, rfl⟩
  exact relProj_le_one j

lemma lam_infty_nonneg (n : ℕ) : 0 ≤ lam 𝕜 ∞ n := by
  unfold lam absProj
  refine Real.sSup_nonneg ?_
  rintro _ ⟨X, _, _, _, j, rfl⟩
  exact Real.iInf_nonneg fun _ => norm_nonneg _

lemma not_sharp : ¬ ConjSharp 𝕜 := by
  rintro ⟨c, -, -, h⟩
  have h0 := lam_infty_nonneg (𝕜 := 𝕜)
  have h1 := lam_infty_le_one (𝕜 := 𝕜)
  rcases lt_trichotomy c 0 with hc | hc | hc
  · -- ratio ≤ 0 eventually, cannot tend to 1
    have : ∀ᶠ n : ℕ in atTop, lam 𝕜 ∞ n / (c * Real.sqrt n) < 1 / 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have : c * Real.sqrt n < 0 := by nlinarith
      exact (div_nonpos_of_nonneg_of_nonpos (h0 n) this.le).trans_lt (by norm_num)
    obtain ⟨n, hn⟩ := (h.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).and this |>.exists
    linarith [hn.1, hn.2]
  · subst hc
    simp at h
  · -- ratio ≤ 1/(c √n) → 0
    have hlim : Tendsto (fun n : ℕ => 1 / (c * Real.sqrt n)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => c * Real.sqrt n) atTop atTop :=
        Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      exact Tendsto.congr (fun n => (one_div _).symm) this.inv_tendsto_atTop
    have : ∀ᶠ n : ℕ in atTop, lam 𝕜 ∞ n / (c * Real.sqrt n) < 1 / 2 := by
      filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
        eventually_ge_atTop 1] with n hn hn1
      have : 0 < c * Real.sqrt n := mul_pos hc (Real.sqrt_pos.2 (by exact_mod_cast hn1))
      refine lt_of_le_of_lt ?_ hn
      rw [one_div]
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.2 this.le) (h1 n)
    obtain ⟨n, hn⟩ := (h.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).and this |>.exists
    linarith [hn.1, hn.2]

lemma not_order : ¬ ConjOrder 𝕜 := by
  rintro ⟨κ, hκ, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / κ ^ 2)
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < 1 / κ ^ 2 := by positivity
    exact_mod_cast (by linarith : (0 : ℝ) < n)
  have h2 := (h n hn1).trans (lam_infty_le_one (𝕜 := 𝕜) n)
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have h3 : κ ^ 2 * n ≤ 1 := by nlinarith [mul_pos hκ (Real.sqrt_pos.2 (by exact_mod_cast hn1 : (0:ℝ) < n))]
  have : 1 < κ ^ 2 * n := by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  linarith

theorem main : Claim :=
  ⟨not_sharp, not_sharp, not_order, not_order⟩

end C1463
