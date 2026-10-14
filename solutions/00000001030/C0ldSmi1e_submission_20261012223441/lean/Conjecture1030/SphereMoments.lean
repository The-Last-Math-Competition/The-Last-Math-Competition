import Conjecture1030.Definitions

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open MeasureTheory Metric Set
namespace Conjecture1030

/-- Coordinate monomials on the genuine Euclidean unit sphere. -/
def sphereMonomial (d : Fin 3 → ℕ) (x : S2) : ℝ := ∏ i, ((x : E) i) ^ d i

/-- The degree-at-most-five moment table, derived below from orthogonal invariance. -/
def sphereMoment (d : Fin 3 → ℕ) : ℝ :=
  if ∃ i, Odd (d i) then 0 else
  if ∑ i, d i = 0 then 1 else
  if ∑ i, d i = 2 then 1 / 3 else
  if ∃ i, d i = 4 then 1 / 5 else 1 / 15

instance sphere_compactSpace : CompactSpace S2 :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)

@[fun_prop] theorem continuous_sphere_coord (i : Fin 3) : Continuous (fun x : S2 => (x : E) i) :=
  ((continuous_apply i).comp (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ))).comp continuous_subtype_val

theorem continuous_sphereMonomial (d : Fin 3 → ℕ) : Continuous (sphereMonomial d) := by
  unfold sphereMonomial
  exact continuous_finset_prod _ (fun i _ => (continuous_sphere_coord i).pow (d i))

theorem continuous_evalOnSphere (p : MvPolynomial (Fin 3) ℝ) : Continuous (evalOnSphere p) := by
  unfold evalOnSphere
  exact p.continuous_eval.comp (continuous_pi continuous_sphere_coord)

theorem integrable_evalOnSphere (μ : Measure S2) [IsFiniteMeasure μ]
    (p : MvPolynomial (Fin 3) ℝ) : Integrable (evalOnSphere p) μ := by
  simpa using (continuous_evalOnSphere p).continuousOn.integrableOn_compact (isCompact_univ : IsCompact (Set.univ : Set S2))

theorem integrable_sphereMonomial (μ : Measure S2) [IsFiniteMeasure μ]
    (d : Fin 3 → ℕ) : Integrable (sphereMonomial d) μ := by
  simpa using (continuous_sphereMonomial d).continuousOn.integrableOn_compact (isCompact_univ : IsCompact (Set.univ : Set S2))

def coordFlip (i : Fin 3) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

@[simp] theorem coordFlip_apply (i j : Fin 3) (x : E) :
    coordFlip i x j = if j = i then -x j else x j := by
  by_cases h : j = i
  · subst j
    simp [coordFlip, LinearIsometryEquiv.piLpCongrRight_apply]
  · simp [coordFlip, LinearIsometryEquiv.piLpCongrRight_apply, h]

def coordSwap (i j : Fin 3) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

@[simp] theorem coordSwap_apply (i j k : Fin 3) (x : E) :
    coordSwap i j x k = x (Equiv.swap i j k) := by
  simp [coordSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem invariant_integral (μ : Measure S2) (hμ : OrthogonallyInvariant μ)
    (U : E ≃ₗᵢ[ℝ] E) (f : S2 → ℝ) :
    (∫ x, f (sphereIso U x) ∂μ) = ∫ x, f x ∂μ :=
  (hμ U).integral_comp (sphereIso U).toHomeomorph.measurableEmbedding f

end Conjecture1030

namespace Conjecture1030

theorem integrable_sphere_continuous (μ : Measure S2) [IsFiniteMeasure μ]
    {f : S2 → ℝ} (hf : Continuous f) : Integrable f μ := by
  simpa using hf.continuousOn.integrableOn_compact (isCompact_univ : IsCompact (Set.univ : Set S2))

theorem sphereMonomial_flip (d : Fin 3 → ℕ) (i : Fin 3) (hi : Odd (d i)) (x : S2) :
    sphereMonomial d (sphereIso (coordFlip i) x) = -sphereMonomial d x := by
  fin_cases i <;> simp_all [sphereMonomial, Fin.prod_univ_succ, Odd.neg_pow]

theorem sphereMonomial_integral_odd (μ : Measure S2) (hμ : OrthogonallyInvariant μ)
    (d : Fin 3 → ℕ) (hi : ∃ i, Odd (d i)) :
    (∫ x, sphereMonomial d x ∂μ) = 0 := by
  obtain ⟨i, hi⟩ := hi
  have ht := invariant_integral μ hμ (coordFlip i) (sphereMonomial d)
  simp_rw [sphereMonomial_flip d i hi] at ht
  rw [integral_neg] at ht
  linarith

def plane45 : E ≃ₗᵢ[ℝ] E where
  toFun x := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(x 0 + x 1) / Real.sqrt 2, (x 0 - x 1) / Real.sqrt 2, x 2]
  invFun x := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(x 0 + x 1) / Real.sqrt 2, (x 0 - x 1) / Real.sqrt 2, x 2]
  left_inv x := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    ext i
    fin_cases i <;> simp [WithLp.equiv_symm_pi_apply] <;> field_simp
  right_inv x := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    ext i
    fin_cases i <;> simp [WithLp.equiv_symm_pi_apply] <;> field_simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp [WithLp.equiv_symm_pi_apply] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [WithLp.equiv_symm_pi_apply] <;> ring
  norm_map' x := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq3, norm_sq3]
    change ((x 0 + x 1) / Real.sqrt 2)^2 + ((x 0 - x 1) / Real.sqrt 2)^2 + x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
    field_simp
    nlinarith

@[simp] theorem plane45_apply_zero (x : E) : plane45 x 0 = (x 0 + x 1) / Real.sqrt 2 := rfl
@[simp] theorem plane45_apply_one (x : E) : plane45 x 1 = (x 0 - x 1) / Real.sqrt 2 := rfl
@[simp] theorem plane45_apply_two (x : E) : plane45 x 2 = x 2 := rfl

end Conjecture1030

namespace Conjecture1030

theorem integrable_coord_pow (μ : Measure S2) [IsFiniteMeasure μ] (i : Fin 3) (n : ℕ) :
    Integrable (fun x : S2 => ((x : E) i)^n) μ :=
  integrable_sphere_continuous μ ((continuous_sphere_coord i).pow n)

theorem coord_pow_integral_eq (μ : Measure S2) (hμ : OrthogonallyInvariant μ)
    (i j : Fin 3) (n : ℕ) :
    (∫ x : S2, ((x : E) i)^n ∂μ) = ∫ x : S2, ((x : E) j)^n ∂μ := by
  have h := invariant_integral μ hμ (coordSwap i j) (fun x => ((x : E) i)^n)
  have hf : (fun x : S2 => ((sphereIso (coordSwap i j) x : S2) : E) i ^ n) =
      (fun x : S2 => (x : E) j ^ n) := by
    funext x
    rw [sphereIso_coe, coordSwap_apply, Equiv.swap_apply_left]
  rw [hf] at h
  exact h.symm

theorem coord_sq_integral (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) (i : Fin 3) :
    (∫ x : S2, ((x : E) i)^2 ∂μ) = 1 / 3 := by
  have hi0 := coord_pow_integral_eq μ hμ 0 i 2
  have hi1 := coord_pow_integral_eq μ hμ 1 i 2
  have hi2 := coord_pow_integral_eq μ hμ 2 i 2
  have he : (∫ x : S2, ((x : E) 0)^2 + ((x : E) 1)^2 + ((x : E) 2)^2 ∂μ) = 1 := by
    simp_rw [sphere_sq]
    simp
  rw [integral_add (f := fun x : S2 => ((x : E) 0)^2 + ((x : E) 1)^2)
      (g := fun x : S2 => ((x : E) 2)^2)
      ((integrable_coord_pow μ 0 2).add (integrable_coord_pow μ 1 2))
      (integrable_coord_pow μ 2 2), integral_add (integrable_coord_pow μ 0 2)
      (integrable_coord_pow μ 1 2)] at he
  linarith

end Conjecture1030

namespace Conjecture1030

theorem coord_mixed_integral_eq (μ : Measure S2) (hμ : OrthogonallyInvariant μ)
    (i j : Fin 3) (hij : i ≠ j) :
    (∫ x : S2, ((x : E) i)^2 * ((x : E) j)^2 ∂μ) =
      ∫ x : S2, ((x : E) 0)^2 * ((x : E) 1)^2 ∂μ := by
  have h02 := invariant_integral μ hμ (coordSwap 1 2)
    (fun x => ((x : E) 0)^2 * ((x : E) 1)^2)
  have h12 := invariant_integral μ hμ (coordSwap 0 2)
    (fun x => ((x : E) 0)^2 * ((x : E) 1)^2)
  have hf02 : (fun x : S2 => ((sphereIso (coordSwap 1 2) x : S2) : E) 0 ^ 2 *
      ((sphereIso (coordSwap 1 2) x : S2) : E) 1 ^ 2) =
      (fun x : S2 => (x : E) 0 ^ 2 * (x : E) 2 ^ 2) := by
    funext x
    simp [sphereIso_coe, coordSwap_apply, Equiv.swap_apply_def]
  have hf12 : (fun x : S2 => ((sphereIso (coordSwap 0 2) x : S2) : E) 0 ^ 2 *
      ((sphereIso (coordSwap 0 2) x : S2) : E) 1 ^ 2) =
      (fun x : S2 => (x : E) 2 ^ 2 * (x : E) 1 ^ 2) := by
    funext x
    simp [sphereIso_coe, coordSwap_apply, Equiv.swap_apply_def]
  rw [hf02] at h02
  rw [hf12] at h12
  have hc (a b : Fin 3) : (∫ x : S2, (x : E) a ^ 2 * (x : E) b ^ 2 ∂μ) =
      ∫ x : S2, (x : E) b ^ 2 * (x : E) a ^ 2 ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  fin_cases i <;> fin_cases j <;>
    first | contradiction | rfl | exact h02 | exact h12 |
      exact (hc _ _).trans h02 | exact (hc _ _).trans h12 | exact hc _ _

theorem coord_fourth_mixed_integrals (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) :
    (∫ x : S2, ((x : E) 0)^4 ∂μ) = 1 / 5 ∧
    (∫ x : S2, ((x : E) 0)^2 * ((x : E) 1)^2 ∂μ) = 1 / 15 := by
  have h31 : (∫ x : S2, ((x : E) 0)^3 * ((x : E) 1) ∂μ) = 0 := by
    simpa [sphereMonomial, Fin.prod_univ_succ] using
      sphereMonomial_integral_odd μ hμ ![3, 1, 0] ⟨0, ⟨1, rfl⟩⟩
  have h13 : (∫ x : S2, ((x : E) 0) * ((x : E) 1)^3 ∂μ) = 0 := by
    simpa [sphereMonomial, Fin.prod_univ_succ] using
      sphereMonomial_integral_odd μ hμ ![1, 3, 0] ⟨0, ⟨0, rfl⟩⟩
  have h4 := coord_pow_integral_eq μ hμ 1 0 4
  have hm := coord_mixed_integral_eq μ hμ 0 2 (by decide)
  have hrot := invariant_integral μ hμ plane45 (fun x => ((x : E) 0)^4)
  simp only [sphereIso_coe, plane45_apply_zero] at hrot
  have hrotpoly (x : S2) : (((x : E) 0 + (x : E) 1) / Real.sqrt 2)^4 =
      (1 / 4 : ℝ) * (((x : E) 0)^4 + 4 * (((x : E) 0)^3 * (x : E) 1) +
      6 * (((x : E) 0)^2 * ((x : E) 1)^2) +
      4 * ((x : E) 0 * ((x : E) 1)^3) + ((x : E) 1)^4) := by
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs4 : Real.sqrt 2 ^ 4 = 4 := by nlinarith [sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
    rw [div_pow, hs4]
    ring
  simp_rw [hrotpoly] at hrot
  rw [integral_const_mul] at hrot
  have hrotint :
      (∫ x : S2, (((x : E) 0)^4 + 4 * (((x : E) 0)^3 * (x : E) 1) +
      6 * (((x : E) 0)^2 * ((x : E) 1)^2) +
      4 * ((x : E) 0 * ((x : E) 1)^3) + ((x : E) 1)^4) ∂μ) =
      (∫ x : S2, ((x : E) 0)^4 ∂μ) + 4 * (∫ x : S2, ((x : E) 0)^3 * (x : E) 1 ∂μ) +
      6 * (∫ x : S2, ((x : E) 0)^2 * ((x : E) 1)^2 ∂μ) +
      4 * (∫ x : S2, (x : E) 0 * ((x : E) 1)^3 ∂μ) + (∫ x : S2, ((x : E) 1)^4 ∂μ) := by
    simp (disch := (apply integrable_sphere_continuous μ; fun_prop)) only [integral_add, integral_const_mul]
  have hnormpoly (x : S2) : ((x : E) 0)^4 + ((x : E) 0)^2 * ((x : E) 1)^2 +
      ((x : E) 0)^2 * ((x : E) 2)^2 = ((x : E) 0)^2 := by
    nlinarith [sphere_sq x]
  have hnorm := congrArg (fun f : S2 → ℝ => ∫ x, f x ∂μ) (funext hnormpoly)
  dsimp only at hnorm
  simp (disch := (apply integrable_sphere_continuous μ; fun_prop)) only [integral_add] at hnorm
  rw [coord_sq_integral μ hμ 0] at hnorm
  rw [hrotint, h31, h13, h4] at hrot
  rw [hm] at hnorm
  constructor <;> linarith

end Conjecture1030

namespace Conjecture1030

theorem evalOnSphere_monomial (d : Fin 3 →₀ ℕ) (c : ℝ) (x : S2) :
    evalOnSphere (MvPolynomial.monomial d c) x = c * sphereMonomial d x := by
  simp only [evalOnSphere, MvPolynomial.eval_monomial, sphereMonomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem evalOnSphere_as_sum (p : MvPolynomial (Fin 3) ℝ) (x : S2) :
    evalOnSphere p x = ∑ d ∈ p.support, p.coeff d * sphereMonomial d x := by
  classical
  calc
    evalOnSphere p x = evalOnSphere (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) x := by rw [← p.as_sum]
    _ = _ := by
      unfold evalOnSphere
      rw [MvPolynomial.eval_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact evalOnSphere_monomial d (p.coeff d) x

theorem designFor_of_monomial_exact (μ : Measure S2) [IsFiniteMeasure μ]
    (t : ℕ) (X : Finset S2) (hne : X.Nonempty)
    (hm : ∀ d : Fin 3 → ℕ, (∑ i, d i) ≤ t →
      (X.card : ℝ)⁻¹ * ∑ x ∈ X, sphereMonomial d x = ∫ x, sphereMonomial d x ∂μ) :
    DesignFor μ t X := by
  classical
  refine ⟨hne, fun p hp => ?_⟩
  simp_rw [evalOnSphere_as_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [integral_const_mul]
    have hd' : (∑ i, d i) ≤ t := by
      have hb := (MvPolynomial.le_totalDegree hd).trans hp
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hb
      exact hb
    rw [← hm d hd']
    ring
  · intro d hd
    exact (integrable_sphereMonomial μ d).const_mul _

end Conjecture1030

namespace Conjecture1030

theorem coord_fourth_integral (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) (i : Fin 3) :
    (∫ x : S2, ((x : E) i)^4 ∂μ) = 1 / 5 :=
  (coord_pow_integral_eq μ hμ i 0 4).trans (coord_fourth_mixed_integrals μ hμ).1

theorem coord_mixed_integral (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) (i j : Fin 3) (hij : i ≠ j) :
    (∫ x : S2, ((x : E) i)^2 * ((x : E) j)^2 ∂μ) = 1 / 15 :=
  (coord_mixed_integral_eq μ hμ i j hij).trans (coord_fourth_mixed_integrals μ hμ).2

theorem sphereMonomial_single (i : Fin 3) (n : ℕ) (x : S2) :
    sphereMonomial (Pi.single i n) x = ((x : E) i)^n := by
  fin_cases i <;> simp [sphereMonomial, Fin.prod_univ_succ, Pi.single_apply]

theorem coord_odd_integral (μ : Measure S2) (hμ : OrthogonallyInvariant μ)
    (i : Fin 3) (n : ℕ) (hn : Odd n) : (∫ x : S2, ((x : E) i)^n ∂μ) = 0 := by
  have h := sphereMonomial_integral_odd μ hμ (Pi.single i n) ⟨i, by simpa using hn⟩
  simpa only [sphereMonomial_single] using h

theorem coord_pow_integral_le_five (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) (i : Fin 3) (n : ℕ) (hn : n ≤ 5) :
    (∫ x : S2, ((x : E) i)^n ∂μ) =
      if n = 0 then 1 else if n = 2 then 1 / 3 else if n = 4 then 1 / 5 else 0 := by
  interval_cases n
  · simp
  · simpa using coord_odd_integral μ hμ i 1 (by norm_num [Nat.odd_iff])
  · simpa using coord_sq_integral μ hμ i
  · simpa using coord_odd_integral μ hμ i 3 (by norm_num [Nat.odd_iff])
  · simpa using coord_fourth_integral μ hμ i
  · simpa using coord_odd_integral μ hμ i 5 (by norm_num [Nat.odd_iff])

theorem sphereMonomial_integral (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) (d : Fin 3 → ℕ) (hd : (∑ i, d i) ≤ 5) :
    (∫ x, sphereMonomial d x ∂μ) = sphereMoment d := by
  classical
  by_cases ho : ∃ i, Odd (d i)
  · rw [sphereMonomial_integral_odd μ hμ d ho]
    simp [sphereMoment, ho]
  have h0 : d 0 = 0 ∨ d 0 = 2 ∨ d 0 = 4 := by
    have hn : ¬Odd (d 0) := fun h => ho ⟨0, h⟩
    simp only [Nat.odd_iff] at hn
    simp only [Fin.sum_univ_three] at hd
    omega
  have h1 : d 1 = 0 ∨ d 1 = 2 ∨ d 1 = 4 := by
    have hn : ¬Odd (d 1) := fun h => ho ⟨1, h⟩
    simp only [Nat.odd_iff] at hn
    simp only [Fin.sum_univ_three] at hd
    omega
  have h2 : d 2 = 0 ∨ d 2 = 2 ∨ d 2 = 4 := by
    have hn : ¬Odd (d 2) := fun h => ho ⟨2, h⟩
    simp only [Nat.odd_iff] at hn
    simp only [Fin.sum_univ_three] at hd
    omega
  simp only [Fin.sum_univ_three] at hd
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;> try omega
  all_goals simp only [sphereMoment, if_neg ho]
  all_goals simp [Fin.sum_univ_three, Fin.exists_fin_succ, h0, h1, h2]
  all_goals simp_rw [sphereMonomial, Fin.prod_univ_three, h0, h1, h2]
  all_goals simp only [pow_zero, mul_one, one_mul]
  all_goals first
    | solve | simp
    | simpa only [one_div] using coord_sq_integral μ hμ 0
    | simpa only [one_div] using coord_sq_integral μ hμ 1
    | simpa only [one_div] using coord_sq_integral μ hμ 2
    | simpa only [one_div] using coord_fourth_integral μ hμ 0
    | simpa only [one_div] using coord_fourth_integral μ hμ 1
    | simpa only [one_div] using coord_fourth_integral μ hμ 2
    | simpa only [one_div] using coord_mixed_integral μ hμ 0 1 (by decide)
    | simpa only [one_div] using coord_mixed_integral μ hμ 0 2 (by decide)
    | simpa only [one_div] using coord_mixed_integral μ hμ 1 2 (by decide)

theorem designFor_of_monomial_moments (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) (X : Finset S2) (hne : X.Nonempty)
    (hm : ∀ d : Fin 3 → ℕ, (∑ i, d i) ≤ 5 →
      (X.card : ℝ)⁻¹ * ∑ x ∈ X, sphereMonomial d x = sphereMoment d) :
    DesignFor μ 5 X := by
  apply designFor_of_monomial_exact μ 5 X hne
  intro d hd
  rw [sphereMonomial_integral μ hμ d hd]
  exact hm d hd

end Conjecture1030
