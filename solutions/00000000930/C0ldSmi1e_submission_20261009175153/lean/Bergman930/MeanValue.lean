import Bergman930.Geometry
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped ENNReal Topology Real
namespace Bergman930

/-- Cauchy's formula in mean-value form on a circle, before radial integration. -/
theorem circle_mean (f : ℂ → ℂ) (w : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall w r)) :
    (∫ θ in (0)..2 * π, f (circleMap w r θ)) = (2 * π : ℂ) * f w := by
  have h := hf.circleIntegral_sub_inv_smul (mem_ball_self hr)
  have hrew : (∮ z in C(w, r), (z - w)⁻¹ • f z) =
      I * ∫ θ in (0)..2 * π, f (circleMap w r θ) := by
    simp only [circleIntegral, deriv_circleMap, smul_smul, smul_eq_mul]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hn : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
    field_simp [hn]
    ring
  rw [hrew, smul_eq_mul] at h
  apply mul_left_cancel₀ I_ne_zero
  rw [h]
  ring

theorem circle_mean_symmetric (f : ℂ → ℂ) (w : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall w r)) :
    (∫ θ in (-π)..π, f (circleMap w r θ)) = (2 * π : ℂ) * f w := by
  let F : ℝ → ℂ := fun θ => f (circleMap w r θ)
  have hc : Continuous F := hf.continuousOn.comp_continuous
    (continuous_const.add (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))))
    (fun θ => circleMap_mem_closedBall w hr.le θ)
  have hp : Function.Periodic F (2 * π) := (periodic_circleMap w r).comp f
  have hshift : (∫ θ in (-π)..0, F θ) = ∫ θ in π..2 * π, F θ := by
    calc
      (∫ θ in (-π)..0, F θ) = ∫ θ in (-π)..0, F (θ + 2 * π) := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact (hp θ).symm
      _ = ∫ θ in π..2 * π, F θ := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 1 <;> ring
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-π) 0) (hc.intervalIntegrable (μ := volume) 0 π)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 π) (hc.intervalIntegrable (μ := volume) π (2 * π))
  change (∫ θ in (-π)..π, F θ) = _
  rw [← h1, hshift, add_comm, h2]
  exact circle_mean f w r hr hf

theorem polar_eq_circle (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

/-- The polar-coordinate formula specialized to an open disk. -/
theorem integral_ball_polar (f : ℂ → ℂ) (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, f z) =
      ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, p.1 • f (circleMap 0 p.1 p.2) := by
  rw [← integral_indicator measurableSet_ball,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  rw [← integral_indicator (isOpen_Ioi.prod isOpen_Ioo).measurableSet,
    ← integral_indicator (isOpen_Ioo.prod isOpen_Ioo).measurableSet]
  apply integral_congr_ae
  filter_upwards with p
  have hnorm : circleMap 0 p.1 p.2 ∈ ball (0 : ℂ) R ↔ |p.1| < R := by simp
  simp only [Complex.polarCoord_target, polarCoord_target, polar_eq_circle]
  by_cases h0 : 0 < p.1
  · by_cases ht : p.2 ∈ Ioo (-π) π
    · by_cases hR : p.1 < R
      · simp [h0, ht, hR, hnorm, abs_of_pos h0]
      · simp [h0, ht, hR, hnorm, abs_of_pos h0]
    · simp [h0, ht]
  · simp [h0]

/-- The area mean-value formula on a centered disk. -/
theorem disk_mean_zero (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R)) :
    (∫ z in ball (0 : ℂ) R, f z) = (π * R ^ 2 : ℝ) • f 0 := by
  let F : ℝ × ℝ → ℂ := fun p => p.1 • f (circleMap 0 p.1 p.2)
  have hcirc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
      (Icc 0 R ×ˢ Icc (-π) π) (closedBall (0 : ℂ) R) := by
    intro p hp
    simpa [abs_of_nonneg hp.1.1] using hp.1.2
  have hc : ContinuousOn F (Icc 0 R ×ˢ Icc (-π) π) :=
    continuous_fst.continuousOn.smul (hf.continuousOn.comp hcirc.continuousOn hmaps)
  have hint : IntegrableOn F (Ioo 0 R ×ˢ Ioo (-π) π) (volume.prod volume) :=
    (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [integral_ball_polar]
  change (∫ p in Ioo 0 R ×ˢ Ioo (-π) π, F p) = _
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod F hint]
  have hmean (r : ℝ) (hr : r ∈ Ioo 0 R) :
      (∫ θ in Ioo (-π) π, F (r, θ)) = r • ((2 * π : ℂ) * f 0) := by
    dsimp [F]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [circle_mean_symmetric f 0 r hr.1
      (hf.mono (closedBall_subset_closedBall hr.2.le))]
  rw [setIntegral_congr_fun measurableSet_Ioo hmean, integral_smul_const]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_id]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_mul]
  ring

theorem disk_mean (f : ℂ → ℂ) (w : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall w R)) :
    (∫ z in ball w R, f z) = (π * R ^ 2 : ℝ) • f w := by
  have hg : DifferentiableOn ℂ (fun z => f (w + z)) (closedBall (0 : ℂ) R) :=
    hf.comp (differentiableOn_const w |>.add differentiableOn_id) (by
      intro z hz
      simpa only [mem_closedBall_iff_norm, add_sub_cancel_left, sub_zero] using hz)
  have hi := (measurePreserving_add_left (volume : Measure ℂ) w).integral_comp
    (Homeomorph.addLeft w).measurableEmbedding ((ball w R).indicator f)
  have hid : (fun z => (ball w R).indicator f (w + z)) =
      (ball (0 : ℂ) R).indicator (fun z => f (w + z)) := by
    funext z
    simp only [indicator, mem_ball_iff_norm, add_sub_cancel_left, sub_zero]
  rw [hid, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at hi
  rw [← hi, disk_mean_zero _ R hR hg, add_zero]

end Bergman930
