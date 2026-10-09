import Bergman930.MeanValue

noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped ENNReal Topology Real
namespace Bergman930

/-- A fixed finite Cauchy--Schwarz constant, namely the L² norm of 1. -/
def areaConstant : ℝ := ‖(memLp_const (p := (2 : ℝ≥0∞)) (μ := area) (1 : ℝ)).toLp
  (fun _ : ℂ => (1 : ℝ))‖

theorem integral_norm_le (f : A2) : (∫ z, ‖f z‖ ∂area) ≤ areaConstant * ‖toL2 f‖ := by
  let u : Lp ℝ 2 area := (memLp_const 1).toLp (fun _ => (1 : ℝ))
  let v : Lp ℝ 2 area := (square_integrable f).norm.toLp (fun z => ‖f z‖)
  have hi : @inner ℝ _ _ u v = ∫ z, ‖f z‖ ∂area := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (p := (2 : ℝ≥0∞)) (μ := area) (1 : ℝ)).coeFn_toLp,
      (square_integrable f).norm.coeFn_toLp] with z hu hv
    simp only [u, v, hu, hv, RCLike.inner_apply, conj_trivial, one_mul, mul_one]
  have hv : ‖v‖ = ‖toL2 f‖ := by
    rw [show v = (square_integrable f).norm.toLp (fun z => ‖f z‖) from rfl,
      show toL2 f = (square_integrable f).toLp f from rfl,
      Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
  have hcs := real_inner_le_norm u v
  rw [hi, hv] at hcs
  exact hcs

/-- Point evaluation is controlled by the genuine area-L² norm. -/
theorem evaluation_bound (f : A2) (w : ℂ) (R : ℝ) (hR : 0 < R)
    (hball : closedBall w R ⊆ disk) :
    ‖f w‖ ≤ (areaConstant / (π * R ^ 2)) * ‖toL2 f‖ := by
  have hmean := disk_mean f w R hR ((holomorphic f).mono hball)
  have hc : 0 < π * R ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hR)
  have hle : (π * R ^ 2) * ‖f w‖ ≤ areaConstant * ‖toL2 f‖ := by
    calc
      (π * R ^ 2) * ‖f w‖ = ‖∫ z in ball w R, f z‖ := by
        rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      _ ≤ ∫ z in ball w R, ‖f z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, ‖f z‖ ∂area := by
        exact integral_mono_measure (Measure.restrict_mono_set _
          (ball_subset_closedBall.trans hball)) (ae_of_all _ (fun z => norm_nonneg (f z)))
          ((square_integrable f).integrable (by norm_num)).norm
      _ ≤ areaConstant * ‖toL2 f‖ := integral_norm_le f
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm ‖f w‖] using hle

end Bergman930
