import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Tactic

noncomputable section

open Filter Topology
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace TLMC2704

instance prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

abbrev Q5 := ℚ_[5]

def forwardLinear : Q5 →L[Q5] Q5 := -(ContinuousLinearMap.id Q5 Q5)

def inverseLinear : Q5 →L[Q5] Q5 := forwardLinear

def f (x : Q5) : Q5 := forwardLinear x

def g (x : Q5) : Q5 := inverseLinear x

@[simp] theorem f_apply (x : Q5) : f x = -x := rfl
@[simp] theorem g_apply (x : Q5) : g x = -x := rfl

theorem left_inverse : Function.LeftInverse g f := by
  intro x
  simp

theorem right_inverse : Function.RightInverse g f := by
  intro x
  simp

def inverseHomeomorph : Q5 ≃ₜ Q5 where
  toFun := f
  invFun := g
  left_inv := left_inverse
  right_inv := right_inverse
  continuous_toFun := forwardLinear.continuous
  continuous_invFun := inverseLinear.continuous

def inverseSeries : FormalMultilinearSeries Q5 Q5 Q5 :=
  inverseLinear.fpowerSeries 0

theorem inverseSeries_radius : inverseSeries.radius = ∞ :=
  inverseLinear.fpowerSeries_radius 0

theorem inverse_series_represents :
    HasFPowerSeriesOnBall g inverseSeries 0 ∞ :=
  inverseLinear.hasFPowerSeriesOnBall 0

theorem inverse_analytic (x : Q5) : AnalyticAt Q5 g x :=
  inverseLinear.analyticAt x

theorem forward_hasStrictDerivAt (x : Q5) : HasStrictDerivAt f (-1) x := by
  exact hasStrictDerivAt_neg x

theorem forward_deriv (x : Q5) : deriv f x = -1 :=
  (forward_hasStrictDerivAt x).hasDerivAt.deriv

theorem forward_deriv_nonzero (x : Q5) : deriv f x ≠ 0 := by
  rw [forward_deriv]
  norm_num

theorem multiplier_norm (x : Q5) : ‖deriv f x‖ = 1 := by
  rw [forward_deriv]
  simp

theorem iterate_even (n : ℕ) (x : Q5) : (g^[2 * n]) x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply]
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, g_apply,
      neg_neg] using ih

theorem iterate_odd (n : ℕ) (x : Q5) : (g^[2 * n + 1]) x = -x := by
  rw [Function.iterate_succ_apply']
  simp only [iterate_even, g_apply]

theorem even_cofinal : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  have h : StrictMono (fun n : ℕ => 2 * n) := by
    intro a b hab
    change 2 * a < 2 * b
    omega
  exact h.tendsto_atTop

theorem odd_cofinal : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
  have h : StrictMono (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 < 2 * b + 1
    omega
  exact h.tendsto_atTop

theorem no_iterate_limit {x : Q5} (hx : x ≠ 0) :
    ∀ y : Q5, ¬ Tendsto (fun n : ℕ => (g^[n]) x) atTop (𝓝 y) := by
  intro y hy
  have he := hy.comp even_cofinal
  have ho := hy.comp odd_cofinal
  simp only [Function.comp_def, iterate_even] at he
  simp only [Function.comp_def, iterate_odd] at ho
  have hyx : y = x := tendsto_nhds_unique he tendsto_const_nhds
  have hys : y = -x := tendsto_nhds_unique ho tendsto_const_nhds
  have hxs : x = -x := hyx.symm.trans hys
  have hzero : (2 : Q5) * x = 0 := by
    calc
      (2 : Q5) * x = x + x := by ring
      _ = x + (-x) := congrArg (fun z : Q5 => x + z) hxs
      _ = 0 := add_neg_cancel x
  rcases mul_eq_zero.mp hzero with h | h
  · norm_num at h
  · exact hx h

theorem iterate_norm (n : ℕ) (x : Q5) : ‖(g^[n]) x‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', g_apply, norm_neg]
    exact ih

theorem arbitrarily_small_nonzero (r : ℝ) (hr : 0 < r) :
    ∃ x : Q5, x ≠ 0 ∧ ‖x‖ < r := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (Padic.norm_p_lt_one (p := 5))
  refine ⟨(5 : Q5) ^ n, pow_ne_zero n (by norm_num), ?_⟩
  simpa only [norm_pow, Nat.cast_ofNat] using hn

theorem arbitrarily_small_nonconvergent_orbit (r : ℝ) (hr : 0 < r) :
    ∃ x : Q5, x ≠ 0 ∧ x ∈ Metric.ball 0 r ∧
      (∀ n : ℕ, (g^[n]) x ∈ Metric.ball 0 r) ∧
      ∀ y : Q5, ¬ Tendsto (fun n : ℕ => (g^[n]) x) atTop (𝓝 y) := by
  obtain ⟨x, hx, hxr⟩ := arbitrarily_small_nonzero r hr
  refine ⟨x, hx, ?_, ?_, no_iterate_limit hx⟩
  · simpa only [Metric.mem_ball, dist_zero_right] using hxr
  · intro n
    simpa only [Metric.mem_ball, dist_zero_right, iterate_norm] using hxr

theorem counterexample :
    Function.LeftInverse g f ∧ Function.RightInverse g f ∧
    inverseSeries.radius = ∞ ∧ HasFPowerSeriesOnBall g inverseSeries 0 ∞ ∧
    (∀ x : Q5, deriv f x ≠ 0 ∧ ‖deriv f x‖ = 1) ∧
    ∀ r : ℝ, 0 < r → ∃ x : Q5, x ≠ 0 ∧ x ∈ Metric.ball 0 r ∧
      (∀ n : ℕ, (g^[n]) x ∈ Metric.ball 0 r) ∧
      ∀ y : Q5, ¬ Tendsto (fun n : ℕ => (g^[n]) x) atTop (𝓝 y) := by
  exact ⟨left_inverse, right_inverse, inverseSeries_radius, inverse_series_represents,
    fun x => ⟨forward_deriv_nonzero x, multiplier_norm x⟩,
    arbitrarily_small_nonconvergent_orbit⟩

end TLMC2704

