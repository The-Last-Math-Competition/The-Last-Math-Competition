import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

namespace TLMC821

abbrev FlatCircle := AddCircle (2 * Real.pi)

def frequency (n : ℕ) : ℝ := (n + 1 : ℕ)
noncomputable def u (n : ℕ) (x : ℝ) := Real.sin (frequency n * x)
noncomputable def du (n : ℕ) (x : ℝ) := frequency n * Real.cos (frequency n * x)

theorem frequency_pos (n : ℕ) : 0 < frequency n := by
  unfold frequency
  positivity

theorem u_periodic (n : ℕ) : Function.Periodic (u n) (2 * Real.pi) := by
  intro x
  simp only [u, frequency, mul_add]
  exact Real.sin_add_nat_mul_two_pi _ (n + 1)

theorem du_periodic (n : ℕ) : Function.Periodic (du n) (2 * Real.pi) := by
  intro x
  simp only [du, frequency, mul_add, Real.cos_add_nat_mul_two_pi]

noncomputable def circleU (n : ℕ) : FlatCircle → ℝ := (u_periodic n).lift
noncomputable def circleD (n : ℕ) : FlatCircle → ℝ := (du_periodic n).lift

@[simp] theorem circleU_coe (n : ℕ) (x : ℝ) : circleU n (x : FlatCircle) = u n x :=
  Function.Periodic.lift_coe _ _

@[simp] theorem circleD_coe (n : ℕ) (x : ℝ) : circleD n (x : FlatCircle) = du n x :=
  Function.Periodic.lift_coe _ _

theorem circleU_continuous (n : ℕ) : Continuous (circleU n) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
  change Continuous (u n)
  exact Real.continuous_sin.comp (continuous_const.mul continuous_id)

theorem circleD_continuous (n : ℕ) : Continuous (circleD n) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
  change Continuous (du n)
  exact continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

theorem circleU_smooth_pullback (n : ℕ) :
    ContDiff ℝ ⊤ (fun x : ℝ => circleU n (x : FlatCircle)) := by
  change ContDiff ℝ ⊤ (fun x : ℝ => Real.sin (frequency n * x))
  fun_prop

theorem circleU_nonzero (n : ℕ) : ∃ z : FlatCircle, circleU n z ≠ 0 := by
  refine ⟨((Real.pi / (2 * frequency n) : ℝ) : FlatCircle), ?_⟩
  have hn : frequency n ≠ 0 := ne_of_gt (frequency_pos n)
  have he : frequency n * (Real.pi / (2 * frequency n)) = Real.pi / 2 := by
    field_simp
  simp [u, he]

theorem first_derivative (n : ℕ) (x : ℝ) : HasDerivAt (u n) (du n x) x := by
  change HasDerivAt (fun y => Real.sin (frequency n * y))
    (frequency n * Real.cos (frequency n * x)) x
  convert (Real.hasDerivAt_sin (frequency n * x)).comp x
      ((hasDerivAt_id x).const_mul (frequency n)) using 1 <;> first | rfl | simp [mul_comm]

theorem second_derivative (n : ℕ) (x : ℝ) :
    HasDerivAt (du n) (-frequency n ^ 2 * u n x) x := by
  change HasDerivAt (fun y => frequency n * Real.cos (frequency n * y))
    (-frequency n ^ 2 * Real.sin (frequency n * x)) x
  convert ((Real.hasDerivAt_cos (frequency n * x)).comp x
      ((hasDerivAt_id x).const_mul (frequency n))).const_mul (frequency n) using 1 <;> first | rfl | simp [pow_two, mul_assoc, mul_comm]

/-- Arc-length coordinates on R/(2 pi Z) identify the positive Laplacian with -d²/dx².
The derivative field is constrained by genuine derivatives of the quotient pullbacks. -/
def CircleEigenpair (lam : ℝ) (f df : FlatCircle → ℝ) : Prop :=
  0 < lam ∧ Continuous f ∧ Continuous df ∧ (∃ z, f z ≠ 0) ∧
  ContDiff ℝ ⊤ (fun x : ℝ => f (x : FlatCircle)) ∧
  (∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : FlatCircle)) (df (x : FlatCircle)) x) ∧
  (∀ x : ℝ, HasDerivAt (fun y : ℝ => df (y : FlatCircle))
    (-lam * f (x : FlatCircle)) x)

theorem circle_eigenpair (n : ℕ) :
    CircleEigenpair (frequency n ^ 2) (circleU n) (circleD n) := by
  refine ⟨sq_pos_of_pos (frequency_pos n), circleU_continuous n, circleD_continuous n,
    circleU_nonzero n, circleU_smooth_pullback n, ?_, ?_⟩
  · intro x
    simpa only [circleU_coe, circleD_coe] using first_derivative n x
  · intro x
    simpa only [circleU_coe, circleD_coe] using second_derivative n x

theorem max_value (n : ℕ) : IsGreatest (Set.range fun z => |circleU n z|) 1 := by
  refine ⟨?_, ?_⟩
  · refine ⟨((Real.pi / (2 * frequency n) : ℝ) : FlatCircle), ?_⟩
    have hn : frequency n ≠ 0 := ne_of_gt (frequency_pos n)
    have he : frequency n * (Real.pi / (2 * frequency n)) = Real.pi / 2 := by
      field_simp
    simp [u, he]
  · rintro y ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    simp only [circleU_coe, u]
    exact Real.abs_sin_le_one _

theorem max_gradient (n : ℕ) :
    IsGreatest (Set.range fun z => |circleD n z|) (frequency n) := by
  refine ⟨?_, ?_⟩
  · refine ⟨((0 : ℝ) : FlatCircle), ?_⟩
    change |du n 0| = frequency n
    simp [du, abs_of_pos (frequency_pos n)]
  · rintro y ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    simp only [circleD_coe, du, abs_mul, abs_of_pos (frequency_pos n)]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (frequency n * x))
      (le_of_lt (frequency_pos n))

theorem eigenfunction_ratio (n : ℕ) :
    frequency n / (frequency n ^ 2 * 1) = 1 / frequency n := by
  have hn : frequency n ≠ 0 := ne_of_gt (frequency_pos n)
  field_simp

theorem arbitrarily_small_ratios (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, frequency n / (frequency n ^ 2 * 1) < c := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  refine ⟨n, ?_⟩
  rw [eigenfunction_ratio]
  simpa [frequency, Nat.cast_add, Nat.cast_one] using hn

theorem arbitrarily_small_ratios_after (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ frequency n / (frequency n ^ 2 * 1) < c := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  refine ⟨N + n, Nat.le_add_right N n, ?_⟩
  rw [eigenfunction_ratio]
  apply lt_of_le_of_lt ?_ hn
  apply one_div_le_one_div_of_le (by positivity)
  simp only [frequency, Nat.cast_add, Nat.cast_one]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

theorem no_uniform_positive_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (lam : ℝ) (f df : FlatCircle → ℝ),
      CircleEigenpair lam f df → ∀ A B : ℝ,
      IsGreatest (Set.range fun z => |f z|) A →
      IsGreatest (Set.range fun z => |df z|) B → c ≤ B / (lam * A) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn⟩ := arbitrarily_small_ratios c hc
  exact (not_lt_of_ge (h (frequency n ^ 2) (circleU n) (circleD n)
    (circle_eigenpair n) 1 (frequency n) (max_value n) (max_gradient n))) hn

end TLMC821
