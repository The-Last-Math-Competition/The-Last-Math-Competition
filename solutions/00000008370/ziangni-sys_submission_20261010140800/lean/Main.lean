import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

noncomputable section
namespace MetricGreen
open Set Filter

-- The connected metrized graph is the interval [0,r] with its real distance.
abbrev Segment (r : ℝ) := ↥(Set.Icc (0 : ℝ) r)

def green (r x y : ℝ) : ℝ := r / 4 - |x - y| / 2

theorem left_derivative (r x y : ℝ) (h : x < y) :
    HasDerivAt (fun z => green r z y) (1/2) x := by
  have ha : HasDerivAt (fun z : ℝ => r/4 + (z-y)/2) (1/2) x := by
    convert (hasDerivAt_const x (r/4)).add (((hasDerivAt_id x).sub_const y).div_const 2) using 1 <;> norm_num
  apply ha.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds h] with z hz
  dsimp [green]
  rw [abs_of_neg (sub_neg.mpr hz)]
  ring

theorem right_derivative (r x y : ℝ) (h : y < x) :
    HasDerivAt (fun z => green r z y) (-1/2) x := by
  have ha : HasDerivAt (fun z : ℝ => r/4 - (z-y)/2) (-1/2) x := by
    convert (hasDerivAt_const x (r/4)).sub (((hasDerivAt_id x).sub_const y).div_const 2) using 1 <;> norm_num
  apply ha.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds h] with z hz
  dsimp [green]
  rw [abs_of_pos (sub_pos.mpr hz)]

-- Endpoint fluxes are the actual constant derivatives of the adjacent pieces.
def leftFlux (r y : ℝ) := deriv (fun x => green r x y) (if y = 0 then r/2 else y/2)
def rightFlux (r y : ℝ) := deriv (fun x => green r x y) (if y = r then r/2 else (y+r)/2)

theorem leftFlux_formula (r y : ℝ) (hr : 0 < r) (hy : y ∈ Icc 0 r) :
    leftFlux r y = if y = 0 then -1/2 else 1/2 := by
  by_cases h : y = 0
  · subst y
    simp only [leftFlux, if_pos rfl]
    exact (right_derivative r (r/2) 0 (by linarith)).deriv
  · simp only [leftFlux, if_neg h]
    exact (left_derivative r (y/2) y (by rcases hy with ⟨a,b⟩; have := lt_of_le_of_ne a (Ne.symm h); linarith)).deriv

theorem rightFlux_formula (r y : ℝ) (hr : 0 < r) (hy : y ∈ Icc 0 r) :
    rightFlux r y = if y = r then 1/2 else -1/2 := by
  by_cases h : y = r
  · subst y
    simp only [rightFlux, if_pos rfl]
    exact (left_derivative r (r/2) r (by linarith)).deriv
  · simp only [rightFlux, if_neg h]
    exact (right_derivative r ((y+r)/2) y (by rcases hy with ⟨a,b⟩; have := lt_of_le_of_ne b h; linarith)).deriv

-- Distributional graph Laplacian of a piecewise affine function:
-- minus outward endpoint slopes and minus its interior derivative jump.
-- This functional on arbitrary test functions represents a finite signed measure.
def laplacianAction (r y : ℝ) (test : ℝ → ℝ) : ℝ :=
  -leftFlux r y * test 0 + rightFlux r y * test r +
    (if y = 0 ∨ y = r then 0 else leftFlux r y - rightFlux r y) * test y

theorem laplacian_identity (r y : ℝ) (hr : 0 < r) (hy : y ∈ Icc 0 r)
    (test : ℝ → ℝ) :
    laplacianAction r y test = test y - (test 0 + test r)/2 := by
  unfold laplacianAction
  rw [leftFlux_formula r y hr hy, rightFlux_formula r y hr hy]
  by_cases h0 : y = 0
  · subst y
    simp [ne_of_gt hr, Ne.symm (ne_of_gt hr)]
    ring
  · by_cases hR : y = r
    · subst y
      simp [ne_of_gt hr]
      ring
    · simp [h0, hR]
      ring

-- Canonical measure is endpoint mass1/2+1/2, so this is its exact integral.
theorem canonical_mean_zero (r y : ℝ) (hy : y ∈ Icc 0 r) :
    (green r 0 y + green r r y)/2 = 0 := by
  rcases hy with ⟨a,b⟩
  rw [green, green, abs_of_nonpos (by linarith : (0:ℝ)-y ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ r-y)]
  ring

theorem symmetric (r x y : ℝ) : green r x y = green r y x := by
  simp only [green, abs_sub_comm]

def length : ℝ := 1/2

theorem length_positive : 0 < length := by norm_num [length]
theorem length_nonintegral : ¬ ∃ z : ℤ, (z : ℝ) = length := by
  rintro ⟨z,h⟩
  have h0 : 0 < z := by exact_mod_cast (show (0:ℝ) < z by rw [h]; norm_num [length])
  have h1 : z < 1 := by exact_mod_cast (show (z:ℝ) < 1 by rw [h]; norm_num [length])
  omega

theorem diagonal_value : green length 0 0 = (1/8 : ℝ) := by norm_num [green,length]
theorem diagonal_algebraic : IsAlgebraic ℚ (green length 0 0) := by
  rw [diagonal_value]
  convert isAlgebraic_rat ℚ (1/8 : ℚ) using 1 <;> norm_num

theorem counterexample : 0 < length ∧ (¬ ∃ z : ℤ, (z:ℝ) = length) ∧
    IsAlgebraic ℚ (green length 0 0) ∧ green length 0 0 ≠ 0 := by
  exact ⟨length_positive, length_nonintegral, diagonal_algebraic, by rw [diagonal_value]; norm_num⟩

#print axioms left_derivative
#print axioms right_derivative
#print axioms laplacian_identity
#print axioms canonical_mean_zero
#print axioms counterexample
end MetricGreen
