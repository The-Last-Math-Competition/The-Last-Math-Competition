import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Conjecture7991

/-- A lower-bounded real graph cannot have derivative at most -1 on a whole tail.
The proof uses the actual real mean value theorem, not discrete finite differences. -/
theorem not_eventually_deriv_le_neg_one (f : ℝ → ℝ)
    (hlower : ∃ L : ℝ, ∀ᶠ p in atTop, L ≤ f p) :
    ¬ (∀ᶠ p in atTop, deriv f p ≤ -1) := by
  intro hderiv
  obtain ⟨L, hL⟩ := hlower
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hL.and hderiv)
  have hdiff : ∀ p : ℝ, a ≤ p → DifferentiableAt ℝ f p := by
    intro p hp
    by_contra hn
    have hd := (ha p hp).2
    rw [deriv_zero_of_not_differentiableAt hn] at hd
    norm_num at hd
  let b : ℝ := a + (f a - L) + 1
  have hfa : L ≤ f a := (ha a le_rfl).1
  have hab : a < b := by dsimp [b]; linarith
  have hc : ContinuousOn f (Icc a b) := by
    intro p hp
    exact (hdiff p hp.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (Ioo a b) := by
    intro p hp
    exact (hdiff p hp.1.le).differentiableWithinAt
  obtain ⟨c, hcI, hcSlope⟩ := exists_deriv_eq_slope f hab hc hd
  have hcBound := (ha c hcI.1.le).2
  rw [hcSlope] at hcBound
  have hdec : f b - f a ≤ -(b-a) := by
    have := (div_le_iff₀ (sub_pos.mpr hab)).mp hcBound
    linarith
  have hfb : L ≤ f b := (ha b hab.le).1
  dsimp [b] at hdec hfb
  linarith

/-- In particular, negative-infinite slopes at p=infinity are impossible for any
eventually lower-bounded graph, with no prior differentiability assumption. -/
theorem no_negative_infinite_slope_of_bddBelow (f : ℝ → ℝ)
    (hlower : ∃ L : ℝ, ∀ᶠ p in atTop, L ≤ f p) :
    ¬ Tendsto (deriv f) atTop atBot := by
  intro hslope
  exact not_eventually_deriv_le_neg_one f hlower
    (hslope.eventually (eventually_le_atBot (-1 : ℝ)))

/-- The natural nonnegative range of a regularity exponent already contradicts
the conjecture's asserted derivative limit at p=infinity. -/
theorem no_nonnegative_regularity_exponent_cusp (α : ℝ → ℝ)
    (hα : ∀ p : ℝ, 2 < p → 0 ≤ α p) :
    ¬ Tendsto (deriv α) atTop atBot := by
  apply no_negative_infinite_slope_of_bddBelow α
  refine ⟨0, ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with p hp
  exact hα p hp

/-- A formulation with a nonnegative codomain, rather than a separately supplied
nonnegativity hypothesis. No PDE-specific exponent formula is assumed. -/
theorem no_nnreal_regularity_exponent_cusp (α : ℝ → ℝ≥0) :
    ¬ Tendsto (deriv (fun p => (α p : ℝ))) atTop atBot := by
  apply no_nonnegative_regularity_exponent_cusp
  intro p _
  exact (α p).coe_nonneg

/-- Direct negation of the two necessary conditions from the source conjecture. -/
theorem conjecture_cusp_impossible :
    ¬ ∃ α : ℝ → ℝ,
      (∀ p : ℝ, 2 < p → 0 ≤ α p) ∧ Tendsto (deriv α) atTop atBot := by
  rintro ⟨α, hα, hslope⟩
  exact no_nonnegative_regularity_exponent_cusp α hα hslope

/-- The exact scalar expression in the conjecture, with its displayed constant parameter. -/
def proposedFormula (ell : ℝ) (p : ℝ) : ℝ :=
  min ((p-1) / (2*p-2+p*ell)) (1 / (p-1))

lemma parameter_gt_neg_two {ell : ℝ} (hα : 0 ≤ proposedFormula ell 3) : -2 < ell := by
  by_contra h
  have hell : ell ≤ -2 := le_of_not_gt h
  have hden : 4 + 3*ell < 0 := by linarith
  have hfirst : 2 / (4+3*ell) < 0 := div_neg_of_pos_of_neg (by norm_num) hden
  have hm : proposedFormula ell 3 ≤ 2 / (4+3*ell) := by
    unfold proposedFormula
    norm_num only [show (3 : ℝ)-1 = 2 by norm_num, show 2*(3 : ℝ)-2 = 4 by norm_num]
    exact min_le_left _ _
  linarith

/-- The formula has a single reciprocal branch on a genuine open real tail. -/
theorem formula_eventually_reciprocal {ell : ℝ} (hell : -2 < ell) :
    ∃ A : ℝ, ∀ p : ℝ, A < p → proposedFormula ell p = 1/(p-1) := by
  let c := ell + 2
  have hc : 0 < c := by dsimp [c]; linarith
  let A := max 3 (max (ell+5) (4/c))
  refine ⟨A, fun p hp => ?_⟩
  have hp3 : 3 < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hpell : ell+5 < p := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp
  have hp4 : 4/c < p := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp
  have hcp : 4 < p*c := (div_lt_iff₀ hc).mp hp4
  have hden : 0 < 2*p-2+p*ell := by dsimp [c] at hcp; nlinarith
  have hpm : 0 < p-1 := by linarith
  have hprod : 0 ≤ p * (p-ell-4) := mul_nonneg (by linarith) (by linarith)
  have hcomp : 1/(p-1) ≤ (p-1)/(2*p-2+p*ell) := by
    apply (div_le_div_iff₀ hpm hden).mpr
    nlinarith
  exact min_eq_right hcomp

/-- The source's scalar formula actually has derivative tending to zero, not minus infinity. -/
theorem formula_derivative_tends_zero {ell : ℝ} (hell : -2 < ell) :
    Tendsto (deriv (proposedFormula ell)) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := formula_eventually_reciprocal hell
  have heq : ∀ᶠ p : ℝ in atTop,
      deriv (proposedFormula ell) p = -((p-1)⁻¹)^2 := by
    filter_upwards [eventually_gt_atTop (max A 2)] with p hp
    have hpA : A < p := lt_of_le_of_lt (le_max_left _ _) hp
    have hp2 : 2 < p := lt_of_le_of_lt (le_max_right _ _) hp
    have hloc : proposedFormula ell =ᶠ[𝓝 p] (fun q : ℝ => 1/(q-1)) := by
      filter_upwards [Ioi_mem_nhds hpA] with q hq
      exact hA q hq
    rw [hloc.deriv_eq]
    have hd := ((hasDerivAt_id p).sub_const 1).inv (by linarith : p-1 ≠ 0)
    have hdr : deriv (fun q : ℝ => 1/(q-1)) p = -1/(p-1)^2 := by
      simpa only [one_div] using hd.deriv
    rw [hdr]
    simp only [one_div, inv_pow, neg_div, neg_mul, one_mul]
  have ht : Tendsto (fun p : ℝ => p-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with p hp
    linarith
  have hi : Tendsto (fun p : ℝ => (p-1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hz : Tendsto (fun p : ℝ => -((p-1)⁻¹)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero] using (hi.pow 2).neg
  have hEq : deriv (proposedFormula ell) =ᶠ[atTop] (fun p : ℝ => -((p-1)⁻¹)^2) := heq
  exact hz.congr' hEq.symm

/-- The formula supplies its own tail differentiability; no singular-function convention
or extra smoothness hypothesis is needed to expose its incompatible slope assertion. -/
theorem proposed_formula_cusp_impossible {ell : ℝ} (hα : 0 ≤ proposedFormula ell 3) :
    ¬ Tendsto (deriv (proposedFormula ell)) atTop atBot := by
  have hz := formula_derivative_tends_zero (parameter_gt_neg_two hα)
  intro hbot
  have hlo : ∀ᶠ p : ℝ in atTop, (-1 : ℝ) < deriv (proposedFormula ell) p :=
    hz.eventually (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))
  have hhi : ∀ᶠ p : ℝ in atTop, deriv (proposedFormula ell) p ≤ -1 :=
    hbot.eventually (eventually_le_atBot (-1 : ℝ))
  obtain ⟨p, hp, hp'⟩ := (hlo.and hhi).exists
  exact (not_lt_of_ge hp') hp

#print axioms not_eventually_deriv_le_neg_one
#print axioms no_negative_infinite_slope_of_bddBelow
#print axioms no_nonnegative_regularity_exponent_cusp
#print axioms no_nnreal_regularity_exponent_cusp
#print axioms conjecture_cusp_impossible
#print axioms formula_eventually_reciprocal
#print axioms formula_derivative_tends_zero
#print axioms proposed_formula_cusp_impossible

end Conjecture7991

