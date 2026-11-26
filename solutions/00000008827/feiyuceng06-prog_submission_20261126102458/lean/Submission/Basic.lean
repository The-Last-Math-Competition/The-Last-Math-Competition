import Mathlib

namespace Submission00000008827

abbrev Support := Set.Icc (-2 : ℝ) 1

def sample : Support := ⟨0, by constructor <;> norm_num⟩
def endpoint : Support := ⟨1, by constructor <;> norm_num⟩

def loss (z : Support) : ℝ := (z : ℝ) + 2

/-- The loss averaged over the one-sample empirical distribution. -/
def empiricalRisk : ℝ := loss sample

/-- Dual integrand for the 1-Wasserstein ball centered at the point mass at sample. -/
noncomputable def integrand (multiplier : ℝ) (z : Support) : ℝ :=
  loss z - multiplier * dist (z : ℝ) (sample : ℝ)

/-- Standard transport dual with one sample and ground cost |z - sample|. -/
noncomputable def transportDual (radius : ℝ) : ℝ :=
  sInf {v | ∃ multiplier : ℝ, 0 ≤ multiplier ∧
    v = multiplier * radius + sSup (Set.range (integrand multiplier))}

private theorem integrand_le (multiplier : ℝ) (hMultiplier : 0 ≤ multiplier) (z : Support) :
    integrand multiplier z ≤ 3 := by
  have hz : (z : ℝ) ≤ 1 := z.property.2
  unfold integrand loss
  linarith [mul_nonneg hMultiplier (dist_nonneg (x := (z : ℝ)) (y := (sample : ℝ)))]

private theorem integrand_endpoint (multiplier : ℝ) : integrand multiplier endpoint = 3 - multiplier := by
  norm_num [integrand, loss, endpoint, sample, Real.dist_eq]

private theorem sup_integrand_zero : sSup (Set.range (integrand 0)) = 3 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨endpoint, by rw [integrand_endpoint]; norm_num⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact integrand_le 0 le_rfl z

private theorem endpoint_le_sup (multiplier : ℝ) (hMultiplier : 0 ≤ multiplier) :
    3 - multiplier ≤ sSup (Set.range (integrand multiplier)) := by
  rw [← integrand_endpoint]
  apply le_csSup
  · exact ⟨3, by rintro _ ⟨z, rfl⟩; exact integrand_le multiplier hMultiplier z⟩
  · exact ⟨endpoint, rfl⟩

/-- The transport dual already saturates at radius one. -/
theorem dual_eq_three (radius : ℝ) (hradius : 1 ≤ radius) :
    transportDual radius = 3 := by
  unfold transportDual
  apply IsLeast.csInf_eq
  refine ⟨⟨0, le_rfl, ?_⟩, ?_⟩
  · rw [zero_mul, zero_add, sup_integrand_zero]
  · rintro _ ⟨multiplier, hMultiplier, rfl⟩
    have hcost : multiplier ≤ multiplier * radius := by
      simpa using (mul_le_mul_of_nonneg_left hradius hMultiplier)
    linarith [endpoint_le_sup multiplier hMultiplier]

/-- The claimed formula uses one fixed penalty and the ball radius as its coefficient. -/
def RadiusRegularization : Prop :=
  ∃ penalty : ℝ, ∀ radius : ℝ, 0 < radius →
    transportDual radius = empiricalRisk + radius * penalty

theorem conjecture_00000008827_false (RemainingClaims : Prop) :
    ¬ (RemainingClaims ∧ RadiusRegularization) := by
  rintro ⟨_, ⟨penalty, h⟩⟩
  have h₁ := h 1 (by norm_num)
  have h₂ := h 2 (by norm_num)
  rw [dual_eq_three 1 le_rfl] at h₁
  rw [dual_eq_three 2 (by norm_num)] at h₂
  have hEmpirical : empiricalRisk = 2 := by norm_num [empiricalRisk, loss, sample]
  linarith

#print axioms conjecture_00000008827_false

end Submission00000008827
