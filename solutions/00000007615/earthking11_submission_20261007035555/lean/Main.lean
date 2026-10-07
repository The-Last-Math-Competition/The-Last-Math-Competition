import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace TLMC7615

/-- Covectors on a two-dimensional real vector space with Lorentz metric
    of signature `(1,1)`. Integer coefficients suffice for this witness. -/
structure OneForm where
  first : ℝ
  second : ℝ

/-- The inverse-metric pairing on covectors for `diag(-1, 1)`. -/
def lorentzPairing (α β : OneForm) : ℝ :=
  -(α.first * β.first) + α.second * β.second

/-- The coefficient of `α ∧ β` relative to the oriented volume form
    `e₁ ∧ e₂`. -/
def wedgeCoefficient (α β : OneForm) : ℝ :=
  α.first * β.second - α.second * β.first

def e₁ : OneForm := ⟨1, 0⟩
def e₂ : OneForm := ⟨0, 1⟩

theorem lorentz_signature_and_orientation :
    lorentzPairing e₁ e₁ = -1 ∧
    lorentzPairing e₂ e₂ = 1 ∧
    wedgeCoefficient e₁ e₂ = 1 := by
  norm_num [lorentzPairing, wedgeCoefficient, e₁, e₂]

/-- In dimension two, the Hodge star is characterized by
    `α ∧ ⋆β = <α,β> vol`. This is the map solving that defining equation
    for the Lorentz pairing and the chosen orientation. -/
def hodgeStar (β : OneForm) : OneForm := ⟨-β.second, -β.first⟩

def HasHodgeDefiningProperty (star : OneForm → OneForm) : Prop :=
  ∀ α β, wedgeCoefficient α (star β) = lorentzPairing α β

theorem hodgeStar_satisfies_definition : HasHodgeDefiningProperty hodgeStar := by
  intro α β
  cases α
  cases β
  simp [wedgeCoefficient, lorentzPairing, hodgeStar]

/-- The defining equation determines the star map uniquely because wedge
    pairing with the two oriented basis covectors reads off both coordinates. -/
theorem hodgeStar_unique (star : OneForm → OneForm)
    (hstar : HasHodgeDefiningProperty star) : star = hodgeStar := by
  funext β
  cases β with
  | mk b₁ b₂ =>
      cases hvalue : star ⟨b₁, b₂⟩ with
      | mk s₁ s₂ =>
          have h₁ := hstar e₁ ⟨b₁, b₂⟩
          have h₂ := hstar e₂ ⟨b₁, b₂⟩
          simp [wedgeCoefficient, lorentzPairing, e₁, e₂, hvalue] at h₁ h₂
          have hs₁ : s₁ = -b₂ := by
            linarith
          have hs₂ : s₂ = -b₁ := by linarith
          simp [hodgeStar, hs₁, hs₂]

theorem hodgeStar_square (α : OneForm) : hodgeStar (hodgeStar α) = α := by
  cases α
  simp [hodgeStar]

def scale (c : ℝ) (α : OneForm) : OneForm :=
  ⟨c * α.first, c * α.second⟩

/-- The dimension-only exponent asserted by the conjecture for one-forms
    in dimension two is `1 * (2 - 1) = 1`. -/
def dimensionOnlyPrediction (α : OneForm) : OneForm :=
  scale ((-1 : ℝ) ^ (1 * (2 - 1))) α

/-- The conjectured dimension-only sign law fails for the actual Lorentzian
    Hodge star on the first basis one-form. -/
theorem conjecture_counterexample :
    hodgeStar (hodgeStar e₁) ≠ dimensionOnlyPrediction e₁ := by
  intro h
  have hfirst := congrArg OneForm.first h
  norm_num [dimensionOnlyPrediction, scale, hodgeStar, e₁] at hfirst

end TLMC7615
