import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

open Set Real

namespace GammaCharacterization

theorem shifted_logGamma_convex :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => log (Gamma (x+1))) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hx1 : (0 : ℝ) < x+1 := by linarith
  have hy1 : (0 : ℝ) < y+1 := by linarith
  have h := Real.convexOn_log_Gamma.2 hx1 hy1 ha hb hab
  simp only [Function.comp_apply, smul_eq_mul] at h ⊢
  convert h using 1 <;> congr 2 <;> nlinarith

theorem logGamma_recurrence {x : ℝ} (hx : 0 < x) :
    log (Gamma (x+1)) = log x + log (Gamma x) := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- Strictness follows from convexity plus the functional equation, without
    assuming an unproved equality case of Holder's inequality. -/
theorem logGamma_strictConvex :
    StrictConvexOn ℝ (Ioi 0) (fun x : ℝ => log (Gamma x)) := by
  have h := shifted_logGamma_convex.add_strictConvexOn strictConcaveOn_log_Ioi.neg
  apply h.congr
  intro x hx
  change log (Gamma (x+1)) + -log x = log (Gamma x)
  rw [logGamma_recurrence hx]
  ring

def Characterizes (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → 0 < f x) ∧ f 1=1 ∧
  (∀ x, 0 < x → f (x+1)=x*f x) ∧
  StrictConvexOn ℝ (Ioi 0) (fun x => log (f x))

theorem Gamma_characterizes : Characterizes Gamma := by
  refine ⟨fun x hx => Real.Gamma_pos_of_pos hx, Real.Gamma_one,
    fun x hx => Real.Gamma_add_one hx.ne', logGamma_strictConvex⟩

theorem normalized_uniqueness {f : ℝ → ℝ} (hf : Characterizes f) :
    EqOn f Gamma (Ioi 0) := by
  exact Real.eq_Gamma_of_log_convex hf.2.2.2.convexOn
    (fun {_} hx => hf.2.2.1 _ hx) (fun {_} hx => hf.1 _ hx) hf.2.1

/-- Every positive log-convex recurrence solution is exactly f(1) times Gamma. -/
theorem unnormalized_classification {f : ℝ → ℝ}
    (hp : ∀ x, 0 < x → 0 < f x)
    (hr : ∀ x, 0 < x → f (x+1)=x*f x)
    (hc : ConvexOn ℝ (Ioi 0) (fun x => log (f x))) :
    ∀ x, 0 < x → f x=f 1*Gamma x := by
  have h1 : 0 < f 1 := hp 1 (by norm_num)
  let g : ℝ → ℝ := fun x => f x / f 1
  have hgconv : ConvexOn ℝ (Ioi 0) (log ∘ g) := by
    apply (hc.add_const (-log (f 1))).congr
    intro x hx
    change log (f x) + -log (f 1) = log (f x / f 1)
    rw [Real.log_div (hp x hx).ne' h1.ne']
    ring
  have hgeq : EqOn g Gamma (Ioi 0) :=
    Real.eq_Gamma_of_log_convex hgconv
      (fun {y} hy => by dsimp [g]; rw [hr y hy]; ring)
      (fun {y} hy => div_pos (hp y hy) h1)
      (by dsimp [g]; exact div_self h1.ne')
  intro x hx
  have h := (div_eq_iff h1.ne').mp (hgeq hx)
  simpa only [mul_comm] using h

theorem uniqueness_constant_one {c : ℝ}
    (h : (fun x : ℝ => c*Gamma x) 1=1) : c=1 := by
  simpa using h

theorem bohr_mollerup_characterization {f : ℝ → ℝ} :
    Characterizes f ↔ EqOn f Gamma (Ioi 0) := by
  constructor
  · exact normalized_uniqueness
  · intro h
    refine ⟨fun x hx => ?_, ?_, fun x hx => ?_, ?_⟩
    · rw [h hx]; exact Real.Gamma_pos_of_pos hx
    · rw [h (by norm_num : (1:ℝ) ∈ Ioi 0), Real.Gamma_one]
    · rw [h (show x+1 ∈ Ioi (0:ℝ) by exact add_pos hx zero_lt_one), h hx]
      exact Real.Gamma_add_one hx.ne'
    · apply logGamma_strictConvex.congr
      intro x hx
      change log (Gamma x) = log (f x)
      rw [h hx]

#print axioms logGamma_strictConvex
#print axioms Gamma_characterizes
#print axioms normalized_uniqueness
#print axioms unnormalized_classification
#print axioms uniqueness_constant_one
#print axioms bohr_mollerup_characterization

end GammaCharacterization
