import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace TLMC145
open scoped BigOperators
open Set
noncomputable section

/-- Exactly the primes at most the real cutoff, rather than an assigned count. -/
def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊+1)).filter Nat.Prime

theorem mem_primesUpTo (x : ℝ) (hx : 0≤x) (p : ℕ) :
    p∈primesUpTo x ↔ p.Prime ∧ (p:ℝ)≤x := by
  simp only [primesUpTo,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  rw [Nat.le_floor_iff hx]
  exact and_comm

def primeCount (x : ℝ) : ℕ := (primesUpTo x).card
def mean (f : ℝ→ℝ) : ℝ := ∫ t in (0:ℝ)..1, f t
def variance (f : ℝ→ℝ) : ℝ := ∫ t in (0:ℝ)..1, (f t-mean f)^2
def centeredSum (α : ℝ) (f : ℝ→ℝ) (x : ℝ) : ℝ :=
  (∑ p∈primesUpTo x, f (Int.fract (α*(p:ℝ))))-primeCount x*mean f

def sine (t : ℝ) : ℝ := Real.sin (2*Real.pi*t)

theorem sine_smooth : ContDiff ℝ ⊤ sine := by unfold sine; fun_prop
theorem sine_periodic : Function.Periodic sine 1 := by
  intro t
  dsimp [sine]
  convert Real.sin_periodic (2*Real.pi*t) using 1
  congr 1
  ring

theorem sine_mean : mean sine=0 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f:=Real.sin) (a:=0) (b:=1) (c:=2*Real.pi)
  rw [integral_sin] at h
  simp only [mul_zero,mul_one,Real.cos_zero,Real.cos_two_pi,sub_self] at h
  have hn : 2*Real.pi≠0 := ne_of_gt (by positivity)
  exact (mul_eq_zero.mp h).resolve_left hn

theorem sine_variance : variance sine=1/2 := by
  rw [variance,sine_mean]
  simp only [sub_zero]
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f:=fun t : ℝ => Real.sin t^2) (a:=0) (b:=1) (c:=2*Real.pi)
  rw [integral_sin_sq] at h
  simp only [mul_zero,mul_one,Real.sin_zero,Real.cos_zero,Real.sin_two_pi,
    Real.cos_two_pi,sub_zero,zero_add] at h
  change 2*Real.pi*(∫ t in (0:ℝ)..1, sine t^2) = (2*Real.pi)/2 at h
  have hp := Real.pi_pos
  change (∫ t in (0:ℝ)..1, sine t^2)=1/2
  nlinarith

theorem sine_nonzero_deviation : ∃ t∈Icc (0:ℝ) 1, sine t≠mean sine := by
  refine ⟨1/4,by norm_num,?_⟩
  rw [sine_mean]
  have he : 2*Real.pi*((1:ℝ)/4)=Real.pi/2 := by ring
  norm_num [sine,he]

theorem sampled_sine_zero (p : ℕ) : sine (Int.fract ((1:ℝ)*p))=0 := by
  simp [sine]

theorem centered_sine_zero (x : ℝ) : centeredSum 1 sine x=0 := by
  simp [centeredSum,sine_mean,sine]

/-- The exact printed LIL fluctuation scale. -/
def scale (x : ℝ) : ℝ := Real.sqrt (x*Real.log (Real.log x)/Real.log x)

theorem scale_pos {x : ℝ} (hx : Real.exp 2≤x) : 0<scale x := by
  have hx0 : 0<x := lt_of_lt_of_le (Real.exp_pos 2) hx
  have hl : 2≤Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    simpa only [Real.log_exp] using h
  have hl0 : 0<Real.log x := by linarith
  have hll : 0<Real.log (Real.log x) := Real.log_pos (by linarith)
  exact Real.sqrt_pos.mpr (div_pos (mul_pos hx0 hll) hl0)

/-- Standard quantitative, arbitrarily-late positive Omega fluctuations. -/
def OmegaPlus (h g : ℝ→ℝ) : Prop :=
  ∃ c : ℝ, 0<c ∧ ∀ N : ℝ, ∃ x : ℝ, N≤x ∧ c*g x≤h x
def OmegaMinus (h g : ℝ→ℝ) : Prop := OmegaPlus (fun x => -h x) g
def OmegaBoth (h g : ℝ→ℝ) : Prop := OmegaPlus h g ∧ OmegaMinus h g

theorem zero_not_omega_plus : ¬OmegaPlus (fun _ => 0) scale := by
  rintro ⟨c,hc,h⟩
  obtain ⟨x,hx,hbound⟩ := h (Real.exp 2)
  exact (not_le_of_gt (mul_pos hc (scale_pos hx))) hbound

theorem actual_prime_fluctuations_fail :
    ¬OmegaPlus (centeredSum 1 sine) scale ∧
    ¬OmegaMinus (centeredSum 1 sine) scale ∧
    ¬OmegaBoth (centeredSum 1 sine) scale := by
  have he : centeredSum 1 sine=(fun _ => 0) := funext centered_sine_zero
  rw [he]
  simp only [OmegaMinus,neg_zero,OmegaBoth]
  exact ⟨zero_not_omega_plus,zero_not_omega_plus,fun h => zero_not_omega_plus h.1⟩

theorem literal_unrestricted_claim_false :
    ¬∀ α : ℝ, 0<α → ∀ f : ℝ→ℝ,
      ContDiff ℝ ⊤ f → Function.Periodic f 1 → 0<variance f →
      OmegaBoth (centeredSum α f) scale := by
  intro h
  exact actual_prime_fluctuations_fail.2.2
    (h 1 (by norm_num) sine sine_smooth sine_periodic (by rw [sine_variance]; norm_num))

end
end TLMC145
