import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic

open Filter

namespace PolynomialCone

/-- A real polynomial bounded on the nonnegative half-line is constant. -/
theorem polynomial_eval_eq_eval_zero_of_bounded_nonneg
    (p : Polynomial ℝ) (M : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → |p.eval t| ≤ M) (t : ℝ) :
    p.eval t = p.eval 0 := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun t : ℝ => |p.eval t|) := by
    refine ⟨M, eventually_map.mpr ?_⟩
    exact (eventually_ge_atTop (0 : ℝ)).mono fun t ht => hbound t ht
  have hd := (Polynomial.abs_isBoundedUnder_iff p).mp hb
  rw [Polynomial.eq_C_of_degree_le_zero hd]
  simp

/-- Substitution of a ray into a multivariate polynomial gives a univariate polynomial. -/
noncomputable def rayPolynomial {ι : Type*} (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (x i) * Polynomial.X) p

@[simp] theorem eval_rayPolynomial {ι : Type*} (p : MvPolynomial ι ℝ)
    (x : ι → ℝ) (t : ℝ) :
    (rayPolynomial p x).eval t = MvPolynomial.eval (fun i => t * x i) p := by
  unfold rayPolynomial
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add, Polynomial.eval_add, map_add] using congrArg₂ (fun a b : ℝ => a + b) hp hq
  | mul_X p i hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, map_mul, MvPolynomial.eval_X]
      rw [hp, mul_comm (x i) t]

/-- Every polynomial bounded on a set closed under nonnegative scaling is constant there. -/
theorem eval_eq_eval_zero_of_bounded_on_cone {ι : Type*}
    (S : Set (ι → ℝ))
    (hscale : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → (fun i => t * x i) ∈ S)
    (p : MvPolynomial ι ℝ) (M : ℝ)
    (hbound : ∀ x ∈ S, |MvPolynomial.eval x p| ≤ M) :
    ∀ x ∈ S, MvPolynomial.eval x p = MvPolynomial.eval (0 : ι → ℝ) p := by
  intro x hx
  have h := polynomial_eval_eq_eval_zero_of_bounded_nonneg (rayPolynomial p x) M
    (fun t ht => by simpa using hbound _ (hscale x hx t ht)) 1
  simpa using h

/-- The coordinate functions of a bounded polynomial map on a cone are constant. -/
theorem polynomial_map_eq_zero_of_bounded_on_cone {ι κ : Type*}
    (S : Set (ι → ℝ))
    (hscale : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → (fun i => t * x i) ∈ S)
    (p : κ → MvPolynomial ι ℝ) (M : κ → ℝ)
    (hbound : ∀ x ∈ S, ∀ j, |MvPolynomial.eval x (p j)| ≤ M j) :
    ∀ x ∈ S, (fun j => MvPolynomial.eval x (p j)) =
      (fun j => MvPolynomial.eval (0 : ι → ℝ) (p j)) := by
  intro x hx
  funext j
  exact eval_eq_eval_zero_of_bounded_on_cone S hscale (p j) (M j)
    (fun y hy => hbound y hy j) x hx

/-- Restriction of a complex-coefficient polynomial to real inputs has real polynomial
real and imaginary coordinate functions. -/
theorem exists_real_imag_polynomials {ι : Type*} (p : MvPolynomial ι ℂ) :
    ∃ pr pi : MvPolynomial ι ℝ, ∀ x : ι → ℝ,
      (MvPolynomial.eval (fun i => (x i : ℂ)) p).re = MvPolynomial.eval x pr ∧
      (MvPolynomial.eval (fun i => (x i : ℂ)) p).im = MvPolynomial.eval x pi := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨MvPolynomial.C c.re, MvPolynomial.C c.im, ?_⟩
      intro x
      simp
  | add p q hp hq =>
      obtain ⟨pr, pi, hp⟩ := hp
      obtain ⟨qr, qi, hq⟩ := hq
      refine ⟨pr + qr, pi + qi, ?_⟩
      intro x
      constructor
      · simpa only [map_add, Complex.add_re] using
          congrArg₂ (fun a b : ℝ => a + b) (hp x).1 (hq x).1
      · simpa only [map_add, Complex.add_im] using
          congrArg₂ (fun a b : ℝ => a + b) (hp x).2 (hq x).2
  | mul_X p i hp =>
      obtain ⟨pr, pi, hp⟩ := hp
      refine ⟨pr * MvPolynomial.X i, pi * MvPolynomial.X i, ?_⟩
      intro x
      constructor
      · simp only [map_mul, MvPolynomial.eval_X, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        rw [(hp x).1]
      · simp only [map_mul, MvPolynomial.eval_X, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
        rw [(hp x).2]

end PolynomialCone
