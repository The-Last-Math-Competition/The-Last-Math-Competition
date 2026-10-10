import Mathlib
import Conjecture1305.Statement

/-! # Conjecture 1305: the Kobayashi pseudodistance of C^2 minus Z^2

The pseudodistance `d_K` of `D = C^2 \ Z^2` (defined as the infimum over finite chains of holomorphic
unit-disc maps into `D`, with the Poincare distance of the disc) vanishes identically on `D`.
So it is not "non-degenerate in the vertical direction" (and not in the horizontal one either). -/

-- (formal statement: see Statement.lean)

namespace C1305

open Metric

lemma swap_mem {z : ℂ × ℂ} (h : z ∈ D) : z.swap ∈ D := by
  intro m n h'
  exact h n m (by simpa [Prod.ext_iff, and_comm] using h')

/-- Core: a one-parameter family of entire curves through `p` and `p+u`, one of which misses `Z^2`
(only countably many parameters are bad). -/
lemma core (p u : ℂ × ℂ) (hu : u.1 ≠ 0) (hp : p ∈ D) (hq : (p.1 + u.1, p.2 + u.2) ∈ D) :
    ∃ s : ℂ, ∀ t : ℂ, (p.1 + t * u.1, p.2 + t * u.2 + s * (t * (t - 1))) ∈ D := by
  let T : ℤ → ℂ := fun m => ((m : ℂ) - p.1) / u.1
  let B : Set ℂ := Set.range (fun mn : ℤ × ℤ =>
    ((mn.2 : ℂ) - p.2 - T mn.1 * u.2) / (T mn.1 * (T mn.1 - 1)))
  have hB : B ≠ Set.univ := fun h => not_countable_complex (h ▸ Set.countable_range _)
  obtain ⟨s, hs⟩ : ∃ s, s ∉ B := by
    by_contra h
    exact hB (Set.eq_univ_of_forall fun x => by by_contra hx; exact h ⟨x, hx⟩)
  refine ⟨s, fun t m n heq => ?_⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  by_cases ht : t * (t - 1) = 0
  · rcases mul_eq_zero.mp ht with h0 | h0
    · apply hp m n
      subst h0
      simp only [zero_mul, add_zero, mul_zero] at h1 h2
      exact Prod.ext h1 h2
    · have : t = 1 := by linear_combination h0
      subst this
      apply hq m n
      simp only [one_mul, sub_self, mul_zero, add_zero] at h1 h2
      exact Prod.ext h1 h2
  · apply hs
    refine ⟨(m, n), ?_⟩
    have htT : t = T m := by
      simp only [T]; field_simp; linear_combination h1
    simp only
    rw [← htT, div_eq_iff (by exact ht)]
    linear_combination -h2

/-- An entire curve in `D` through two distinct points of `D`. -/
lemma exists_curve {p q : ℂ × ℂ} (hp : p ∈ D) (hq : q ∈ D) (hne : p ≠ q) :
    ∃ f : ℂ → ℂ × ℂ, Differentiable ℂ f ∧ (∀ t, f t ∈ D) ∧ f 0 = p ∧ f 1 = q := by
  by_cases h1 : q.1 - p.1 ≠ 0
  · obtain ⟨s, hs⟩ := core p (q.1 - p.1, q.2 - p.2) h1 hp (by simpa using hq)
    refine ⟨fun t => (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2) + s * (t * (t - 1))),
      by fun_prop, hs, by simp, by simp⟩
  · have h2 : q.2 - p.2 ≠ 0 := by
      intro h2
      apply hne
      rw [not_not] at h1
      exact Prod.ext (by linear_combination -h1) (by linear_combination -h2)
    obtain ⟨s, hs⟩ := core p.swap (q.2 - p.2, q.1 - p.1) h2 (swap_mem hp)
      (by
        have h := swap_mem hq
        rwa [show (p.swap.1 + (q.2 - p.2), p.swap.2 + (q.1 - p.1)) = q.swap by simp [Prod.swap]])
    refine ⟨fun t => (p.1 + t * (q.1 - p.1) + s * (t * (t - 1)), p.2 + t * (q.2 - p.2)),
      by fun_prop, fun t => ?_, by simp, by simp⟩
    have := swap_mem (hs t)
    simpa using this

lemma poincare_zero (b : ℂ) : poincare 0 b = Real.artanh ‖b‖ := by
  simp [poincare]

/-- One-link bound from the definition. -/
lemma dK_le {p q : ℂ × ℂ} {f : ℂ → ℂ × ℂ} (hf : Differentiable ℂ f) (hD : ∀ t, f t ∈ D)
    (h0 : f 0 = p) (h1 : f 1 = q) {R : ℝ} (hR : 1 < R) :
    dK p q ≤ ENNReal.ofReal (Real.artanh (1 / R)) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast (by linarith : R ≠ 0)
  have hb : ((1 / R : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_zero_right, Complex.norm_real, norm_div, norm_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < R)]
    rw [div_lt_one (by linarith)]; exact hR
  have hch : Chain p q (0 + ENNReal.ofReal (poincare 0 ((1 / R : ℝ) : ℂ))) :=
    Chain.step (fun z => f ((R : ℂ) * z)) 0 ((1 / R : ℝ) : ℂ) (Chain.refl p)
      ⟨(hf.comp (differentiable_const _ |>.mul differentiable_id)).differentiableOn,
        fun z _ => hD _⟩ (mem_ball_self one_pos) hb (by simpa using h0)
      (by simp [hR0, h1])
  have : dK p q ≤ _ := sInf_le hch
  rw [poincare_zero] at this
  simpa [abs_of_pos (by linarith : (0 : ℝ) < R), Complex.norm_real,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / R)] using this

/-- `d_K` vanishes between any two points of `D`. -/
theorem dK_eq_zero {p q : ℂ × ℂ} (hp : p ∈ D) (hq : q ∈ D) : dK p q = 0 := by
  by_cases hne : p = q
  · subst hne
    exact le_antisymm (sInf_le (Chain.refl p)) zero_le
  obtain ⟨f, hf, hD, h0, h1⟩ := exists_curve hp hq hne
  apply le_antisymm _ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have ht0 : 0 < Real.tanh ε := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hε') (Real.cosh_pos ε)
  have ht1 : Real.tanh ε < 1 := Real.tanh_lt_one ε
  set R : ℝ := 1 + 1 / Real.tanh ε with hRdef
  have hR : 1 < R := by have : 0 < 1 / Real.tanh ε := by positivity
                        linarith
  have hlt : 1 / R < Real.tanh ε := by
    rw [hRdef, div_lt_iff₀ (by linarith [hR])]
    have : Real.tanh ε * (1 / Real.tanh ε) = 1 := by field_simp
    nlinarith
  have hart : Real.artanh (1 / R) ≤ ε := by
    have h1R : 0 < 1 / R := by positivity
    have := Real.artanh_lt_artanh (x := 1 / R) (y := Real.tanh ε) (by linarith) ht1 hlt
    rw [Real.artanh_tanh] at this
    exact this.le
  calc dK p q ≤ ENNReal.ofReal (Real.artanh (1 / R)) := dK_le hf hD h0 h1 hR
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hart
    _ = ε := ENNReal.ofReal_coe_nnreal

lemma I0_mem : ((Complex.I, 0) : ℂ × ℂ) ∈ D := by
  intro m n h
  have := congrArg (fun z => z.1.im) h
  simp at this

lemma I1_mem : ((Complex.I, 1) : ℂ × ℂ) ∈ D := by
  intro m n h
  have := congrArg (fun z => z.1.im) h
  simp at this

lemma mem_swap_I0 : ((0, Complex.I) : ℂ × ℂ) ∈ D := by
  intro m n h
  have := congrArg (fun z => z.2.im) h
  simp at this

lemma mem_swap_I1 : ((1, Complex.I) : ℂ × ℂ) ∈ D := by
  intro m n h
  have := congrArg (fun z => z.2.im) h
  simp at this

theorem main : Claim := by
  refine ⟨?_, fun p hp q hq => dK_eq_zero hp hq⟩
  rintro (⟨-, hA⟩ | ⟨-, hB⟩)
  · have := hA _ I0_mem _ I1_mem rfl (by simp [Prod.ext_iff])
    rw [dK_eq_zero I0_mem I1_mem] at this
    exact lt_irrefl _ this
  · have := hB _ mem_swap_I0 _ mem_swap_I1 rfl (by simp [Prod.ext_iff])
    rw [dK_eq_zero mem_swap_I0 mem_swap_I1] at this
    exact lt_irrefl _ this

end C1305
