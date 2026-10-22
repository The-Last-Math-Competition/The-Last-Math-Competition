import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Necessary clauses of the printed step-function formula are incompatible.
No Ohsawa--Takegoshi optimum is assigned a value or assumed to exist. -/
namespace TLMC1785
open Set Function
open scoped BigOperators

def positiveWindow : Set ℝ := Ioo (1 / 2) 1
noncomputable def printedFormula (c : ℝ) : ℝ := max 1 (2 * c) * Real.pi

/-- The standard finite disjoint-interval indicator-sum definition, restricted to I. -/
def FiniteIntervalStepOn (I : Set ℝ) (C : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (J : Fin n → Set ℝ) (a : Fin n → ℝ),
    (∀ i, OrdConnected (J i)) ∧ Pairwise (Disjoint on J) ∧
    ∀ x ∈ I, C x = ∑ i, (J i).indicator (fun _ => a i) x

/-- A more permissive countable interval partition into constant pieces. -/
def CountableIntervalStepOn (I : Set ℝ) (C : ℝ → ℝ) : Prop :=
  ∃ (J : ℕ → Set ℝ) (a : ℕ → ℝ),
    (∀ i, OrdConnected (J i)) ∧ Pairwise (Disjoint on J) ∧
    I ⊆ ⋃ i, J i ∧ ∀ i x, x ∈ I → x ∈ J i → C x = a i

theorem finite_step_restrict {I K : Set ℝ} {C : ℝ → ℝ}
    (h : FiniteIntervalStepOn I C) (hsub : K ⊆ I) : FiniteIntervalStepOn K C := by
  obtain ⟨n, J, a, hJ, hdisj, hC⟩ := h
  exact ⟨n, J, a, hJ, hdisj, fun x hx => hC x (hsub hx)⟩

theorem countable_step_restrict {I K : Set ℝ} {C : ℝ → ℝ}
    (h : CountableIntervalStepOn I C) (hsub : K ⊆ I) : CountableIntervalStepOn K C := by
  obtain ⟨J, a, hJ, hdisj, hcover, hC⟩ := h
  exact ⟨J, a, hJ, hdisj, hsub.trans hcover, fun i x hx hxi => hC i x (hsub hx) hxi⟩

theorem finite_steps_finite_image {I : Set ℝ} {C : ℝ → ℝ}
    (h : FiniteIntervalStepOn I C) : (C '' I).Finite := by
  classical
  obtain ⟨n, J, a, _, _, hC⟩ := h
  let value : (Fin n → Bool) → ℝ := fun b => ∑ i, if b i then a i else 0
  apply (Set.finite_range value).subset
  rintro y ⟨x, hx, rfl⟩
  refine ⟨fun i => decide (x ∈ J i), ?_⟩
  rw [hC x hx]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ J i
  · simp [hi]
  · simp [hi]

theorem countable_steps_countable_image {I : Set ℝ} {C : ℝ → ℝ}
    (h : CountableIntervalStepOn I C) : (C '' I).Countable := by
  obtain ⟨J, a, _, _, hcover, hC⟩ := h
  apply (Set.countable_range a).mono
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  exact ⟨i, (hC i x hx hi).symm⟩

theorem formula_on_positive_window {c : ℝ} (hc : c ∈ positiveWindow) :
    printedFormula c = (2 * c) * Real.pi := by
  rw [printedFormula, max_eq_right (by have := hc.1; dsimp [positiveWindow] at *; linarith)]

theorem formula_injective_on_window : Set.InjOn printedFormula positiveWindow := by
  intro x hx y hy h
  rw [formula_on_positive_window hx, formula_on_positive_window hy] at h
  have h' : 2 * x = 2 * y := mul_right_cancel₀ Real.pi_ne_zero h
  linarith

theorem positive_window_uncountable : ¬positiveWindow.Countable := by
  rw [positiveWindow, Cardinal.Real.Ioo_countable_iff]
  norm_num

theorem formula_image_uncountable : ¬(printedFormula '' positiveWindow).Countable := by
  intro h
  let : Countable (printedFormula '' positiveWindow) := h.to_subtype
  have hinj : Function.Injective
      (fun x : positiveWindow => (⟨printedFormula x,
        mem_image_of_mem printedFormula x.property⟩ : printedFormula '' positiveWindow)) := by
    intro x y he
    apply Subtype.ext
    exact formula_injective_on_window x.property y.property (congrArg Subtype.val he)
  have : Countable positiveWindow := Function.Injective.countable hinj
  exact positive_window_uncountable (Set.to_countable positiveWindow)

theorem necessary_finite_step_clauses_impossible (C : ℝ → ℝ) :
    ¬(FiniteIntervalStepOn positiveWindow C ∧
      ∀ c ∈ positiveWindow, C c = printedFormula c) := by
  rintro ⟨hstep, hformula⟩
  have himg : C '' positiveWindow = printedFormula '' positiveWindow := by
    apply Set.image_congr
    exact hformula
  exact formula_image_uncountable (himg ▸ (finite_steps_finite_image hstep).countable)

theorem necessary_countable_step_clauses_impossible (C : ℝ → ℝ) :
    ¬(CountableIntervalStepOn positiveWindow C ∧
      ∀ c ∈ positiveWindow, C c = printedFormula c) := by
  rintro ⟨hstep, hformula⟩
  have himg : C '' positiveWindow = printedFormula '' positiveWindow := by
    apply Set.image_congr
    exact hformula
  exact formula_image_uncountable (himg ▸ countable_steps_countable_image hstep)

theorem no_finite_step_constant_function :
    ¬∃ C : ℝ → ℝ, FiniteIntervalStepOn positiveWindow C ∧
      ∀ c ∈ positiveWindow, C c = printedFormula c := by
  rintro ⟨C, h⟩
  exact necessary_finite_step_clauses_impossible C h

theorem no_countable_step_constant_function :
    ¬∃ C : ℝ → ℝ, CountableIntervalStepOn positiveWindow C ∧
      ∀ c ∈ positiveWindow, C c = printedFormula c := by
  rintro ⟨C, h⟩
  exact necessary_countable_step_clauses_impossible C h

theorem positive_window_subset_positive : positiveWindow ⊆ Ioi (0 : ℝ) := by
  intro c hc
  have h := hc.1
  change (1 : ℝ) / 2 < c at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 2) h

theorem no_positive_finite_steps_with_formula :
    ¬∃ C : ℝ → ℝ, FiniteIntervalStepOn (Ioi 0) C ∧
      ∀ c > 0, C c = printedFormula c := by
  rintro ⟨C, hstep, hformula⟩
  exact necessary_finite_step_clauses_impossible C
    ⟨finite_step_restrict hstep positive_window_subset_positive,
      fun c hc => hformula c (positive_window_subset_positive hc)⟩

theorem no_positive_countable_steps_with_formula :
    ¬∃ C : ℝ → ℝ, CountableIntervalStepOn (Ioi 0) C ∧
      ∀ c > 0, C c = printedFormula c := by
  rintro ⟨C, hstep, hformula⟩
  exact necessary_countable_step_clauses_impossible C
    ⟨countable_step_restrict hstep positive_window_subset_positive,
      fun c hc => hformula c (positive_window_subset_positive hc)⟩

end TLMC1785
