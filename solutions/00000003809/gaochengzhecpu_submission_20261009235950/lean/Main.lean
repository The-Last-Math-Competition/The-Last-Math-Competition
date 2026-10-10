import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
open Set

namespace Conjecture3809

def C : Set ℝ := Icc 0 1
def F (x : ℝ) : ℝ := 2 * x - x ^ 2
def K (x : ℝ) : ℝ := -x

/-- The usual real one-dimensional monotone-operator condition. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, 0 ≤ (f x - f y) * (x - y)

/-- The genuine primal and dual gap functions, as suprema over the feasible set. -/
def primalGap (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun y => f x * (x - y)) '' C)

def dualGap (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun y => f y * (x - y)) '' C)

theorem F_nonnegative {x : ℝ} (hx : x ∈ C) : 0 ≤ F x := by
  have h := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  dsimp [F]
  nlinarith

theorem F_order_monotone : MonotoneOn F C := by
  intro x hx y hy hxy
  have h : 0 ≤ (y - x) * (2 - x - y) :=
    mul_nonneg (sub_nonneg.mpr hxy) (by linarith [hx.2, hy.2])
  dsimp [F]
  nlinarith

theorem F_operator_monotone : OperatorMonotone F := by
  intro x hx y hy
  calc
    0 ≤ (x - y) ^ 2 * (2 - x - y) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx.2, hy.2])
    _ = (F x - F y) * (x - y) := by dsimp [F]; ring

theorem primal_gap_formula {x : ℝ} (hx : x ∈ C) :
    primalGap F x = 2 * x ^ 2 - x ^ 3 := by
  have hmax : IsGreatest ((fun y => F x * (x - y)) '' C) (F x * x) := by
    constructor
    · refine ⟨0, ?_, ?_⟩
      · norm_num [C]
      · simp
    · rintro z ⟨y, hy, rfl⟩
      exact mul_le_mul_of_nonneg_left (by linarith [hy.1]) (F_nonnegative hx)
  rw [primalGap, hmax.csSup_eq]
  dsimp [F]
  ring

theorem primal_gap_not_convex : ¬ ConvexOn ℝ C (primalGap F) := by
  intro h
  have hmid := h.2 (by norm_num [C] : (2 / 3 : ℝ) ∈ C)
    (by norm_num [C] : (1 : ℝ) ∈ C)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  norm_num [smul_eq_mul] at hmid
  rw [primal_gap_formula (by norm_num [C] : (5 / 6 : ℝ) ∈ C),
    primal_gap_formula (by norm_num [C] : (2 / 3 : ℝ) ∈ C),
    primal_gap_formula (by norm_num [C] : (1 : ℝ) ∈ C)] at hmid
  norm_num at hmid

theorem K_not_operator_monotone : ¬ OperatorMonotone K := by
  intro h
  have hh := h 0 (by norm_num [C]) 1 (by norm_num [C])
  norm_num [K] at hh

theorem dual_gap_formula {x : ℝ} (hx : x ∈ C) : dualGap K x = 1 - x := by
  have hmax : IsGreatest ((fun y => K y * (x - y)) '' C) (1 - x) := by
    constructor
    · refine ⟨1, ?_, ?_⟩
      · norm_num [C]
      · dsimp [K]
        ring
    · rintro z ⟨y, hy, rfl⟩
      have h : 0 ≤ (1 - y) * (1 + y - x) :=
        mul_nonneg (sub_nonneg.mpr hy.2) (by linarith [hx.2, hy.1])
      dsimp [K]
      nlinarith
  exact hmax.csSup_eq

theorem dual_gap_convex : ConvexOn ℝ C (dualGap K) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ C := (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  rw [dual_gap_formula hxy, dual_gap_formula hx, dual_gap_formula hy]
  simp only [smul_eq_mul]
  nlinarith

theorem primal_counterexample :
    OperatorMonotone F ∧ ¬ ConvexOn ℝ C (primalGap F) :=
  ⟨F_operator_monotone, primal_gap_not_convex⟩

theorem dual_counterexample :
    ConvexOn ℝ C (dualGap K) ∧ ¬ OperatorMonotone K :=
  ⟨dual_gap_convex, K_not_operator_monotone⟩

theorem neither_gap_gives_the_claimed_equivalence :
    (¬ ∀ f : ℝ → ℝ, OperatorMonotone f ↔ ConvexOn ℝ C (primalGap f)) ∧
    (¬ ∀ f : ℝ → ℝ, OperatorMonotone f ↔ ConvexOn ℝ C (dualGap f)) := by
  constructor
  · intro h
    exact primal_gap_not_convex ((h F).mp F_operator_monotone)
  · intro h
    exact K_not_operator_monotone ((h K).mpr dual_gap_convex)

end Conjecture3809

#print axioms Conjecture3809.primal_gap_formula
#print axioms Conjecture3809.primal_counterexample
#print axioms Conjecture3809.dual_gap_formula
#print axioms Conjecture3809.dual_counterexample
#print axioms Conjecture3809.neither_gap_gives_the_claimed_equivalence
