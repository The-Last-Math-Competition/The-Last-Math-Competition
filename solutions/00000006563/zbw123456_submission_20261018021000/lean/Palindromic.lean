import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Palindromic
noncomputable section
set_option linter.unnecessarySeqFocus false
abbrev State := ℝ × ℝ
def A (h : ℝ) (x : State) : State := (x.1+h,x.2)
def B (h : ℝ) (x : State) : State := (x.1,x.2+h)
def method (h : ℝ) (x : State) : State := A (h/3) (B h (A (2*h/3) x))
def Reversible (S : ℝ → State → State) : Prop :=
  ∀ h x, S (-h) (S h x) = x ∧ S h (S (-h) x) = x
def coefficients : List ℝ := [1/3,1,2/3]

theorem flow_A (s t : ℝ) (x : State) : A (s+t) x = A s (A t x) := by
  ext <;> simp [A] <;> ring
theorem flow_B (s t : ℝ) (x : State) : B (s+t) x = B s (B t x) := by
  ext <;> simp [B] <;> ring
theorem flow_id (x : State) : A 0 x = x ∧ B 0 x = x := by simp [A, B]
theorem independent : A 1 (0,0) ≠ B 1 (0,0) := by norm_num [A, B]
theorem exact_translation (h : ℝ) (x : State) : method h x = (x.1+h,x.2+h) := by
  ext <;> simp [method, A, B] <;> ring
theorem reversible : Reversible method := by
  intro h x
  simp only [exact_translation]
  constructor <;> ext <;> simp
theorem not_palindromic : coefficients.reverse ≠ coefficients := by
  norm_num [coefficients, List.cons.injEq]
theorem counterexample : Reversible method ∧ coefficients.reverse ≠ coefficients :=
  ⟨reversible, not_palindromic⟩
#print axioms counterexample
end
end Palindromic
