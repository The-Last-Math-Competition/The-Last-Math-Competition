import Mathlib.Topology.Instances.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace NilCorrelation
open Filter
open scoped BigOperators Topology ComplexConjugate

/-- A basic circle nilsequence: continuous observable on R/Z along a rotation.
The circle is a compact abelian (hence one-step nilpotent) nilmanifold. -/
def circleSequence (F : C(AddCircle (1 : ℝ), ℂ)) (a : AddCircle (1 : ℝ)) (n : ℕ) : ℂ :=
  F (n • a)

def constantObservable : C(AddCircle (1 : ℝ), ℂ) := ContinuousMap.const _ 1

def witness : ℕ → ℂ := circleSequence constantObservable 0

def phase (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp ((2 * Real.pi * α * n : ℝ) * Complex.I)

def correlation (a : ℕ → ℂ) (α : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, a n * conj (phase α n)

theorem witness_one (n : ℕ) : witness n = 1 := rfl

theorem stationary (τ n : ℕ) : witness (n + τ) = witness n := rfl

theorem correlation_one (N : ℕ) (hN : N ≠ 0) : correlation witness 0 N = 1 := by
  simp [correlation, witness_one, phase, hN]

theorem no_weyl_bound : ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    ‖correlation witness 0 N‖ ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rintro ⟨C, hC⟩
  have ht : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop |>.const_mul C
  have he : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [hC, eventually_ge_atTop 1] with N hN hpos
    simpa [correlation_one N (by omega)] using hN
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto ht he
  norm_num at this

#print axioms no_weyl_bound
#print axioms stationary
end NilCorrelation
